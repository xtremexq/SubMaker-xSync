let ffmpegModule = null;
let currentRequestId = null;
let lastRunLogs = [];
const MAX_CAPTURED_LOGS = 400;
const EXTRACTED_PREFIX = 'extracted_sub';
const FFMPEG_GLOBAL_ARGS = ['-hide_banner', '-nostats', '-loglevel', 'warning'];

try {
  self.postMessage({ type: 'BOOT' });
} catch (_) { /* ignore */ }

function normalizeWorkerLogText(text) {
  return String(text || '')
    .replace(/@\s*0x[0-9a-f]+/ig, '@ 0xaddr')
    .replace(/\s+/g, ' ')
    .trim();
}

function isLowSignalWorkerLog(text) {
  const lower = normalizeWorkerLogText(text).toLowerCase();
  if (!lower) return true;
  return lower === 'metadata:'
    || lower === 'aborted()'
    || /^duration\s*:/.test(lower)
    || /^title\s*:/.test(lower)
    || /^encoder\s*:/.test(lower)
    || /^filename\s*:/.test(lower)
    || /^mimetype\s*:/.test(lower)
    || /^chapters:?$/.test(lower)
    || /^chapter #\d+:\d+:/.test(lower)
    || /^bps\s*:/.test(lower)
    || /^number_of_frames\s*:/.test(lower)
    || /^number_of_bytes\s*:/.test(lower)
    || /^_statistics_/.test(lower)
    || /could not find codec parameters for stream \d+ \(attachment: none\): unknown codec/.test(lower)
    || /consider increasing the value for the 'analyzeduration'/.test(lower)
    || /invalid value of waveformatextensible_channel_mask/.test(lower)
    || /unknown-sized element at /.test(lower)
    || /file ended prematurely/.test(lower)
    || /^stream map '0:s:\d+' matches no streams\.$/.test(lower)
    || /^to ignore this, add a trailing '\?' to the map\.$/.test(lower)
    || /^output file is empty, nothing was encoded /.test(lower)
    || /guessed channel layout for input stream #\d+:\d+ : /.test(lower)
    || /error initializing output stream \d+:\d+ -- subtitle encoding currently only possible from text to text or bitmap to bitmap/.test(lower)
    || /\[ass @ .*?\] readorder gap found between \d+ and \d+/.test(lower)
    || /readorder gap found between \d+ and \d+/.test(lower);
}

function splitWorkerLogLines(text) {
  return String(text || '')
    .split(/\r?\n+/)
    .map((entry) => normalizeWorkerLogText(entry))
    .filter(Boolean);
}

function classifyWorkerFfmpegError(text, fallback = 'FFmpeg failed') {
  const lines = splitWorkerLogLines(text);
  const joined = lines.join(' ');
  const lower = joined.toLowerCase();
  if (!lower) {
    return { category: 'generic', summary: fallback };
  }
  if (lower.includes('subtitle encoding currently only possible from text to text or bitmap to bitmap')) {
    return {
      category: 'subtitle-kind-mismatch',
      summary: 'FFmpeg reported that this subtitle stream cannot be converted directly to text output.'
    };
  }
  if (/matches no streams|does not contain any stream|output file does not contain any stream|stream map/.test(lower)) {
    return {
      category: 'missing-stream',
      summary: 'FFmpeg reported that the requested subtitle stream was not present in this input.'
    };
  }
  const useful = lines.filter((line) => !isLowSignalWorkerLog(line));
  const summary = useful[useful.length - 1] || lines[lines.length - 1] || fallback;
  const compact = summary.length > 240 ? `${summary.slice(0, 237)}...` : summary;
  return { category: 'generic', summary: compact };
}

function sendLog(message, level = 'info') {
  const text = String(message || '');
  if (level !== 'error' && isLowSignalWorkerLog(text)) {
    return;
  }
  try {
    self.postMessage({
      type: 'LOG',
      level,
      message: text,
      messageId: currentRequestId
    });
  } catch (_) { /* ignore */ }
}

function buildRunError(ret, fallbackLabel) {
  const stderrLines = lastRunLogs
    .filter((entry) => String(entry?.type || '').toLowerCase().includes('stderr') && entry?.message)
    .map((entry) => String(entry.message || '').trim())
    .filter(Boolean);
  const classified = classifyWorkerFfmpegError(
    stderrLines.slice(-12).join('\n'),
    `${fallbackLabel} exited with code ${ret}`
  );
  const message = classified.summary || `${fallbackLabel} exited with code ${ret}`;
  const err = new Error(message);
  err.code = ret;
  err.ffmpegCategory = classified.category;
  err.ffmpegLogs = lastRunLogs.slice();
  return err;
}

function loadBinarySync(url, label = 'binary') {
  if (!url) {
    throw new Error(`Missing URL for ${label}`);
  }
  let xhr;
  try {
    xhr = new XMLHttpRequest();
    xhr.open('GET', url, false);
    xhr.responseType = 'arraybuffer';
    xhr.send(null);
  } catch (err) {
    throw new Error(`Failed to request ${label} (${url}): ${err?.message || err}`);
  }

  const ok = xhr.status === 200 || xhr.status === 0;
  if (!ok || !xhr.response) {
    throw new Error(`Failed to load ${label} (${url}); status=${xhr.status || 'n/a'}`);
  }
  return new Uint8Array(xhr.response);
}

async function ensureFfmpegCore(payload) {
  if (ffmpegModule) {
    return ffmpegModule;
  }
  if (typeof self.createFFmpegCore !== 'function') {
    try {
      importScripts(payload.coreUrl);
    } catch (err) {
      throw new Error(`Failed to load FFmpeg core script in dedicated demux worker (${payload?.coreUrl || 'unknown url'}): ${err?.message || err}`);
    }
  }
  if (typeof self.createFFmpegCore !== 'function') {
    throw new Error('createFFmpegCore not found after loading ffmpeg-core.js');
  }

  let module;
  try {
    const wasmBinary = payload?.wasmBinary
      ? (payload.wasmBinary instanceof Uint8Array ? payload.wasmBinary : new Uint8Array(payload.wasmBinary))
      : loadBinarySync(payload?.wasmUrl, 'FFmpeg wasm');
    module = await self.createFFmpegCore({
      wasmBinary,
      locateFile: (path) => {
        if (path.endsWith('.wasm')) return payload.wasmUrl;
        if (path.endsWith('.worker.js')) return payload.coreWorkerUrl;
        return path;
      },
      print: (msg) => sendLog(msg, 'info'),
      printErr: (msg) => sendLog(msg, 'warn')
    });
  } catch (err) {
    throw new Error(`Failed to initialize FFmpeg core in dedicated demux worker: ${err?.message || err}`);
  }

  if (typeof module.setLogger === 'function') {
    module.setLogger((entry) => {
      if (entry?.message) {
        lastRunLogs.push(entry);
        if (lastRunLogs.length > MAX_CAPTURED_LOGS) {
          lastRunLogs.shift();
        }
      }
      const lowerType = String(entry?.type || '').toLowerCase();
      const level = (lowerType === 'fferr' || lowerType === 'stderr') ? 'warn' : 'info';
      sendLog(entry?.message || '', level);
    });
  }

  ffmpegModule = module;
  sendLog('Bare FFmpeg core ready in dedicated demux worker.', 'info');
  return ffmpegModule;
}

function ffmpegFs(module, cmd, ...args) {
  const target = module.FS || module;
  const fn = target?.[cmd];
  if (typeof fn === 'function') {
    return fn.apply(target, args);
  }
  if (typeof target.FS === 'function') {
    return target.FS(cmd, ...args);
  }
  throw new Error(`FFmpeg FS command unavailable: ${cmd}`);
}

function ffmpegMount(module, fsType, options, mountPoint) {
  const target = module.FS || module;
  const mountImpl = typeof fsType === 'string'
    ? (module[fsType] || target?.[fsType] || target?.filesystems?.[fsType])
    : fsType;
  if (!mountImpl || typeof target?.mount !== 'function') {
    throw new Error(`FFmpeg mount unavailable for fs type: ${fsType}`);
  }
  return target.mount(mountImpl, options, mountPoint);
}

function ffmpegUnmount(module, mountPoint) {
  const target = module.FS || module;
  if (typeof target?.unmount !== 'function') {
    throw new Error('FFmpeg unmount unavailable');
  }
  return target.unmount(mountPoint);
}

async function ffmpegRun(module, ...args) {
  const rawArgv = Array.isArray(args[0]) ? args[0] : args;
  const argv = rawArgv.slice();
  const insertAt = argv[0] === '-y' ? 1 : 0;
  argv.splice(insertAt, 0, ...FFMPEG_GLOBAL_ARGS);
  lastRunLogs = [];
  if (typeof module.reset === 'function') {
    module.reset();
  }
  if (typeof module.exec === 'function') {
    const ret = module.exec(...argv);
    if (typeof ret === 'number' && ret !== 0) {
      throw buildRunError(ret, 'FFmpeg');
    }
    return;
  }
  if (typeof module.callMain === 'function') {
    const ret = module.callMain(argv);
    if (typeof ret === 'number' && ret !== 0) {
      throw buildRunError(ret, 'FFmpeg');
    }
    return;
  }
  throw new Error('FFmpeg core has no exec or callMain entry point');
}

function cleanupFsFile(module, file) {
  if (!file) return;
  try {
    ffmpegFs(module, 'unlink', file);
  } catch (_) { /* ignore */ }
}

function readFsFileIfPresent(module, file) {
  if (!file) return null;
  try {
    return ffmpegFs(module, 'readFile', file);
  } catch (_) {
    return null;
  }
}

function shouldKeepPartialFfmpegOutput(message) {
  const lower = String(message || '').toLowerCase();
  return lower.includes('file ended prematurely')
    || lower.includes('invalid data found when processing input')
    || lower.includes('error during demuxing')
    || lower.includes('error reading trailer')
    || lower.includes('output file is empty')
    || lower.includes('aborted()');
}

function recoverPartialFfmpegOutput(module, file, err, label) {
  const data = readFsFileIfPresent(module, file);
  if (!data?.byteLength || !shouldKeepPartialFfmpegOutput(err?.message || err)) {
    cleanupFsFile(module, file);
    return false;
  }
  const sizeKb = Math.max(1, Math.round(data.byteLength / 1024));
  sendLog(`${label} kept ${sizeKb} KB of partial output after FFmpeg reported a truncated input.`, 'warn');
  return true;
}

const formatExtractedName = (index, ext = 'srt', variant = '') => {
  const num = String(index).padStart(2, '0');
  const prefix = variant ? `${EXTRACTED_PREFIX}_${variant}_` : `${EXTRACTED_PREFIX}_`;
  return `${prefix}${num}.${ext}`;
};

function getSubtitleExtractionTargets(opts = {}) {
  const explicitPlans = Array.isArray(opts.streamPlans)
    ? opts.streamPlans.filter((entry) => entry && Number.isInteger(entry.streamIndex) && entry.streamIndex >= 0)
    : [];
  if (explicitPlans.length) {
    return explicitPlans.map((entry) => ({
      streamIndex: entry.streamIndex,
      outputIndex: Number.isInteger(entry.outputIndex) ? entry.outputIndex : (entry.streamIndex + 1),
      kind: entry.kind || 'unknown',
      codecId: entry.codecId || '',
      language: entry.language || '',
      name: entry.name || '',
      codec: entry.codec || '',
      mime: entry.mime || '',
      ext: entry.ext || ''
    }));
  }
  const maxTracks = Math.max(1, opts.maxTracks || 32);
  return Array.from({ length: maxTracks }, (_, idx) => ({
    streamIndex: idx,
    outputIndex: idx + 1,
    kind: 'unknown',
    codecId: '',
    language: '',
    name: '',
    codec: '',
    mime: '',
    ext: ''
  }));
}

function isNoSubtitleStreamErrorMessage(message) {
  const lower = String(message || '').toLowerCase();
  return lower.includes('matches no streams')
    || lower.includes('stream map')
    || lower.includes('output file #0 does not contain any stream')
    || lower.includes('subtitle codec 94213 is not supported')
    || lower.includes('subtitle encoding currently only possible from text to text or bitmap to bitmap');
}

function normalizeSubtitleFormatHint(...values) {
  for (const value of values) {
    const lower = String(value || '').trim().toLowerCase();
    if (!lower) continue;
    if (lower.includes('webvtt') || /\bvtt\b/.test(lower)) return 'vtt';
    if (lower.includes('s_text/ssa') || lower.includes('substation alpha') || /\bssa\b/.test(lower)) return 'ssa';
    if (lower.includes('s_text/ass') || lower.includes('advanced substation alpha') || /\bass\b/.test(lower)) return 'ass';
    if (lower.includes('subrip') || lower.includes('utf8') || lower.includes('mov_text') || lower.includes('tx3g') || /\bsrt\b/.test(lower)) return 'srt';
  }
  return 'srt';
}

function resolveTextSubtitleOutputPlan(target = {}) {
  const format = normalizeSubtitleFormatHint(
    target?.format,
    target?.ext,
    target?.codecId,
    target?.codec,
    target?.mime,
    target?.label,
    target?.name
  );
  switch (format) {
    case 'ass':
      return { format: 'ass', ffmpegCodec: 'ass', codec: 'ass', ext: 'ass', mime: 'text/x-ssa; charset=utf-8' };
    case 'ssa':
      return { format: 'ssa', ffmpegCodec: 'ssa', codec: 'ssa', ext: 'ssa', mime: 'text/x-ssa; charset=utf-8' };
    case 'vtt':
      return { format: 'vtt', ffmpegCodec: 'webvtt', codec: 'vtt', ext: 'vtt', mime: 'text/vtt; charset=utf-8' };
    default:
      return { format: 'srt', ffmpegCodec: 'srt', codec: 'srt', ext: 'srt', mime: 'application/x-subrip; charset=utf-8' };
  }
}

function parseExtractedOutputIndex(file) {
  const match = String(file || '').match(/^extracted_sub(?:_fix)?_(\d+)\.[a-z0-9]+$/i);
  if (!match) return null;
  const value = parseInt(match[1], 10);
  return Number.isInteger(value) && value > 0 ? value : null;
}

function findExtractionTargetByOutputIndex(targets, outputIndex) {
  if (!Array.isArray(targets) || !Number.isInteger(outputIndex) || outputIndex <= 0) {
    return null;
  }
  return targets.find((entry) => Number.isInteger(entry?.outputIndex) && entry.outputIndex === outputIndex) || null;
}

function parseArrowSubtitleTimeToSeconds(raw) {
  const match = String(raw || '').trim().match(/^(\d+):(\d{2}):(\d{2})[,.](\d{1,3})$/);
  if (!match) return null;
  const hours = parseInt(match[1], 10);
  const minutes = parseInt(match[2], 10);
  const seconds = parseInt(match[3], 10);
  const millis = parseInt(match[4].padEnd(3, '0').slice(0, 3), 10);
  return hours * 3600 + minutes * 60 + seconds + millis / 1000;
}

function parseAssSubtitleTimeToSeconds(raw) {
  const match = String(raw || '').trim().match(/^(\d+):(\d{2}):(\d{2})\.(\d{1,2})$/);
  if (!match) return null;
  const hours = parseInt(match[1], 10);
  const minutes = parseInt(match[2], 10);
  const seconds = parseInt(match[3], 10);
  const centiseconds = parseInt(match[4].padEnd(2, '0').slice(0, 2), 10);
  return hours * 3600 + minutes * 60 + seconds + centiseconds / 100;
}

function collectCueWindowsFromTrack(track) {
  const content = typeof track?.content === 'string' ? track.content : '';
  if (!content) return [];

  const format = normalizeSubtitleFormatHint(track?.codec, track?.mime, track?.label);
  const parseArrow = () => {
    const windows = [];
    const timeRegex = /(\d+:\d{2}:\d{2}[,.]\d{1,3})\s+-->\s+(\d+:\d{2}:\d{2}[,.]\d{1,3})/g;
    let match;
    while ((match = timeRegex.exec(content)) !== null) {
      const startSec = parseArrowSubtitleTimeToSeconds(match[1]);
      const endSec = parseArrowSubtitleTimeToSeconds(match[2]);
      if (startSec === null || endSec === null) continue;
      windows.push({ startSec, endSec });
    }
    return windows;
  };
  const parseAss = () => {
    const windows = [];
    const dialogueRegex = /^Dialogue:\s*[^,]*,\s*([^,]+),\s*([^,]+),/gmi;
    let match;
    while ((match = dialogueRegex.exec(content)) !== null) {
      const startSec = parseAssSubtitleTimeToSeconds(match[1]);
      const endSec = parseAssSubtitleTimeToSeconds(match[2]);
      if (startSec === null || endSec === null) continue;
      windows.push({ startSec, endSec });
    }
    return windows;
  };

  if (format === 'ass' || format === 'ssa') {
    return parseAss();
  }
  const arrowWindows = parseArrow();
  return arrowWindows.length ? arrowWindows : parseAss();
}

function shouldTreatNonMonotonicCueOrderAsBroken(track) {
  const format = normalizeSubtitleFormatHint(track?.codec, track?.mime, track?.label);
  return format !== 'ass' && format !== 'ssa';
}

function analyzeCueTimelines(tracks) {
  let flatCueStarts = false;
  let nonMonotonicCues = false;

  for (const track of tracks || []) {
    const starts = collectCueWindowsFromTrack(track).map((entry) => entry.startSec);
    if (!starts.length) continue;
    if (shouldTreatNonMonotonicCueOrderAsBroken(track)) {
      for (let i = 1; i < starts.length; i++) {
        if (starts[i] + 1e-3 < starts[i - 1]) {
          nonMonotonicCues = true;
          break;
        }
      }
    }
    if (starts.length >= 6) {
      const uniqueStarts = new Set(starts.map((value) => value.toFixed(3)));
      if ((uniqueStarts.size / starts.length) <= 0.2) {
        flatCueStarts = true;
      }
    }
    if (flatCueStarts && nonMonotonicCues) {
      break;
    }
  }

  return { flatCueStarts, nonMonotonicCues };
}

function mergeReplacementTracks(existingTracks, replacementTracks) {
  const base = Array.isArray(existingTracks) ? existingTracks.filter(Boolean) : [];
  const replacements = Array.isArray(replacementTracks) ? replacementTracks.filter(Boolean) : [];
  if (!replacements.length) {
    return base.slice();
  }

  const baseIds = new Set(base.map((track) => String(track?.id ?? '')));
  const replacementById = new Map(
    replacements
      .map((track) => [String(track?.id ?? ''), track])
      .filter(([id]) => !!id)
  );

  const merged = base.map((track) => {
    const id = String(track?.id ?? '');
    return replacementById.get(id) || track;
  });

  for (const track of replacements) {
    const id = String(track?.id ?? '');
    if (!id || baseIds.has(id)) {
      continue;
    }
    merged.push(track);
    baseIds.add(id);
  }

  return merged;
}

function buildExtractedTextTrack(module, file, target = null, decoder = new TextDecoder()) {
  const data = ffmpegFs(module, 'readFile', file);
  const outputIndex = parseExtractedOutputIndex(file);
  const extMatch = String(file || '').match(/\.([a-z0-9]+)$/i);
  const outputPlan = resolveTextSubtitleOutputPlan({
    ...(target || {}),
    ext: extMatch ? extMatch[1].toLowerCase() : ''
  });
  return {
    id: Number.isInteger(outputIndex) ? String(outputIndex) : file.replace(/\..*$/, ''),
    label: target?.name || file,
    language: target?.language || 'und',
    codec: outputPlan.codec,
    mime: outputPlan.mime,
    binary: false,
    byteLength: data.byteLength,
    content: decoder.decode(data)
  };
}

async function extractSubtitleCopyTracks(module, inputName, opts = {}) {
  const copiedTracks = [];
  const targets = getSubtitleExtractionTargets(opts);
  for (const target of targets) {
    const streamIndex = target.streamIndex;
    const outputIndex = target.outputIndex;
    const outName = formatExtractedName(outputIndex, 'mkv');
    cleanupFsFile(module, outName);
    try {
      await ffmpegRun(
        module,
        '-y',
        '-analyzeduration', '60M',
        '-probesize', '60M',
        '-i', inputName,
        '-map', `0:s:${streamIndex}`,
        '-c:s', 'copy',
        outName
      );
      const data = ffmpegFs(module, 'readFile', outName);
      if (data?.byteLength > 0) {
        copiedTracks.push(outName);
        continue;
      }
      cleanupFsFile(module, outName);
      break;
    } catch (err) {
      if (isNoSubtitleStreamErrorMessage(err?.message || err)) {
        cleanupFsFile(module, outName);
        break;
      }
      if (recoverPartialFfmpegOutput(module, outName, err, `Subtitle copy for stream ${streamIndex + 1}`)) {
        copiedTracks.push(outName);
        continue;
      }
      sendLog(`Subtitle copy failed for stream ${streamIndex + 1}: ${err?.message || err}`, 'warn');
    }
  }
  return copiedTracks;
}

function readExistingExtractedTextOutputs(module, outputs) {
  const extracted = [];
  for (const output of outputs || []) {
    if (!output?.outName) {
      continue;
    }
    const data = readFsFileIfPresent(module, output.outName);
    if (data?.byteLength > 0) {
      extracted.push(output.outName);
    } else {
      cleanupFsFile(module, output.outName);
    }
  }
  return extracted;
}

async function extractSubtitleTextTracksSequential(module, inputName, opts = {}) {
  const variant = opts.variant || '';
  const extracted = [];
  const targets = getSubtitleExtractionTargets(opts);
  const outputArgs = Array.isArray(opts.outputArgs) ? opts.outputArgs : [];
  const inputArgs = Array.isArray(opts.inputArgs) ? opts.inputArgs : [];
  let skippedKindMismatches = 0;
  for (const target of targets) {
    const streamIndex = target.streamIndex;
    const outputIndex = target.outputIndex;
    const outputPlan = resolveTextSubtitleOutputPlan(target);
    const outName = formatExtractedName(outputIndex, outputPlan.ext, variant);
    cleanupFsFile(module, outName);
    try {
      await ffmpegRun(
        module,
        '-y',
        ...inputArgs,
        '-i', inputName,
        '-map', `0:s:${streamIndex}`,
        '-c:s', outputPlan.ffmpegCodec,
        ...outputArgs,
        outName
      );
      const data = ffmpegFs(module, 'readFile', outName);
      if (data?.byteLength > 0) {
        extracted.push(outName);
      } else {
        cleanupFsFile(module, outName);
      }
    } catch (err) {
      if (isNoSubtitleStreamErrorMessage(err?.message || err)) {
        cleanupFsFile(module, outName);
        break;
      }
      if (recoverPartialFfmpegOutput(module, outName, err, `Text subtitle conversion for stream ${streamIndex + 1}`)) {
        extracted.push(outName);
        continue;
      }
      const classified = classifyWorkerFfmpegError(err?.message || err, 'FFmpeg failed to convert the subtitle stream to text output.');
      if (classified.category === 'subtitle-kind-mismatch') {
        skippedKindMismatches += 1;
        continue;
      }
      sendLog(`Text subtitle conversion failed for stream ${streamIndex + 1}: ${classified.summary}`, 'warn');
    }
  }
  if (skippedKindMismatches > 0) {
    sendLog(
      `Skipped direct text extraction for ${skippedKindMismatches} stream(s) that FFmpeg reported as non-text/bitmap mismatches.`,
      'info'
    );
  }
  return extracted;
}

async function extractSubtitleTextTracks(module, inputName, opts = {}) {
  const variant = opts.variant || '';
  const targets = getSubtitleExtractionTargets(opts);
  const outputArgs = Array.isArray(opts.outputArgs) ? opts.outputArgs : [];
  const inputArgs = Array.isArray(opts.inputArgs) ? opts.inputArgs : [];

  if (!targets.length) {
    return [];
  }

  const outputs = targets.map((target) => ({
    target,
    outputPlan: resolveTextSubtitleOutputPlan(target),
    outName: formatExtractedName(target.outputIndex, resolveTextSubtitleOutputPlan(target).ext, variant)
  }));

  for (const output of outputs) {
    cleanupFsFile(module, output.outName);
  }

  try {
    const argv = ['-y', ...inputArgs, '-i', inputName];
    for (const output of outputs) {
      argv.push(
        '-map', `0:s:${output.target.streamIndex}?`,
        '-c:s', output.outputPlan.ffmpegCodec,
        ...outputArgs,
        output.outName
      );
    }
    await ffmpegRun(module, argv);
  } catch (err) {
    const classified = classifyWorkerFfmpegError(err?.message || err, 'FFmpeg batch text extraction failed.');
    const retryReason = classified.category === 'subtitle-kind-mismatch'
      ? 'FFmpeg hit one or more streams that cannot be converted directly to text output.'
      : classified.summary;
    sendLog(`Batch text extraction failed; retrying streams individually (${retryReason})`, 'warn');
    return await extractSubtitleTextTracksSequential(module, inputName, opts);
  }

  const extracted = readExistingExtractedTextOutputs(module, outputs);
  if (extracted.length === outputs.length) {
    return extracted.sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
  }

  const extractedIds = new Set(
    extracted
      .map((file) => parseExtractedOutputIndex(file))
      .filter((value) => Number.isInteger(value) && value >= 0)
  );
  const missingTargets = targets.filter((target) => !extractedIds.has(target.outputIndex));
  if (missingTargets.length) {
    sendLog(
      `Batch text extraction produced ${extracted.length}/${outputs.length} output(s); retrying ${missingTargets.length} missing stream(s) individually...`,
      'warn'
    );
    const recovered = await extractSubtitleTextTracksSequential(module, inputName, {
      ...opts,
      streamPlans: missingTargets
    });
    return [...extracted, ...recovered].sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
  }

  return extracted.sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
}

async function buildInputSource(module, source) {
  if (source?.kind === 'file' && source.file) {
    const file = source.file;
    const mountPoint = `/opfs_input_${Date.now()}_${Math.random().toString(16).slice(2, 8)}`;
    const mountedName = `${mountPoint}/${file.name || 'embedded_input.bin'}`;
    try {
      ffmpegFs(module, 'mkdir', mountPoint);
    } catch (err) {
      const msg = String(err?.message || err || '');
      if (!/File exists|ErrnoError/i.test(msg)) {
        throw err;
      }
    }
    try {
      ffmpegMount(module, 'WORKERFS', { files: [file] }, mountPoint);
      sendLog('Mounted OPFS temp file via WORKERFS in dedicated demux worker.', 'info');
      return {
        inputName: mountedName,
        cleanup: () => {
          try { ffmpegUnmount(module, mountPoint); } catch (_) { /* ignore */ }
          try { ffmpegFs(module, 'rmdir', mountPoint); } catch (_) { /* ignore */ }
        }
      };
    } catch (err) {
      try { ffmpegUnmount(module, mountPoint); } catch (_) { /* ignore */ }
      try { ffmpegFs(module, 'rmdir', mountPoint); } catch (_) { /* ignore */ }
      throw new Error(`WORKERFS mount failed in dedicated demux worker: ${err?.message || err}`);
    }
  }

  const inputName = 'embedded_input.bin';
  const inputData = source?.kind === 'buffer'
    ? (source.buffer instanceof Uint8Array ? source.buffer : new Uint8Array(source.buffer || 0))
    : null;
  if (!inputData?.byteLength) {
    throw new Error('Worker demux received an empty input buffer.');
  }
  ffmpegFs(module, 'writeFile', inputName, inputData);
  return {
    inputName,
    cleanup: () => cleanupFsFile(module, inputName)
  };
}

function readTextTrack(module, file) {
  return buildExtractedTextTrack(module, file, null, new TextDecoder());
}

function readCopyTrack(module, file) {
  const data = ffmpegFs(module, 'readFile', file);
  const cloned = data instanceof Uint8Array ? data.slice() : new Uint8Array(data || []);
  const trackId = String(parseInt((file.match(/extracted_sub_(\d+)\.mkv$/i) || [])[1] || '0', 10));
  return {
    id: trackId,
    label: file,
    language: 'und',
    codec: 'copy',
    binary: true,
    mime: 'video/x-matroska',
    byteLength: cloned.byteLength,
    data: cloned.buffer
  };
}

async function runAudioDecode(payload) {
  const module = await ensureFfmpegCore(payload);
  const byteLength = Number(payload?.source?.byteLength) || 0;
  const sizeMb = Math.round((byteLength / (1024 * 1024)) * 10) / 10;
  const windows = Array.isArray(payload?.windows) ? payload.windows : [];
  if (!windows.length) {
    throw new Error('Dedicated audio worker received no decode windows.');
  }
  const audioStreamIndex = Number.isInteger(payload?.audioStreamIndex) ? payload.audioStreamIndex : 0;
  sendLog(`Starting dedicated audio decode worker (${payload?.source?.kind === 'file' ? 'mounted file' : 'buffer'} ~${sizeMb} MB, windows=${windows.length})`, 'info');

  let inputSource = null;
  try {
    inputSource = await buildInputSource(module, payload.source);
    const results = [];
    for (let i = 0; i < windows.length; i++) {
      const win = windows[i] || {};
      const outputName = `audio_decode_${i}.wav`;
      cleanupFsFile(module, outputName);
      const args = ['-y'];
      if (typeof win.seekToSec === 'number' && win.seekToSec > 0) {
        args.push('-ss', String(win.seekToSec));
      }
      args.push('-i', inputSource.inputName, '-vn');
      if (Number.isInteger(audioStreamIndex) && audioStreamIndex >= 0) {
        args.push('-map', `0:a:${audioStreamIndex}`);
      }
      args.push('-acodec', 'pcm_s16le', '-ar', '16000', '-ac', '1');
      if (typeof win.durSec === 'number' && win.durSec > 0) {
        args.push('-t', String(win.durSec));
      }
      args.push(outputName);
      await ffmpegRun(module, args);
      const data = ffmpegFs(module, 'readFile', outputName);
      if (!data?.byteLength) {
        throw new Error(`FFmpeg produced empty audio for window ${i + 1}`);
      }
      if (data.byteLength < 44) {
        throw new Error(`FFmpeg produced too-small audio for window ${i + 1} (${data.byteLength} bytes)`);
      }
      const cloned = data instanceof Uint8Array ? data.slice() : new Uint8Array(data || []);
      results.push({
        audioBytes: cloned.buffer,
        startMs: Math.round(((win.startSec ?? win.seekToSec ?? 0) || 0) * 1000)
      });
      cleanupFsFile(module, outputName);
    }
    return { audioWindows: results };
  } finally {
    try {
      for (const file of ffmpegFs(module, 'readdir', '/')) {
        if (/^audio_decode_\d+\.wav$/i.test(file)) {
          cleanupFsFile(module, file);
        }
      }
      inputSource?.cleanup?.();
    } catch (_) { /* ignore */ }
  }
}

async function runDemux(payload) {
  const module = await ensureFfmpegCore(payload);
  const byteLength = Number(payload?.source?.byteLength) || 0;
  const sizeMb = Math.round((byteLength / (1024 * 1024)) * 10) / 10;
  sendLog(`Starting dedicated demux worker (${payload?.source?.kind === 'file' ? 'mounted file' : 'buffer'} ~${sizeMb} MB)`, 'info');
  const hasExplicitStreamPlans = Array.isArray(payload?.streamPlans) && payload.streamPlans.length > 0;
  const hasExplicitTextPlans = Array.isArray(payload?.textStreamPlans) && payload.textStreamPlans.length > 0;
  const inputArgs = Array.isArray(payload?.inputArgs) && payload.inputArgs.length
    ? payload.inputArgs
    : ['-analyzeduration', '60M', '-probesize', '60M'];
  const skipCopyTracks = payload?.skipCopyTracks === true;
  const skipFlatCueRepair = payload?.skipFlatCueRepair === true;
  const copyStreamPlans = hasExplicitStreamPlans
    ? payload.streamPlans.filter((entry) => entry && entry.kind !== 'text')
    : null;

  let inputSource = null;
  let inputName = 'embedded_input.bin';
  let copiedTracks = [];
  let files = [];

  try {
    inputSource = await buildInputSource(module, payload.source || {});
    inputName = inputSource.inputName;

    sendLog('Running FFmpeg to extract subtitle streams...', 'info');
    if ((!hasExplicitStreamPlans || copyStreamPlans.length) && !skipCopyTracks) {
      copiedTracks = await extractSubtitleCopyTracks(module, inputName, copyStreamPlans ? {
        streamPlans: copyStreamPlans
      } : {});
    }
    if (hasExplicitTextPlans || !hasExplicitStreamPlans) {
      files = await extractSubtitleTextTracks(module, inputName, {
        streamPlans: hasExplicitTextPlans ? payload.textStreamPlans : undefined,
        inputArgs
      });
    }

    if (copiedTracks.length) {
      sendLog(`Preserved ${copiedTracks.length} subtitle stream(s) as MKV copy for bitmap-only detection.`, 'info');
    }

    if (copiedTracks.length) {
      const existingIds = new Set(files.map((file) => parseExtractedOutputIndex(file)).filter((value) => Number.isInteger(value) && value > 0));
      let skippedCopyTextConversions = 0;
      for (const copyName of copiedTracks) {
        const trackIdx = parseExtractedOutputIndex(copyName);
        if (Number.isInteger(trackIdx) && existingIds.has(trackIdx)) {
          continue;
        }
        const target = findExtractionTargetByOutputIndex(payload.textStreamPlans, trackIdx);
        const outputPlan = resolveTextSubtitleOutputPlan(target || {});
        const textName = copyName.replace(/\.mkv$/i, `.${outputPlan.ext}`);
        try {
          await ffmpegRun(
            module,
            '-y',
            '-analyzeduration', '60M',
            '-probesize', '60M',
            '-i', copyName,
            '-map', '0:s:0',
            '-c:s', outputPlan.ffmpegCodec,
            textName
          );
          const data = ffmpegFs(module, 'readFile', textName);
          if (data?.byteLength) {
            files.push(textName);
          } else {
            cleanupFsFile(module, textName);
          }
        } catch (convErr) {
          cleanupFsFile(module, textName);
          const classified = classifyWorkerFfmpegError(convErr?.message || convErr, 'FFmpeg could not convert the copied subtitle stream to text output.');
          if (classified.category === 'subtitle-kind-mismatch') {
            skippedCopyTextConversions += 1;
            continue;
          }
          sendLog(`Failed to convert ${copyName} to text subtitle output: ${classified.summary}`, 'warn');
        }
      }
      if (skippedCopyTextConversions > 0) {
        sendLog(
          `Left ${skippedCopyTextConversions} copied subtitle stream(s) as MKV because FFmpeg could not convert them directly to text output.`,
          'info'
        );
      }
      files = files.sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
    }

    if (files.length) {
      sendLog(`FFmpeg demux produced ${files.length} track file(s)`, 'info');
      let tracks = files.map((file) => {
        const outputIndex = parseExtractedOutputIndex(file);
        const target = findExtractionTargetByOutputIndex(payload.textStreamPlans, outputIndex);
        return buildExtractedTextTrack(module, file, target, new TextDecoder());
      });

      const timelineStatus = analyzeCueTimelines(tracks);
      if (timelineStatus.flatCueStarts && skipFlatCueRepair && !timelineStatus.nonMonotonicCues) {
        sendLog('Detected flat cue timestamps in a bounded demux pass; skipping PTS normalization for this slice.', 'info');
      } else if (timelineStatus.flatCueStarts || timelineStatus.nonMonotonicCues) {
        sendLog(`Detected ${timelineStatus.flatCueStarts ? 'flat' : 'non-monotonic'} cue timestamps; retrying with PTS normalization...`, 'warn');
        try {
          for (const file of ffmpegFs(module, 'readdir', '/')) {
            if (/^extracted_sub_(fix_)?\d+\.[a-z0-9]+$/i.test(file) && !/\.mkv$/i.test(file)) {
              try { ffmpegFs(module, 'unlink', file); } catch (_) { /* ignore */ }
            }
          }
          const fixedFiles = await extractSubtitleTextTracks(module, inputName, {
            streamPlans: payload.textStreamPlans,
            variant: 'fix',
            inputArgs: [
              '-fix_sub_duration',
              '-fflags', '+genpts',
              '-copyts',
              '-start_at_zero',
              '-analyzeduration', '60M',
              '-probesize', '60M'
            ],
            outputArgs: [
              '-avoid_negative_ts', 'make_zero',
              '-max_interleave_delta', '0',
              '-muxpreload', '0',
              '-muxdelay', '0'
            ]
          });
          if (fixedFiles.length) {
            const fixedTracks = fixedFiles.map((file) => {
              const outputIndex = parseExtractedOutputIndex(file);
              const target = findExtractionTargetByOutputIndex(payload.textStreamPlans, outputIndex);
              return buildExtractedTextTrack(module, file, target, new TextDecoder());
            });
            const mergedTracks = mergeReplacementTracks(tracks, fixedTracks);
            const fixedStatus = analyzeCueTimelines(mergedTracks);
            if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
              if (mergedTracks.length === tracks.length) {
                sendLog('PTS-normalized retry improved timelines; using fixed tracks.', 'info');
              } else {
                sendLog(
                  `PTS-normalized retry improved ${fixedTracks.length} track(s); keeping ${Math.max(0, tracks.length - fixedTracks.length)} original track(s) that were not regenerated.`,
                  'info'
                );
              }
              tracks = mergedTracks;
            } else {
              sendLog('PTS-normalized retry still looks broken; keeping original tracks.', 'warn');
            }
          } else {
            sendLog('PTS-normalized retry produced no replacement text outputs.', 'warn');
          }
        } catch (normErr) {
          sendLog(`PTS-normalized retry failed: ${normErr?.message || normErr}`, 'error');
        }
      }

      const postNormStatus = analyzeCueTimelines(tracks);
      if (postNormStatus.nonMonotonicCues || (postNormStatus.flatCueStarts && !skipFlatCueRepair)) {
        sendLog('Timelines still broken after PTS normalization; trying per-stream remux...', 'warn');
        try {
          const remuxed = [];
          const remuxTargets = Array.isArray(payload.textStreamPlans) && payload.textStreamPlans.length
            ? payload.textStreamPlans
            : getSubtitleExtractionTargets({});
          for (const target of remuxTargets) {
            const streamIndex = target.streamIndex;
            const outputIndex = target.outputIndex;
            const outName = `remux_sub_${String(outputIndex - 1).padStart(2, '0')}.mkv`;
            try {
              await ffmpegRun(
                module,
                '-y',
                '-analyzeduration', '60M',
                '-probesize', '60M',
                '-copyts',
                '-avoid_negative_ts', 'make_zero',
                '-i', inputName,
                '-map', `0:s:${streamIndex}`,
                '-c:s', 'copy',
                outName
              );
              const data = ffmpegFs(module, 'readFile', outName);
              if (data?.byteLength) {
                remuxed.push(outName);
              }
            } catch (_) {
              cleanupFsFile(module, outName);
              break;
            }
          }

          const fixedTracks = [];
          for (const remuxName of remuxed) {
            const remuxMatch = remuxName.match(/^remux_sub_(\d+)\.mkv$/i);
            const outputIndex = remuxMatch ? (parseInt(remuxMatch[1], 10) + 1) : null;
            const target = findExtractionTargetByOutputIndex(remuxTargets, outputIndex);
            const outputPlan = resolveTextSubtitleOutputPlan(target || {});
            const textName = remuxName.replace(/\.mkv$/i, `.${outputPlan.ext}`).replace(/^remux_sub_/, 'extracted_sub_fix_');
            try {
              await ffmpegRun(
                module,
                '-y',
                '-fix_sub_duration',
                '-fflags', '+genpts',
                '-copyts',
                '-start_at_zero',
                '-avoid_negative_ts', 'make_zero',
                '-analyzeduration', '60M',
                '-probesize', '60M',
                '-i', remuxName,
                '-map', '0:s:0',
                '-c:s', outputPlan.ffmpegCodec,
                textName
              );
              const data = ffmpegFs(module, 'readFile', textName);
              if (data?.byteLength) {
                fixedTracks.push(buildExtractedTextTrack(module, textName, target, new TextDecoder()));
              }
            } catch (convErr) {
              sendLog(`Remux conversion failed for ${remuxName}: ${convErr?.message || convErr}`, 'warn');
            }
          }

          if (fixedTracks.length) {
            const mergedTracks = mergeReplacementTracks(tracks, fixedTracks);
            const fixedStatus = analyzeCueTimelines(mergedTracks);
            if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
              if (mergedTracks.length === tracks.length) {
                sendLog('Per-stream remux fixed timelines; using remuxed tracks.', 'info');
              } else {
                sendLog(
                  `Per-stream remux fixed ${fixedTracks.length} track(s); keeping ${Math.max(0, tracks.length - fixedTracks.length)} prior track(s) that were not regenerated.`,
                  'info'
                );
              }
              tracks = mergedTracks;
            } else {
              sendLog('Per-stream remux still looks broken; keeping prior tracks.', 'warn');
            }
          } else {
            sendLog('Per-stream remux produced no usable tracks.', 'warn');
          }
        } catch (remuxErr) {
          sendLog(`Per-stream remux attempt failed: ${remuxErr?.message || remuxErr}`, 'error');
        }
      }

      return {
        textTracks: tracks,
        copyTracks: [],
        skippedCopies: copiedTracks.length
      };
    }

    sendLog('FFmpeg produced no text tracks; returning copied subtitle streams for fallback handling.', 'warn');
    return {
      textTracks: [],
      copyTracks: copiedTracks.map((file) => readCopyTrack(module, file)),
      skippedCopies: copiedTracks.length
    };
  } finally {
    try {
      for (const file of ffmpegFs(module, 'readdir', '/')) {
        if (/^(?:embedded_input\.bin|extracted_sub_(?:fix_)?\d+\.[a-z0-9]+|remux_sub_\d+\.mkv)$/i.test(file)) {
          cleanupFsFile(module, file);
        }
      }
      inputSource?.cleanup?.();
    } catch (_) { /* ignore */ }
  }
}

self.onmessage = async (event) => {
  const payload = event?.data || {};
  if (payload.type !== 'START') {
    return;
  }
  currentRequestId = payload.messageId || null;
  try {
    const action = payload?.action === 'audio-decode' ? 'audio-decode' : 'demux';
    const result = action === 'audio-decode'
      ? await runAudioDecode(payload)
      : await runDemux(payload);
    const transfer = [];
    if (action === 'audio-decode') {
      for (const win of result.audioWindows || []) {
        if (win?.audioBytes instanceof ArrayBuffer) {
          transfer.push(win.audioBytes);
        }
      }
    } else {
      for (const track of result.copyTracks || []) {
        if (track?.data instanceof ArrayBuffer) {
          transfer.push(track.data);
        }
      }
    }
    self.postMessage({ type: 'RESULT', result }, transfer);
  } catch (err) {
    self.postMessage({
      type: 'ERROR',
      error: err?.message || String(err || 'Unknown worker error')
    });
  }
};
