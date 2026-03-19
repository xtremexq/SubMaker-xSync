// Offscreen document runner for FFmpeg demux (embedded subtitles)
// Runs in a DOM context so FFmpeg can spawn Workers (not allowed in MV3 service worker)

function sendOffscreenLog(text, level = 'info', messageId) {
  if (!shouldEmitOffscreenLog(level)) return;
  if (shouldSuppressOffscreenLog(text, level, messageId)) return;
  try {
    chrome.runtime.sendMessage({
      type: 'OFFSCREEN_LOG',
      text,
      level,
      ts: Date.now(),
      messageId
    });
  } catch (_) { /* ignore */ }
}

console.log('[Offscreen] Initialized');

// Minimal stubs to satisfy ffmpeg.js expectations if needed
if (typeof self.document === 'undefined') {
  self.document = { baseURI: self.location?.href || '', currentScript: null };
}
if (typeof self.window === 'undefined') {
  self.window = self;
}

self.addEventListener('error', (evt) => {
  sendOffscreenLog(`Unhandled error: ${evt?.message || evt?.error?.message || evt}`, 'error');
});
self.addEventListener('unhandledrejection', (evt) => {
  sendOffscreenLog(`Unhandled rejection: ${evt?.reason?.message || evt?.reason || evt}`, 'error');
});

// Shared state
let _ffmpegInstance = null;
let _ffmpegMode = 'unknown';
let _bareFfmpegModule = null;
let _ffmpegLoadPromise = null;
let _debugEnabled = true; // default to verbose so extraction failures surface without manual toggles
const _chunkedBuffers = new Map();
const _activeOffscreenJobs = new Map();
const _activeDemuxWorkers = new Map();
const _offscreenLogSeen = new Map();
const CHUNK_BUFFER_TTL_MS = 5 * 60 * 1000;
const OUTGOING_CHUNK_BYTES = 512 * 1024;
const OUTGOING_CHUNK_THRESHOLD = 2.5 * 1024 * 1024; // approx 2.5MB before chunking
const OFFSCREEN_LOG_BUCKET_LIMIT = 400;
const FFMPEG_GLOBAL_ARGS = ['-hide_banner', '-nostats', '-loglevel', 'warning'];
const DIRECT_DEMUX_TIMEOUT_MS = 90 * 1000;
const OPFS_DEMUX_BASE_TIMEOUT_MS = 10 * 60 * 1000;
const OPFS_DEMUX_MAX_TIMEOUT_MS = 24 * 60 * 1000;
const OPFS_DEMUX_EXTRA_TIMEOUT_PER_GIB_MS = 6 * 60 * 1000;

const DEBUG_FLAG_KEY = 'debugLogsEnabled';
function refreshDebugFlag() {
  try {
    chrome.storage?.local.get([DEBUG_FLAG_KEY], (res) => {
      const stored = res?.[DEBUG_FLAG_KEY];
      if (typeof stored === 'boolean') {
        _debugEnabled = stored;
      }
    });
  } catch (_) { /* ignore */ }
}
refreshDebugFlag();
chrome.storage?.onChanged?.addListener((changes, area) => {
  if (area === 'local' && Object.prototype.hasOwnProperty.call(changes, DEBUG_FLAG_KEY)) {
    const next = changes[DEBUG_FLAG_KEY]?.newValue;
    _debugEnabled = typeof next === 'boolean' ? next : true;
  }
});

function shouldEmitOffscreenLog(level = 'info') {
  return _debugEnabled || level === 'error' || level === 'warn';
}

function normalizeOffscreenLogText(text) {
  return String(text || '')
    .replace(/@\s*0x[0-9a-f]+/ig, '@ 0xaddr')
    .replace(/\s+/g, ' ')
    .trim();
}

function isLowSignalFfmpegLog(text) {
  const lower = normalizeOffscreenLogText(text).toLowerCase();
  if (!lower) return true;
  return lower === 'metadata:'
    || lower === 'aborted()'
    || /^ffmpeg version\b/.test(lower)
    || /^configuration:/.test(lower)
    || /^built with emcc\b/.test(lower)
    || /^lib(av|sw|post)/.test(lower)
    || /^stream mapping:/.test(lower)
    || /^stream #\d+:\d+/.test(lower)
    || /^output #\d+,/.test(lower)
    || /^input #\d+,/.test(lower)
    || /^duration:/.test(lower)
    || /^title\s*:/.test(lower)
    || /^encoder\s*:/.test(lower)
    || /^creation_time\s*:/.test(lower)
    || /^size=\s*\d/.test(lower)
    || /^video:\d/.test(lower)
    || /^chapters:?$/.test(lower)
    || /^chapter #\d+:\d+:/.test(lower)
    || /^filename\s*:/.test(lower)
    || /^mimetype\s*:/.test(lower)
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
    || /non-monotonous dts in output stream/.test(lower)
    || /\[ass @ .*?\] readorder gap found between \d+ and \d+/.test(lower)
    || /readorder gap found between \d+ and \d+/.test(lower);
}

function splitOffscreenLogLines(text) {
  return String(text || '')
    .split(/\r?\n+/)
    .map((entry) => normalizeOffscreenLogText(entry))
    .filter(Boolean);
}

function computeOffscreenDemuxTimeoutMs(transferMethod, byteLength) {
  if (transferMethod !== 'opfs') {
    return DIRECT_DEMUX_TIMEOUT_MS;
  }
  const oneGiB = 1024 * 1024 * 1024;
  const bytes = Math.max(0, Number(byteLength) || 0);
  if (bytes <= oneGiB) {
    return OPFS_DEMUX_BASE_TIMEOUT_MS;
  }
  const extraGiB = Math.ceil((bytes - oneGiB) / oneGiB);
  return Math.min(
    OPFS_DEMUX_MAX_TIMEOUT_MS,
    OPFS_DEMUX_BASE_TIMEOUT_MS + (extraGiB * OPFS_DEMUX_EXTRA_TIMEOUT_PER_GIB_MS)
  );
}

function classifyOffscreenFfmpegError(text, fallback = 'FFmpeg failed') {
  const lines = splitOffscreenLogLines(text);
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
  const useful = lines.filter((line) => !isLowSignalFfmpegLog(line));
  const summary = useful[useful.length - 1] || lines[lines.length - 1] || fallback;
  const compact = summary.length > 240 ? `${summary.slice(0, 237)}...` : summary;
  return { category: 'generic', summary: compact };
}

function shouldSuppressOffscreenLog(text, level = 'info', messageId) {
  const normalized = normalizeOffscreenLogText(text);
  if (!normalized) return true;
  if (level !== 'error' && isLowSignalFfmpegLog(normalized)) {
    return true;
  }
  const bucketKey = messageId || '__global__';
  let seen = _offscreenLogSeen.get(bucketKey);
  if (!seen) {
    seen = new Set();
    _offscreenLogSeen.set(bucketKey, seen);
  }
  const dedupeKey = `${String(level || 'info').toLowerCase()}:${normalized}`;
  if (seen.has(dedupeKey)) {
    return true;
  }
  if (seen.size >= OFFSCREEN_LOG_BUCKET_LIMIT) {
    seen.clear();
  }
  seen.add(dedupeKey);
  return false;
}

function stashChunk(transferId, chunkIndex, totalChunks, chunk, expectedBytes, chunkArray) {
  if (!transferId || totalChunks <= 0 || chunkIndex < 0 || chunkIndex >= totalChunks || (!chunk && !chunkArray)) {
    return { ok: false, error: 'Invalid chunk metadata' };
  }
  let part = chunk instanceof Uint8Array ? chunk : (chunk ? new Uint8Array(chunk) : null);
  if ((!part || !part.byteLength) && Array.isArray(chunkArray)) {
    part = new Uint8Array(chunkArray);
  }
  const partBytes = part?.byteLength || 0;
  if (!partBytes) {
    return { ok: false, error: `Empty chunk received (index ${chunkIndex + 1}/${totalChunks})` };
  }
  if (expectedBytes && partBytes !== expectedBytes) {
    return { ok: false, error: `Chunk size mismatch at ${chunkIndex + 1}/${totalChunks}: expected ${expectedBytes}, got ${partBytes}` };
  }
  let entry = _chunkedBuffers.get(transferId);
  if (!entry || entry.totalChunks !== totalChunks) {
    entry = { totalChunks, parts: new Array(totalChunks), received: 0, timer: null };
    _chunkedBuffers.set(transferId, entry);
  }
  if (!entry.parts[chunkIndex]) {
    entry.received += 1;
  }
  entry.parts[chunkIndex] = part;
  if (entry.timer) clearTimeout(entry.timer);
  entry.timer = setTimeout(() => _chunkedBuffers.delete(transferId), CHUNK_BUFFER_TTL_MS);
  const complete = entry.received === entry.totalChunks && entry.parts.every(Boolean);
  return { ok: true, complete, received: entry.received, total: entry.totalChunks };
}

function consumeChunkedBuffer(transferId) {
  const entry = _chunkedBuffers.get(transferId);
  if (!entry || !entry.parts || entry.parts.length !== entry.totalChunks || entry.parts.some(p => !p)) {
    return null;
  }
  const totalBytes = entry.parts.reduce((n, p) => n + (p?.byteLength || 0), 0);
  const merged = new Uint8Array(totalBytes);
  let offset = 0;
  for (const p of entry.parts) {
    merged.set(p, offset);
    offset += p.byteLength;
  }
  if (entry.timer) clearTimeout(entry.timer);
  _chunkedBuffers.delete(transferId);
  return merged;
}

function createAbortError(reason = 'Operation aborted') {
  const message = typeof reason === 'string' && reason ? reason : 'Operation aborted';
  const err = new Error(message);
  err.name = 'AbortError';
  return err;
}

function isAbortError(err) {
  if (!err) return false;
  return err.name === 'AbortError'
    || err.code === 'ABORT_ERR'
    || /aborted|cancelled|canceled/i.test(err?.message || '');
}

function beginOffscreenJob(messageId) {
  if (!messageId) return null;
  const job = {
    messageId,
    aborted: false,
    reason: '',
    startedAt: Date.now()
  };
  _activeOffscreenJobs.set(messageId, job);
  return job;
}

function finishOffscreenJob(messageId) {
  if (!messageId) return;
  const workerEntry = _activeDemuxWorkers.get(messageId);
  if (workerEntry) {
    _activeDemuxWorkers.delete(messageId);
    try { workerEntry.worker?.terminate?.(); } catch (_) { /* ignore */ }
    try { workerEntry.reject?.(createAbortError('Offscreen job finished')); } catch (_) { /* ignore */ }
  }
  _activeOffscreenJobs.delete(messageId);
  _offscreenLogSeen.delete(messageId);
}

function markOffscreenJobAborted(messageId, reason = 'Operation aborted') {
  if (!messageId) return false;
  const job = _activeOffscreenJobs.get(messageId);
  if (!job) return false;
  job.aborted = true;
  job.reason = reason || 'Operation aborted';
  const workerEntry = _activeDemuxWorkers.get(messageId);
  if (workerEntry) {
    _activeDemuxWorkers.delete(messageId);
    try { workerEntry.worker?.terminate?.(); } catch (_) { /* ignore */ }
    try { workerEntry.reject?.(createAbortError(job.reason)); } catch (_) { /* ignore */ }
  }
  return true;
}

function throwIfOffscreenJobAborted(messageId) {
  if (!messageId) return;
  const job = _activeOffscreenJobs.get(messageId);
  if (job?.aborted) {
    throw createAbortError(job.reason || 'Operation aborted');
  }
}

function prependDefaultFfmpegArgs(rawArgv) {
  const argv = Array.isArray(rawArgv) ? rawArgv.slice() : [];
  const insertAt = argv[0] === '-y' ? 1 : 0;
  argv.splice(insertAt, 0, ...FFMPEG_GLOBAL_ARGS);
  return argv;
}

async function sendResultChunksToBackground(transferId, buffer, messageId, label = 'result') {
  if (!(buffer instanceof Uint8Array)) {
    throw new Error('sendResultChunksToBackground expects Uint8Array');
  }
  const totalBytes = buffer.byteLength;
  const totalChunks = Math.max(1, Math.ceil(totalBytes / OUTGOING_CHUNK_BYTES));
  for (let i = 0; i < totalChunks; i++) {
    const start = i * OUTGOING_CHUNK_BYTES;
    const end = Math.min(totalBytes, start + OUTGOING_CHUNK_BYTES);
    const view = buffer.subarray(start, end);
    const chunkArray = Array.from(view);
    const shouldLog = totalChunks <= 20 || i === 0 || i === totalChunks - 1 || ((i + 1) % 25 === 0);
    await new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({
        type: 'OFFSCREEN_RESULT_CHUNK',
        transferId,
        chunkIndex: i,
        totalChunks,
        chunkArray,
        expectedBytes: view.byteLength,
        messageId,
        label
      }, (resp) => {
        if (chrome.runtime.lastError) {
          return reject(new Error(chrome.runtime.lastError.message));
        }
        if (resp?.ok === false) {
          return reject(new Error(resp?.error || `Chunk ${i + 1}/${totalChunks} rejected`));
        }
        if (shouldLog) {
          console.log('[Offscreen] Result chunk sent', { transferId, idx: i + 1, totalChunks, label });
        }
        resolve();
      });
    });
  }
  return { transferId, totalChunks, totalBytes };
}

async function prepareTracksForSend(tracks, messageId) {
  if (!Array.isArray(tracks)) return { tracks: [] };
  const encoder = new TextEncoder();
  const prepared = [];
  let chunked = false;

  for (let i = 0; i < tracks.length; i++) {
    const t = tracks[i] || {};
    const base = { ...t };
    const trackLabel = `track_${i + 1}`;

    const stringContent = typeof t.content === 'string' ? t.content : null;
    const base64Content = !stringContent && typeof t.contentBase64 === 'string' ? t.contentBase64 : null;

    const toBytes = () => {
      if (stringContent !== null) {
        return encoder.encode(stringContent);
      }
      if (base64Content !== null) {
        try {
          const bin = atob(base64Content);
          const out = new Uint8Array(bin.length);
          for (let j = 0; j < bin.length; j++) out[j] = bin.charCodeAt(j);
          return out;
        } catch (err) {
          console.warn('[Offscreen] Failed to decode base64 track', err);
        }
      }
      return null;
    };

    const bytes = toBytes();
    const byteLength = bytes?.byteLength || 0;
    if (bytes && byteLength > OUTGOING_CHUNK_THRESHOLD) {
      const transferId = `${trackLabel}_${messageId || Date.now()}_${Math.random().toString(16).slice(2)}`;
      await sendResultChunksToBackground(transferId, bytes, messageId, trackLabel);
      delete base.content;
      delete base.contentBase64;
      prepared.push({
        ...base,
        transferId,
        byteLength,
        chunked: true
      });
      chunked = true;
    } else {
      prepared.push(base);
    }
  }

  return { tracks: prepared, chunked };
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

function inferTrackFileExt(track = {}) {
  if (track?.binary || track?.codec === 'copy' || String(track?.mime || '').toLowerCase().includes('matroska')) {
    return 'mkv';
  }
  return resolveTextSubtitleOutputPlan(track).ext;
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

  for (const t of tracks || []) {
    const starts = collectCueWindowsFromTrack(t).map((entry) => entry.startSec);
    if (!starts.length) continue;
    if (shouldTreatNonMonotonicCueOrderAsBroken(t)) {
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
    if (flatCueStarts && nonMonotonicCues) break;
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

function buildExtractedTextTrack(file, data, target = null, decoder = new TextDecoder()) {
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

function uint8ToBase64(u8) {
  let str = '';
  for (let i = 0; i < u8.length; i++) {
    str += String.fromCharCode(u8[i]);
  }
  return btoa(str);
}

function decodeUtf8Safe(u8) {
  try {
    return new TextDecoder('utf-8', { fatal: false }).decode(u8);
  } catch (_) {
    try {
      return new TextDecoder().decode(u8);
    } catch (_) {
      return '';
    }
  }
}

function readVint(u8, offset) {
  const first = u8[offset];
  if (first === undefined) return null;
  let length = 1;
  let mask = 0x80;
  while (length <= 8 && (first & mask) === 0) {
    length += 1;
    mask >>= 1;
  }
  if (length > 8 || offset + length > u8.length) return null;
  let value = BigInt(first & (mask - 1));
  for (let i = 1; i < length; i++) {
    value = (value * 256n) + BigInt(u8[offset + i]);
  }
  const unknownValue = (1n << BigInt(7 * length)) - 1n;
  return {
    length,
    value: value > BigInt(Number.MAX_SAFE_INTEGER) ? Number.MAX_SAFE_INTEGER : Number(value),
    valueBigInt: value,
    isUnknownSize: value === unknownValue,
    exceedsSafeInteger: value > BigInt(Number.MAX_SAFE_INTEGER)
  };
}

function readEbmlElement(u8, offset, limit) {
  if (offset >= limit) return null;
  const idInfo = readVint(u8, offset);
  if (!idInfo) return null;
  // For element IDs, preserve the full raw bytes (VINT marker bits included).
  let idRaw = 0;
  for (let i = 0; i < idInfo.length; i++) {
    idRaw = (idRaw << 8) | u8[offset + i];
  }
  const sizeInfo = readVint(u8, offset + idInfo.length);
  if (!sizeInfo) return null;
  const dataStart = offset + idInfo.length + sizeInfo.length;
  let size = sizeInfo.value;
  // Unknown-size EBML elements set all size bits; treat as consuming the remaining scan window
  if (sizeInfo.isUnknownSize || sizeInfo.exceedsSafeInteger) {
    size = Math.max(0, limit - dataStart);
  }
  let dataEnd = dataStart + size;
  if (dataEnd > limit) {
    // Element spills past the scanned window (common when probing with a byte range).
    // Cap to the available buffer so we can still walk nested headers like Tracks.
    dataEnd = limit;
    size = Math.max(0, dataEnd - dataStart);
  }
  if (dataStart >= limit) return null;
  return {
    id: idRaw >>> 0,
    idHex: (idRaw >>> 0).toString(16).toUpperCase(),
    size,
    header: idInfo.length + sizeInfo.length,
    dataStart,
    dataEnd
  };
}

function parseMkvHeaderInfo(buffer, opts = {}) {
  const u8 = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer || 0);
  const limit = Math.min(u8.length, opts.maxScanBytes || u8.length);
  const info = {
    segmentOffset: null,
    seekHead: [],
    tracks: [],
    cues: [],
    attachments: [],
    chapters: []
  };

  const ID = {
    SEGMENT: '18538067',
    SEEK_HEAD: '114D9B74',
    SEEK: '4DBB',
    SEEK_ID: '53AB',
    SEEK_POSITION: '53AC',
    CUES: '1C53BB6B',
    CUE_POINT: 'BB',
    CUE_TIME: 'B3',
    CUE_TRACK_POSITIONS: 'B7',
    CUE_TRACK: 'F7',
    CUE_CLUSTER_POS: 'F1',
    CUE_REL_POS: 'F0',
    TRACKS: '1654AE6B',
    TRACK_ENTRY: 'AE',
    TRACK_NUMBER: 'D7',
    TRACK_TYPE: '83',
    TRACK_NAME: '536E',
    TRACK_LANGUAGE: '22B59C',       // RFC 1766 / ISO-639-2
    TRACK_LANGUAGE_IETF: '22B59D',  // RFC 5646 (modern)
    CODEC_ID: '86',
    ATTACHMENTS: '1941A469',
    ATTACHED_FILE: '61A7',
    FILE_NAME: '466E',
    FILE_MIME: '4660',
    FILE_DATA: '465C',
    CHAPTERS: '1043A770',
    EDITION_ENTRY: '45B9',
    CHAPTER_ATOM: 'B6',
    CHAPTER_TIME_START: '91',
    CHAPTER_TIME_END: '92'
  };

  function parseUint(u8Arr, start, end) {
    let v = 0n;
    for (let i = start; i < end; i++) v = (v * 256n) + BigInt(u8Arr[i]);
    return v > BigInt(Number.MAX_SAFE_INTEGER) ? Number.MAX_SAFE_INTEGER : Number(v);
  }

  function parseString(u8Arr, start, end) {
    return decodeUtf8Safe(u8Arr.subarray(start, end)).trim();
  }

  function walk(start, end, handlers) {
    let p = start;
    while (p < end) {
      const el = readEbmlElement(u8, p, end);
      if (!el) break;
      const handler = handlers?.[el.idHex];
      if (handler) {
        handler(el);
      }
      p = el.dataEnd;
    }
  }

  let segmentStart = null;
  walk(0, limit, {
    [ID.SEGMENT]: (el) => {
      segmentStart = el.dataStart;
      info.segmentOffset = el.dataStart;
      const segEnd = Math.min(el.dataEnd, limit);
      walk(el.dataStart, segEnd, {
        [ID.SEEK_HEAD]: parseSeekHead,
        [ID.TRACKS]: parseTracks,
        [ID.CUES]: parseCues,
        [ID.ATTACHMENTS]: parseAttachments,
        [ID.CHAPTERS]: parseChapters
      });
    }
  });

  function parseSeekHead(el) {
    walk(el.dataStart, Math.min(el.dataEnd, limit), {
      [ID.SEEK]: (seekEl) => {
        let seekId = null;
        let seekPos = null;
        walk(seekEl.dataStart, Math.min(seekEl.dataEnd, limit), {
          [ID.SEEK_ID]: (idEl) => { seekId = parseUint(u8, idEl.dataStart, idEl.dataEnd); },
          [ID.SEEK_POSITION]: (posEl) => { seekPos = parseUint(u8, posEl.dataStart, posEl.dataEnd); }
        });
        if (seekId !== null && seekPos !== null) {
          info.seekHead.push({ id: seekId, idHex: seekId.toString(16).toUpperCase(), position: seekPos });
        }
      }
    });
  }

  function parseTracks(el) {
    walk(el.dataStart, Math.min(el.dataEnd, limit), {
      [ID.TRACK_ENTRY]: (tEl) => {
        const track = { number: null, type: null, name: '', language: '', languageIetf: '', codecId: '' };
        walk(tEl.dataStart, Math.min(tEl.dataEnd, limit), {
          [ID.TRACK_NUMBER]: (nEl) => { track.number = parseUint(u8, nEl.dataStart, nEl.dataEnd); },
          [ID.TRACK_TYPE]: (tEl2) => { track.type = parseUint(u8, tEl2.dataStart, tEl2.dataEnd); },
          [ID.TRACK_NAME]: (nEl) => { track.name = parseString(u8, nEl.dataStart, nEl.dataEnd); },
          [ID.TRACK_LANGUAGE]: (lEl) => { track.language = parseString(u8, lEl.dataStart, lEl.dataEnd); },
          [ID.TRACK_LANGUAGE_IETF]: (lEl) => { track.languageIetf = parseString(u8, lEl.dataStart, lEl.dataEnd); },
          [ID.CODEC_ID]: (cEl) => { track.codecId = parseString(u8, cEl.dataStart, cEl.dataEnd); }
        });
        if (track.languageIetf && !track.language) {
          track.language = track.languageIetf;
        }
        info.tracks.push(track);
      }
    });
  }

  function parseCues(el) {
    walk(el.dataStart, Math.min(el.dataEnd, limit), {
      [ID.CUE_POINT]: (cpEl) => {
        let cueTime = null;
        const positions = [];
        walk(cpEl.dataStart, Math.min(cpEl.dataEnd, limit), {
          [ID.CUE_TIME]: (tEl) => { cueTime = parseUint(u8, tEl.dataStart, tEl.dataEnd); },
          [ID.CUE_TRACK_POSITIONS]: (posEl) => {
            let track = null, clusterPos = null, relPos = null;
            walk(posEl.dataStart, Math.min(posEl.dataEnd, limit), {
              [ID.CUE_TRACK]: (elT) => { track = parseUint(u8, elT.dataStart, elT.dataEnd); },
              [ID.CUE_CLUSTER_POS]: (elP) => { clusterPos = parseUint(u8, elP.dataStart, elP.dataEnd); },
              [ID.CUE_REL_POS]: (elRP) => { relPos = parseUint(u8, elRP.dataStart, elRP.dataEnd); }
            });
            positions.push({ track, clusterPos, relPos });
          }
        });
        if (cueTime !== null) {
          info.cues.push({ time: cueTime, positions });
        }
      }
    });
  }

  function parseAttachments(el) {
    walk(el.dataStart, Math.min(el.dataEnd, limit), {
      [ID.ATTACHED_FILE]: (aEl) => {
        let name = '';
        let mime = '';
        let data = null;
        walk(aEl.dataStart, Math.min(aEl.dataEnd, limit), {
          [ID.FILE_NAME]: (f) => { name = parseString(u8, f.dataStart, f.dataEnd); },
          [ID.FILE_MIME]: (f) => { mime = parseString(u8, f.dataStart, f.dataEnd); },
          [ID.FILE_DATA]: (f) => { data = u8.subarray(f.dataStart, Math.min(f.dataEnd, limit)); }
        });
        if (data && data.length) {
          info.attachments.push({ name, mime, data });
        }
      }
    });
  }

  function parseChapters(el) {
    walk(el.dataStart, Math.min(el.dataEnd, limit), {
      [ID.EDITION_ENTRY]: (edEl) => {
        walk(edEl.dataStart, Math.min(edEl.dataEnd, limit), {
          [ID.CHAPTER_ATOM]: (chEl) => {
            let start = null;
            let end = null;
            walk(chEl.dataStart, Math.min(chEl.dataEnd, limit), {
              [ID.CHAPTER_TIME_START]: (sEl) => { start = parseUint(u8, sEl.dataStart, sEl.dataEnd); },
              [ID.CHAPTER_TIME_END]: (eEl) => { end = parseUint(u8, eEl.dataStart, eEl.dataEnd); }
            });
            if (start !== null) {
              info.chapters.push({ start, end });
            }
          }
        });
      }
    });
  }

  return { ...info, segmentOffset: segmentStart ?? info.segmentOffset };
}

// Naming helpers to keep extracted tracks consistent across modes
const EXTRACTED_PREFIX = 'extracted_sub';
const EXTRACTED_SRT_PATTERN = /^extracted_sub_\d+\.srt$/i;
const EXTRACTED_COPY_PATTERN = /^extracted_sub_\d+\.mkv$/i;
const EXTRACTED_FIX_PATTERN = /^extracted_sub_fix_\d+\.srt$/i;

const TRACK_LANG_NORMALIZE_MAP = {
  eng: 'en', enu: 'en', enus: 'en', enn: 'en', enuk: 'en', en_gb: 'en', 'en-gb': 'en', enus: 'en', engb: 'en', enau: 'en', enze: 'en',
  spa: 'es', esl: 'es', esu: 'es', esp: 'es', espanol: 'es', spn: 'es', es419: 'es', lat: 'es', latam: 'es', castellano: 'es',
  por: 'por', pt: 'por', porpt: 'por', pt_pt: 'por', 'pt-pt': 'por', ptpt: 'por',
  pob: 'pob', pb: 'pob', ptb: 'pob', ptbr: 'pob', 'pt-br': 'pob', porbr: 'pob', brazpor: 'pob', brazilian: 'pob',
  fre: 'fr', fra: 'fr', frf: 'fr', frca: 'fr', frfr: 'fr',
  ger: 'de', deu: 'de', gerde: 'de',
  ita: 'it', itb: 'it',
  rus: 'ru', rusru: 'ru',
  chi: 'zh', zho: 'zh', cmn: 'zh', mlt: 'zh', mnd: 'zh', chs: 'zh', cht: 'zh', zhn: 'zh', zhcn: 'zh', zhtw: 'zh', zh_hans: 'zh', 'zh-hans': 'zh', zh_hant: 'zh', 'zh-hant': 'zh',
  jpn: 'ja', jap: 'ja', jp: 'ja',
  kor: 'ko', korus: 'ko', kr: 'ko',
  ara: 'ar', arg: 'ar', arb: 'ar', arq: 'ar',
  hin: 'hi', hnd: 'hi',
  tur: 'tr', turk: 'tr',
  pol: 'pl',
  dut: 'nl', nld: 'nl', hol: 'nl', fla: 'nl', vla: 'nl',
  swe: 'sv', sve: 'sv',
  nor: 'no', nob: 'no', nno: 'no', norw: 'no', bok: 'no', nyn: 'no',
  dan: 'da',
  fin: 'fi',
  hun: 'hu', hunh: 'hu',
  ces: 'cs', cze: 'cs',
  ell: 'el', gre: 'el', grk: 'el',
  heb: 'he', arahe: 'he', hebrew: 'he', iw: 'he',
  vie: 'vi', vit: 'vi',
  ind: 'id', ina: 'id', bah: 'id',
  tha: 'th',
  ukr: 'uk', ukraines: 'uk',
  ron: 'ro', rum: 'ro', rom: 'ro', rop: 'ro',
  bul: 'bg',
  slk: 'sk', slo: 'sk',
  slv: 'sl',
  hrv: 'hr', cro: 'hr',
  srp: 'sr', scc: 'sr',
  bos: 'bs',
  cat: 'ca',
  fas: 'fa', per: 'fa', pes: 'fa', farsi: 'fa',
  urd: 'ur',
  ben: 'bn', bang: 'bn',
  tam: 'ta',
  tel: 'te',
  mar: 'mr',
  kan: 'kn',
  mal: 'ml',
  pan: 'pa', pun: 'pa',
  guj: 'gu',
  nep: 'ne',
  sin: 'si',
  mya: 'my', bur: 'my',
  khm: 'km',
  lao: 'lo', laoian: 'lo',
  mon: 'mn',
  uzb: 'uz',
  kaz: 'kk',
  kir: 'ky',
  tgk: 'tg',
  tuk: 'tk',
  pus: 'ps', pst: 'ps',
  som: 'so',
  amh: 'am',
  hau: 'ha',
  yor: 'yo',
  zul: 'zu',
  xho: 'xh',
  afr: 'af',
  eus: 'eu', baq: 'eu',
  glg: 'gl',
  glv: 'gv',
  gle: 'ga',
  cym: 'cy', wel: 'cy',
  isl: 'is',
  sqi: 'sq', alb: 'sq',
  mkd: 'mk', mac: 'mk',
  est: 'et',
  lit: 'lt',
  lav: 'lv',
  aze: 'az',
  kat: 'ka', geo: 'ka',
  amh: 'am',
  epo: 'eo',
  fil: 'tl', tgl: 'tl',
  msa: 'ms', may: 'ms'
};

const LANGUAGE_NAME_ALIASES = {
  english: 'en', anglisch: 'en', anglais: 'en', ingles: 'en',
  spanish: 'es', espanol: 'es', castellano: 'es', latino: 'es', latam: 'es',
  portuguese: 'por', portugues: 'por', portugal: 'por',
  brazilian: 'pob', brazillian: 'pob', brazillianportuguese: 'pob', brazilianportuguese: 'pob', portuguese_brazil: 'pob', portuguese_brazilian: 'pob',
  french: 'fr', francais: 'fr', francophone: 'fr',
  german: 'de', deutsch: 'de',
  italian: 'it', italiano: 'it',
  russian: 'ru', russisch: 'ru', russkiy: 'ru',
  chinese: 'zh', mandarin: 'zh', cantonese: 'zh', taiwanese: 'zh',
  japanese: 'ja', nihongo: 'ja',
  korean: 'ko', hangul: 'ko',
  arabic: 'ar',
  hindi: 'hi',
  turkish: 'tr',
  polish: 'pl',
  dutch: 'nl', flemish: 'nl', nederlands: 'nl',
  swedish: 'sv', svenska: 'sv',
  norwegian: 'no', bokmal: 'no', nynorsk: 'no',
  danish: 'da', dansk: 'da',
  finnish: 'fi', suomi: 'fi',
  hungarian: 'hu', magyar: 'hu',
  czech: 'cs', cesky: 'cs',
  greek: 'el', hellenic: 'el',
  hebrew: 'he', yiddish: 'yi',
  vietnamese: 'vi',
  indonesian: 'id', bahasa: 'id',
  thai: 'th',
  ukrainian: 'uk',
  romanian: 'ro',
  bulgarian: 'bg',
  slovak: 'sk',
  slovenian: 'sl',
  croatian: 'hr',
  serbian: 'sr',
  bosnian: 'bs',
  catalan: 'ca',
  persian: 'fa', farsi: 'fa', dari: 'fa',
  urdu: 'ur',
  bengali: 'bn',
  tamil: 'ta',
  telugu: 'te',
  marathi: 'mr',
  kannada: 'kn',
  malayalam: 'ml',
  punjabi: 'pa',
  gujarati: 'gu',
  nepali: 'ne',
  sinhala: 'si',
  burmese: 'my',
  khmer: 'km',
  lao: 'lo',
  mongolian: 'mn',
  uzbek: 'uz',
  kazakh: 'kk',
  kyrgyz: 'ky',
  tajik: 'tg',
  turkmen: 'tk',
  pashto: 'ps',
  somali: 'so',
  amharic: 'am',
  hausa: 'ha',
  yoruba: 'yo',
  zulu: 'zu',
  xhosa: 'xh',
  afrikaans: 'af',
  basque: 'eu',
  galician: 'gl',
  irish: 'ga',
  welsh: 'cy',
  icelandic: 'is',
  albanian: 'sq',
  macedonian: 'mk',
  estonian: 'et',
  lithuanian: 'lt',
  latvian: 'lv',
  azerbaijani: 'az',
  georgian: 'ka',
  esperanto: 'eo',
  tagalog: 'tl',
  filipino: 'tl',
  malay: 'ms'
};

function normalizeTrackLanguageCode(raw) {
  if (!raw) return null;
  const rawStr = String(raw).trim().toLowerCase();
  if (rawStr === 'und' || rawStr === 'unk' || rawStr === 'unknown' || rawStr === 'auto') return null;
  if (/^extracte/.test(rawStr)) return null;
  if (/^extracted[_\s-]?sub/.test(rawStr)) return null;
  if (/^remux[_\s-]?sub/.test(rawStr)) return null;
  if (/^track\s*\d+/.test(rawStr)) return null;
  if (/^subtitle\s*\d+/.test(rawStr)) return null;
  const cleaned = rawStr.replace(/_/g, '-').replace(/[^a-z-]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '');
  if (!cleaned) return null;
  if (TRACK_LANG_NORMALIZE_MAP[cleaned]) return TRACK_LANG_NORMALIZE_MAP[cleaned];
  if (LANGUAGE_NAME_ALIASES[cleaned]) return LANGUAGE_NAME_ALIASES[cleaned];
  const compact = cleaned.replace(/-/g, '');
  if (TRACK_LANG_NORMALIZE_MAP[compact]) return TRACK_LANG_NORMALIZE_MAP[compact];
  if (LANGUAGE_NAME_ALIASES[compact]) return LANGUAGE_NAME_ALIASES[compact];
  const base = cleaned.split('-')[0];
  if (!base) return null;
  if (TRACK_LANG_NORMALIZE_MAP[base]) return TRACK_LANG_NORMALIZE_MAP[base];
  if (LANGUAGE_NAME_ALIASES[base]) return LANGUAGE_NAME_ALIASES[base];
  if (base.length === 2) return base;
  if (base.length === 3 && TRACK_LANG_NORMALIZE_MAP[base]) return TRACK_LANG_NORMALIZE_MAP[base];
  if (base.length === 3) return base;
  return base.slice(0, 8);
}

function detectLanguageFromLabel(label) {
  if (!label) return null;
  const lowered = String(label).toLowerCase();
  if (/^extracte/.test(lowered)) return null;
  if (/^extracted[_\s-]?sub/.test(lowered)) return null;
  if (/^remux[_\s-]?sub/.test(lowered)) return null;
  if (/^track\s+\d+/.test(lowered)) return null;
  if (/^subtitle\s+\d+/.test(lowered)) return null;
  if (lowered.includes('brazil')) return 'pob';
  if (lowered.includes('portuguese (br')) return 'pob';
  const codeMatch = lowered.match(/(?:^|\[|\(|\s)([a-z]{2,3})(?:\s|$|\]|\))/);
  if (codeMatch) {
    const byCode = normalizeTrackLanguageCode(codeMatch[1]);
    if (byCode) return byCode;
  }
  const cleaned = lowered.replace(/[^a-z\s]/g, ' ').replace(/\s+/g, ' ').trim();
  if (!cleaned) return null;
  if (LANGUAGE_NAME_ALIASES[cleaned]) return LANGUAGE_NAME_ALIASES[cleaned];
  const parts = cleaned.split(' ');
  for (const part of parts) {
    const byName = LANGUAGE_NAME_ALIASES[part];
    if (byName) return byName;
    const byCode = normalizeTrackLanguageCode(part);
    if (byCode) return byCode;
  }
  return null;
}

function detectLanguageFromContent(text) {
  if (!text || typeof text !== 'string') return null;
  const sample = text.slice(0, 48000);
  const cyrillicLetters = (sample.match(/[\u0400-\u04FF]/g) || []).length;
  const latinLetters = (sample.match(/[A-Za-z\u00C0-\u024F]/g) || []).length;
  if (cyrillicLetters > 24 && cyrillicLetters >= latinLetters * 0.15) return 'ru';
  const cueCount = (sample.match(/\d{1,2}:\d{2}:\d{2}[,\.]\d{3}\s+-->\s+\d{1,2}:\d{2}:\d{2}[,\.]\d{3}/g) || []).length;

  const cleaned = sample
    .replace(/<[^>]+>/g, ' ')
    .replace(/&[a-z]+;/gi, ' ')
    .replace(/\d{2}:\d{2}:\d{2}[,\.]\d{3}\s+-->\s+\d{2}:\d{2}:\d{2}[,\.]\d{3}/g, ' ')
    .replace(/\d+\s*\n\d{2}:\d{2}:\d{2}[^\n]*-->[^\n]+/g, ' ')
    .replace(/[^A-Za-z\u00C0-\u024F]+/g, ' ')
    .toLowerCase();
  const normalized = cleaned.normalize('NFD').replace(/[\u0300-\u036f]/g, '');
  const words = normalized.split(/\s+/).filter((w) => w.length > 1);
  if (!words.length) return null;
  const totalWords = words.length;
  const uniqueWords = new Set(words);
  if (totalWords < 18 || uniqueWords.size < 8 || (latinLetters < 80 && cueCount < 4)) return null;
  const counts = {};
  for (const w of words) counts[w] = (counts[w] || 0) + 1;

  const STOPWORDS = {
    en: ['the', 'and', 'you', 'that', 'this', 'for', 'with', 'not', 'have', 'just', 'like', 'know', 'yeah', 'but', 'are', 'your', 'all', 'get', 'about', 'would', 'there', 'right', 'think', 'really', 'here', 'can', 'now', 'well', 'got', 'they'],
    es: ['que', 'de', 'no', 'la', 'el', 'es', 'y', 'en', 'lo', 'un', 'por', 'una', 'te', 'los', 'se', 'con', 'para', 'mi', 'bien', 'pero', 'si', 'del', 'al', 'me', 'como'],
    pob: ['que', 'nao', 'uma', 'por', 'voce', 'voces', 'pra', 'ele', 'ela', 'isso', 'esta', 'ser', 'mais', 'bem'],
    por: ['que', 'nao', 'uma', 'por', 'ele', 'ela', 'isso', 'esta', 'ser', 'mais', 'bem', 'voces', 'tambem'],
    fr: ['que', 'qui', 'oui', 'non', 'je', 'vous', 'pour', 'avec', 'est', 'pas', 'une', 'des', 'les', 'dans', 'comme', 'mais', 'nous', 'elle', 'il', 'tu', 'sur'],
    de: ['und', 'ich', 'nicht', 'die', 'das', 'der', 'du', 'was', 'mit', 'mir', 'sie', 'ist', 'ein', 'eine', 'dass', 'ja', 'auf', 'für', 'aber', 'wie'],
    it: ['che', 'non', 'per', 'con', 'una', 'questo', 'questa', 'sono', 'sei', 'era', 'hai', 'ciao', 'perche', 'ma', 'come', 'gli', 'nel', 'degli']
  };

  let best = null;
  let bestScore = 0;
  let bestHits = 0;
  let runnerUp = 0;
  for (const [lang, list] of Object.entries(STOPWORDS)) {
    let hits = 0;
    for (const word of list) {
      hits += counts[word] || 0;
    }
    const score = hits / Math.max(12, totalWords);
    if (score > bestScore) {
      runnerUp = bestScore;
      bestScore = score;
      bestHits = hits;
      best = lang;
    } else if (score > runnerUp) {
      runnerUp = score;
    }
  }

  const asciiLetters = (sample.match(/[A-Za-z]/g) || []).length;
  const nonAsciiLetters = (sample.match(/[^\x00-\x7F]/g) || []).length;
  const asciiRatio = asciiLetters / Math.max(1, asciiLetters + nonAsciiLetters);

  if (best && bestHits >= 4 && (bestScore >= 0.05 || (bestScore >= 0.03 && bestScore >= runnerUp * 1.5))) {
    return normalizeTrackLanguageCode(best) || best;
  }
  if (!best && asciiRatio > 0.9 && latinLetters > 120 && totalWords >= 24) return 'en';
  return null;
}

function isWeakLanguageSource(track) {
  const source = String(track?.languageSource || '').toLowerCase();
  return !source || source === 'content-guess' || source === 'label';
}

function getTrackMetadataLanguage(track) {
  return normalizeTrackLanguageCode(
    track?.languageRaw || track?.languageCode || track?.languageIetf || track?.langCode || track?.languageTag || track?.langTag
  );
}

function getTrackMetadataLanguageRaw(track, fallback = '') {
  const candidates = [
    track?.languageRaw,
    track?.languageCode,
    track?.languageIetf,
    track?.langCode,
    track?.languageTag,
    track?.langTag
  ];
  const chosen = candidates.find((value) => normalizeTrackLanguageCode(value));
  return chosen || fallback || '';
}

function applyContentLanguageGuesses(tracks) {
  if (!Array.isArray(tracks)) return tracks || [];
  return tracks.map((track) => {
    if (!track) return track;
    const metadataLang = getTrackMetadataLanguage(track);
    const currentLang = normalizeTrackLanguageCode(track.language);
    const weakSource = isWeakLanguageSource(track);
    if (metadataLang && (!currentLang || track.language === 'und' || weakSource)) {
      return {
        ...track,
        language: metadataLang,
        languageRaw: getTrackMetadataLanguageRaw(track, metadataLang),
        languageSource: weakSource ? 'metadata' : (track.languageSource || 'metadata')
      };
    }
    if (currentLang && track.language !== currentLang) {
      return {
        ...track,
        language: currentLang
      };
    }
    if (track.language && track.language !== 'und') return track;
    const content = typeof track.content === 'string' ? track.content : null;
    const guess = detectLanguageFromContent(content);
    if (guess) {
      return {
        ...track,
        language: guess,
        languageRaw: guess,
        languageSource: 'content-guess'
      };
    }
    return track;
  });
}

function collectSubtitleLanguagesFromMkv(buffer) {
  if (!buffer || typeof buffer.byteLength !== 'number' || buffer.byteLength === 0) return [];
  try {
    const parseTracks = (maxScanBytes) => {
      const headerInfo = parseMkvHeaderInfo(buffer, { maxScanBytes });
      const subtitleTracks = (headerInfo?.tracks || []).filter((t) => {
        const codec = (t.codecId || '').toLowerCase();
        return t.type === 0x11 || t.type === 17 || codec.includes('s_text') || codec.includes('subtitle') || codec.includes('subrip') || codec.includes('ass') || codec.includes('pgs');
      });
      return subtitleTracks.map((t, idx) => {
        const name = t.name || '';
        const normalizedLang = normalizeTrackLanguageCode(t.languageIetf || t.language) || detectLanguageFromLabel(name) || null;
        return {
          index: idx,
          trackNumber: typeof t.number === 'number' ? t.number : null,
          lang: normalizedLang,
          languageRaw: t.languageIetf || t.language || '',
          name
        };
      }).filter(entry => !!entry.lang);
    };

    const primaryLimit = Math.min(buffer.byteLength, 24 * 1024 * 1024);
    let langs = parseTracks(primaryLimit);
    if (!langs.length && buffer.byteLength > primaryLimit) {
      const deepLimit = Math.min(buffer.byteLength, 96 * 1024 * 1024);
      if (deepLimit > primaryLimit) {
        langs = parseTracks(deepLimit);
      }
    }
    return langs;
  } catch (_) {
    return [];
  }
}

function collectSubtitleLanguagesFromMp4(buffer) {
  if (!buffer || typeof buffer.byteLength !== 'number' || buffer.byteLength === 0) return [];
  const u8 = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
  const len = u8.length;
  const readU32 = (off) => (u8[off] << 24 | u8[off + 1] << 16 | u8[off + 2] << 8 | u8[off + 3]) >>> 0;
  const readStr = (off, count) => String.fromCharCode(...u8.subarray(off, off + count));

  const handlersForSubs = new Set(['sbtl', 'subt', 'text', 'tx3g', 'wvtt', 'stpp', 'clcp']);
  const tracks = [];

  const walkBoxes = (start, end, visitor) => {
    let p = start;
    while (p + 8 <= end) {
      const size = readU32(p);
      const type = readStr(p + 4, 4);
      if (!size) break;
      const boxEnd = size === 1
        ? Math.min(end, p + 16 + Number(readU32(p + 8)) * 2 ** 32)
        : Math.min(end, p + size);
      visitor(type, p + 8, boxEnd);
      if (boxEnd <= p) break;
      p = boxEnd;
    }
  };

  const decodeMdhdLanguage = (mdhdStart, mdhdEnd) => {
    if (mdhdStart + 12 >= mdhdEnd) return null;
    const version = u8[mdhdStart];
    const langOffset = version === 1 ? mdhdStart + 20 : mdhdStart + 12;
    if (langOffset + 2 > mdhdEnd) return null;
    const langBits = (u8[langOffset] << 8) | u8[langOffset + 1];
    const c1 = ((langBits >> 10) & 0x1F) + 0x60;
    const c2 = ((langBits >> 5) & 0x1F) + 0x60;
    const c3 = (langBits & 0x1F) + 0x60;
    const code = String.fromCharCode(c1, c2, c3).replace(/\0/g, '').trim();
    if (!code || code === 'und') return null;
    return normalizeTrackLanguageCode(code) || code;
  };

  const decodeTrackIdFromTkhd = (start, end) => {
    const version = u8[start];
    const idOffset = version === 1 ? start + 20 : start + 12;
    if (idOffset + 4 > end) return null;
    return readU32(idOffset);
  };

  const parseTrak = (trakStart, trakEnd, trakIndex) => {
    let handler = null;
    let lang = null;
    let trackId = null;
    walkBoxes(trakStart, trakEnd, (type, boxStart, boxEnd) => {
      if (type === 'tkhd' && trackId === null) {
        trackId = decodeTrackIdFromTkhd(boxStart, boxEnd);
      } else if (type === 'mdia') {
        walkBoxes(boxStart, boxEnd, (mdType, mdStart, mdEnd) => {
          if (mdType === 'hdlr') {
            if (mdStart + 8 <= mdEnd) {
              handler = readStr(mdStart + 4, 4);
            }
          } else if (mdType === 'mdhd' && !lang) {
            lang = decodeMdhdLanguage(mdStart, mdEnd);
          }
        });
      }
    });
    if (!handler || !handlersForSubs.has(handler)) return;
    if (!lang) return;
    tracks.push({
      index: trakIndex,
      trackNumber: trackId !== null ? trackId : null,
      lang,
      languageRaw: lang,
      name: ''
    });
  };

  try {
    walkBoxes(0, len, (type, start, end) => {
      if (type === 'moov') {
        let idx = 0;
        walkBoxes(start, end, (innerType, innerStart, innerEnd) => {
          if (innerType === 'trak') {
            parseTrak(innerStart, innerEnd, idx++);
          }
        });
      }
    });
  } catch (_) {
    return [];
  }
  return tracks;
}

function collectSubtitleLanguagesFromHeader(buffer) {
  const mkv = collectSubtitleLanguagesFromMkv(buffer);
  if (mkv.length) return mkv;
  const mp4 = collectSubtitleLanguagesFromMp4(buffer);
  if (mp4.length) return mp4;
  return [];
}

function isSubtitleAttachmentFile(att) {
  if (!att) return false;
  const lowerName = String(att.name || '').toLowerCase();
  const lowerMime = String(att.mime || '').toLowerCase();
  return lowerMime.startsWith('text/')
    || lowerMime.includes('subtitle')
    || lowerName.endsWith('.srt')
    || lowerName.endsWith('.ass')
    || lowerName.endsWith('.ssa')
    || lowerName.endsWith('.vtt')
    || lowerName.endsWith('.sub');
}

function probeMkvSubtitleMetadata(buffer) {
  if (!buffer || typeof buffer.byteLength !== 'number' || buffer.byteLength === 0) return null;
  try {
    const shallowScanBytes = Math.min(buffer.byteLength, 24 * 1024 * 1024);
    let scanBytes = shallowScanBytes;
    let headerInfo = parseMkvHeaderInfo(buffer, { maxScanBytes: scanBytes });
    const initialTracks = Array.isArray(headerInfo?.tracks) ? headerInfo.tracks : [];
    if (!initialTracks.length && buffer.byteLength > shallowScanBytes) {
      const deepScanBytes = Math.min(buffer.byteLength, 96 * 1024 * 1024);
      if (deepScanBytes > shallowScanBytes) {
        scanBytes = deepScanBytes;
        headerInfo = parseMkvHeaderInfo(buffer, { maxScanBytes: scanBytes });
      }
    }
    const tracks = Array.isArray(headerInfo?.tracks) ? headerInfo.tracks : [];
    const subtitleTracks = tracks.filter((t) => {
      const codec = String(t?.codecId || '').toLowerCase();
      return t?.type === 0x11 || t?.type === 17 || codec.includes('s_text') || codec.includes('subtitle') || codec.includes('subrip') || codec.includes('ass') || codec.includes('pgs');
    });
    const subtitleAttachments = (headerInfo?.attachments || []).filter(isSubtitleAttachmentFile);
    return {
      scanBytes,
      tracks,
      subtitleTracks,
      subtitleAttachments
    };
  } catch (_) {
    return null;
  }
}

function formatMkvTrackProbe(track) {
  if (!track) return '';
  let typeLabel = 'unknown';
  if (track.type === 0x01 || track.type === 1) typeLabel = 'video';
  else if (track.type === 0x02 || track.type === 2) typeLabel = 'audio';
  else if (track.type === 0x11 || track.type === 17) typeLabel = 'subtitle';
  else if (track.type === 0x12 || track.type === 18) typeLabel = 'buttons';
  else if (typeof track.type === 'number') typeLabel = `type=${track.type}`;
  const parts = [`#${track.number ?? '?'}`, typeLabel];
  if (track.codecId) parts.push(track.codecId);
  if (track.languageIetf || track.language) parts.push(track.languageIetf || track.language);
  if (track.name) parts.push(`"${track.name}"`);
  return parts.join(' ');
}

function isTextSubtitleCodec(codecId) {
  const codec = String(codecId || '').toLowerCase();
  if (!codec) return false;
  return codec.includes('s_text')
    || codec.includes('subrip')
    || codec.includes('utf8')
    || codec.includes('ssa')
    || codec.includes('ass')
    || codec.includes('webvtt')
    || codec.includes('vtt')
    || codec.includes('mov_text')
    || codec.includes('tx3g');
}

function isBitmapSubtitleCodec(codecId) {
  const codec = String(codecId || '').toLowerCase();
  if (!codec) return false;
  return codec.includes('pgs')
    || codec.includes('hdmv')
    || codec.includes('vobsub')
    || codec.includes('dvd_subtitle')
    || codec.includes('dvb_subtitle')
    || codec.includes('xsub')
    || codec.includes('pgssub')
    || codec.includes('sup');
}

function buildMkvSubtitleExtractionPlan(mkvProbe) {
  if (!Array.isArray(mkvProbe?.subtitleTracks) || !mkvProbe.subtitleTracks.length) return [];
  return mkvProbe.subtitleTracks.map((track, idx) => {
    const codecId = String(track?.codecId || '');
    const kind = isTextSubtitleCodec(codecId)
      ? 'text'
      : (isBitmapSubtitleCodec(codecId) ? 'bitmap' : 'unknown');
    return {
      streamIndex: idx,
      outputIndex: idx + 1,
      kind,
      codecId,
      trackNumber: typeof track?.number === 'number' ? track.number : null,
      language: track?.languageIetf || track?.language || '',
      name: track?.name || ''
    };
  });
}

function isNoSubtitleStreamErrorMessage(message) {
  const lower = String(message || '').toLowerCase();
  return lower.includes('matches no streams')
    || lower.includes('does not contain any stream')
    || lower.includes('output file does not contain any stream')
    || lower.includes('stream map')
    || lower.includes('no stream');
}

function applyHeaderLanguagesToTracks(tracks, headerLangs) {
  if (!Array.isArray(tracks) || !tracks.length || !Array.isArray(headerLangs) || !headerLangs.length) return tracks || [];
  const usable = headerLangs.filter((l) => l && l.lang);
  if (!usable.length) return tracks;
  const canOverrideExistingLanguage = (track) => {
    return !track?.language
      || track.language === 'und'
      || isWeakLanguageSource(track);
  };

  const isGeneratedLabel = (label) => {
    if (!label) return true;
    const lower = String(label).toLowerCase();
    if (/^extracted[_\s-]?sub/.test(lower)) return true;
    if (/^remux[_\s-]?sub/.test(lower)) return true;
    if (/^track\s+\d+/.test(lower)) return true;
    if (/^subtitle\s+\d+/.test(lower)) return true;
    return false;
  };

  return tracks.map((track, idx) => {
    const numericId = Number(track?.id);
    const langEntry = (() => {
      if (Number.isInteger(numericId)) {
        const byTrackNumber = usable.find((l) => l.trackNumber !== null && (l.trackNumber === numericId || l.trackNumber === numericId + 1));
        if (byTrackNumber) return byTrackNumber;
        const byIndex = usable.find((l) => l.index === numericId - 1 || l.index === numericId);
        if (byIndex) return byIndex;
      }
      return usable[idx] || null;
    })();
    if (langEntry?.lang && canOverrideExistingLanguage(track)) {
      const nextLabel = !track?.label || isGeneratedLabel(track.label)
        ? (langEntry.name || track?.label || `Track ${idx + 1}`)
        : track.label;
      return {
        ...track,
        language: langEntry.lang,
        languageRaw: langEntry.languageRaw || langEntry.lang,
        languageSource: 'container-header',
        name: track?.name || langEntry.name || '',
        label: nextLabel
      };
    }
    if (!canOverrideExistingLanguage(track)) {
      return track;
    }
    const labelSource = [track?.label, track?.name, track?.originalLabel].find((l) => l && !isGeneratedLabel(l));
    const labelGuess = labelSource ? detectLanguageFromLabel(labelSource) : null;
    if (labelGuess) {
      return {
        ...track,
        language: labelGuess,
        languageRaw: labelGuess,
        languageSource: 'label'
      };
    }
    return track;
  });
}

const formatExtractedName = (index, ext = 'srt', variant = '') => {
  const num = String(index).padStart(2, '0');
  const prefix = variant ? `${EXTRACTED_PREFIX}_${variant}_` : `${EXTRACTED_PREFIX}_`;
  return `${prefix}${num}.${ext}`;
};

function normalizeExtractedTracks(tracks) {
  if (!Array.isArray(tracks)) return [];
  return tracks.map((t, idx) => {
    const ext = inferTrackFileExt(t);
    const label = formatExtractedName(idx + 1, ext);
    const outputPlan = t?.binary ? null : resolveTextSubtitleOutputPlan(t);
    return {
      ...t,
      id: String(idx + 1),
      label,
      codec: t?.binary ? (t?.codec || 'copy') : (t?.codec || outputPlan?.codec || 'srt'),
      mime: t?.binary ? (t?.mime || 'video/x-matroska') : (t?.mime || outputPlan?.mime || 'application/x-subrip; charset=utf-8'),
      originalLabel: t?.originalLabel || t?.label
    };
  });
}

function loadScriptTag(url, label, messageId) {
  return new Promise((resolve, reject) => {
    try {
      const script = document.createElement('script');
      script.src = url;
      script.async = true;
      script.onload = () => {
        console.log(`[Offscreen] Loaded ${label}`);
        sendOffscreenLog(`Loaded ${label}`, 'info', messageId);
        resolve();
      };
      script.onerror = (e) => {
        console.warn(`[Offscreen] Failed to load ${label}:`, e);
        sendOffscreenLog(`Failed to load ${label}: ${e?.message || e}`, 'warn', messageId);
        reject(new Error(`Failed to load ${label}`));
      };
      document.head.appendChild(script);
    } catch (err) {
      reject(err);
    }
  });
}

const PADDLE_OCR_URLS = (() => {
  const local = (file) => {
    try {
      return chrome?.runtime?.getURL ? chrome.runtime.getURL(`assets/lib/paddle/${file}`) : null;
    } catch (_) {
      return null;
    }
  };
  const core = local('paddlejs-core.js');
  const backend = local('paddlejs-backend-webgl.js');
  const opencv = local('paddlejs-opencv.js');
  const ocr = local('paddlejs-ocr.js');
  return { core, backend, opencv, ocr };
})();

const TESSERACT_URLS = (() => {
  const url = (file) => {
    try {
      return chrome?.runtime?.getURL ? chrome.runtime.getURL(`assets/lib/tesseract/${file}`) : null;
    } catch (_) {
      return null;
    }
  };
  const langBase = (() => {
    try {
      return chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/tesseract/') : null;
    } catch (_) {
      return null;
    }
  })();
  const main = url('tesseract.min.js');
  const worker = url('worker.min.js');
  const core = url('tesseract-core.wasm');
  const langPath = langBase || undefined; // directory; Tesseract appends /<lang>.traineddata
  return { main, worker, core, langPath };
})();

let _paddleOcrReady = false;
let _paddleOcrLoading = null;
let _paddleCvReady = false;
let _tesseractLoading = null;

const IMAGE_SUBTITLE_OCR_NOT_IMPLEMENTED_MESSAGE = 'Image-based subtitle streams were detected, but OCR extraction is not implemented yet.';

function throwImageSubtitleOcrNotImplemented(messageId, copyTrackCount = 0) {
  const countLabel = copyTrackCount > 0
    ? `${copyTrackCount} image-based subtitle stream(s)`
    : 'image-based subtitle streams';
  sendOffscreenLog(
    `Detected ${countLabel} (likely PGS/VobSub). OCR extraction is not implemented yet, so the job stops here.`,
    'error',
    messageId
  );
  throw new Error(IMAGE_SUBTITLE_OCR_NOT_IMPLEMENTED_MESSAGE);
}

async function waitForOpencvReady(messageId) {
  if (_paddleCvReady) return;
  const cvReady = self?.cv?.ready;
  if (cvReady && typeof cvReady.then === 'function') {
    await withTimeout(cvReady, 60000, 'OpenCV (paddle) init timed out');
    _paddleCvReady = true;
    sendOffscreenLog('OpenCV runtime ready for PaddleOCR', 'info', messageId);
  }
}

async function decodePngToImage(pngBytes, messageId) {
  const bytes = pngBytes instanceof Uint8Array ? pngBytes : new Uint8Array(pngBytes || []);
  const blob = new Blob([bytes], { type: 'image/png' });
  const url = URL.createObjectURL(blob);

  // Prefer HTMLImageElement so PaddleOCR can read naturalWidth/naturalHeight.
  if (typeof Image === 'function') {
    return new Promise((resolve, reject) => {
      try {
        const img = new Image();
        img.decoding = 'async';
        img.onload = () => {
          URL.revokeObjectURL(url);
          resolve(img);
        };
        img.onerror = (err) => {
          URL.revokeObjectURL(url);
          reject(new Error(`Image decode failed: ${err?.message || err}`));
        };
        img.src = url;
      } catch (err) {
        URL.revokeObjectURL(url);
        reject(err);
      }
    });
  }

  // Fallback to drawing an ImageBitmap into a canvas with natural* metadata.
  if (typeof createImageBitmap === 'function') {
    const bmp = await createImageBitmap(blob);
    const canvas = typeof document !== 'undefined' ? document.createElement('canvas') : new OffscreenCanvas(bmp.width, bmp.height);
    canvas.width = bmp.width;
    canvas.height = bmp.height;
    try {
      canvas.getContext('2d').drawImage(bmp, 0, 0);
    } catch (_) { /* ignore */ }
    try { bmp.close?.(); } catch (_) { /* ignore */ }
    URL.revokeObjectURL(url);
    // Annotate so PaddleOCR math works even if the target is a canvas.
    canvas.naturalWidth = canvas.width;
    canvas.naturalHeight = canvas.height;
    return canvas;
  }

  URL.revokeObjectURL(url);
  const err = new Error('No image decoding APIs available in offscreen context');
  sendOffscreenLog(`OCR: ${err.message}`, 'error', messageId);
  throw err;
}

async function ensurePaddleOcrLoaded(messageId) {
  if (!PADDLE_OCR_URLS.core || !PADDLE_OCR_URLS.backend || !PADDLE_OCR_URLS.opencv || !PADDLE_OCR_URLS.ocr) {
    throw new Error('PaddleOCR assets unavailable (local only, no CDN fallback)');
  }
  if (_paddleOcrReady && self?.paddlejs?.ocr) return self.paddlejs.ocr;
  if (_paddleOcrLoading) return _paddleOcrLoading;
  _paddleOcrLoading = (async () => {
    sendOffscreenLog('Loading PaddleOCR dependencies...', 'info', messageId);
    await loadScriptTag(PADDLE_OCR_URLS.core, 'paddlejs-core', messageId);
    await loadScriptTag(PADDLE_OCR_URLS.backend, 'paddlejs-backend-webgl', messageId);
    await loadScriptTag(PADDLE_OCR_URLS.opencv, 'paddlejs-mediapipe-opencv', messageId);
    await waitForOpencvReady(messageId);
    await loadScriptTag(PADDLE_OCR_URLS.ocr, 'paddlejs-models-ocr', messageId);
    if (!self?.paddlejs?.ocr) {
      throw new Error('PaddleOCR global missing after script load');
    }
    if (typeof self.paddlejs.ocr.init === 'function') {
      await withTimeout(self.paddlejs.ocr.init(), 120000, 'PaddleOCR init timed out');
    }
    _paddleOcrReady = true;
    sendOffscreenLog('PaddleOCR initialized', 'info', messageId);
    return self.paddlejs.ocr;
  })();
  return _paddleOcrLoading;
}

async function ensureTesseractLoaded(messageId) {
  if (_tesseractLoading) return _tesseractLoading;
  _tesseractLoading = (async () => {
    if (!TESSERACT_URLS.main || !TESSERACT_URLS.worker || !TESSERACT_URLS.core) {
      throw new Error('Tesseract assets unavailable');
    }
    const workerUrl = TESSERACT_URLS.worker;
    if (/^https?:/i.test(workerUrl || '')) {
      throw new Error('Refusing CDN Tesseract worker (workerPath must be packaged)');
    }
    sendOffscreenLog('Loading Tesseract.js OCR...', 'info', messageId);
    await loadScriptTag(TESSERACT_URLS.main, 'tesseract.js', messageId);
    if (!self?.Tesseract?.createWorker) {
      throw new Error('Tesseract global missing after script load');
    }
    try {
      // Force Tesseract to use our packaged assets only.
      self.Tesseract.setDefaultOptions?.({
        workerPath: workerUrl,
        corePath: TESSERACT_URLS.core,
        langPath: TESSERACT_URLS.langPath,
        workerBlobURL: false
      });
    } catch (err) {
      console.warn('[Offscreen] Failed to set Tesseract default options', err);
    }
    sendOffscreenLog('Tesseract.js ready', 'info', messageId);
    return self.Tesseract;
  })();
  return _tesseractLoading;
}

function parsePtsFromFilename(name) {
  const match = name.match(/_(\d+)\.png$/i);
  if (!match) return null;
  const raw = Number(match[1]);
  if (!Number.isFinite(raw)) return null;
  if (raw > 1e9) return raw / 90000; // assume 90k clock
  if (raw > 1e6) return raw / 1000;  // assume ms
  if (raw > 90000) return raw / 90000;
  if (raw > 10000) return raw / 1000;
  return raw;
}

function formatSrtTimestamp(sec) {
  const clamped = Math.max(0, Number.isFinite(sec) ? sec : 0);
  const msTotal = Math.round(clamped * 1000);
  const ms = msTotal % 1000;
  const totalSeconds = (msTotal - ms) / 1000;
  const s = totalSeconds % 60;
  const totalMinutes = (totalSeconds - s) / 60;
  const m = totalMinutes % 60;
  const h = (totalMinutes - m) / 60;
  const pad = (v, len = 2) => String(v).padStart(len, '0');
  return `${pad(h)}:${pad(m)}:${pad(s)},${pad(ms, 3)}`;
}

function cuesToSrt(cues) {
  return cues.map((cue, idx) => {
    const start = formatSrtTimestamp(cue.start);
    const end = formatSrtTimestamp(cue.end);
    const text = cue.text || '';
    return `${idx + 1}\n${start} --> ${end}\n${text.trim()}\n`;
  }).join('\n');
}

async function runTesseractOcrOnCopiedTracks(ffmpeg, copiedTracks, messageId) {
  const T = await ensureTesseractLoaded(messageId);
  const worker = await T.createWorker({
    workerPath: TESSERACT_URLS.worker,
    corePath: TESSERACT_URLS.core,
    langPath: TESSERACT_URLS.langPath,
    workerBlobURL: false,
    logger: () => {} // quiet
  });
  await worker.load();
  await worker.loadLanguage('eng');
  await worker.initialize('eng');

  const tracks = [];
  const MAX_FRAMES = 500; // keep reasonable for CPU
  const DEFAULT_DURATION = 4;

  let trackNo = 0;
  try {
    for (const copyName of copiedTracks) {
      trackNo += 1;
      const framePrefix = `tess_${String(trackNo).padStart(2, '0')}_`;
      sendOffscreenLog(`OCR (Tesseract): exporting bitmaps for ${copyName}...`, 'info', messageId);
      await ffmpeg.run(
        '-y',
        '-analyzeduration', '60M',
        '-probesize', '60M',
        '-i', copyName,
        '-map', '0:s:0',
        '-vsync', '0',
        '-frame_pts', '1',
        `${framePrefix}%05d.png`
      );

      let frameFiles = ffmpeg.FS('readdir', '/')
        .filter(f => f.startsWith(framePrefix) && f.endsWith('.png'))
        .sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));

      if (!frameFiles.length) {
        sendOffscreenLog(`OCR (Tesseract): no bitmap frames for ${copyName}`, 'warn', messageId);
        continue;
      }
      if (frameFiles.length > MAX_FRAMES) {
        sendOffscreenLog(`OCR (Tesseract): limiting frames for ${copyName} to ${MAX_FRAMES} (had ${frameFiles.length})`, 'warn', messageId);
        frameFiles = frameFiles.slice(0, MAX_FRAMES);
      }

      const cues = [];
      for (let i = 0; i < frameFiles.length; i++) {
        const file = frameFiles[i];
        const data = ffmpeg.FS('readFile', file);
        let img = null;
        try {
          img = await decodePngToImage(data, messageId);
        } catch (imgErr) {
          sendOffscreenLog(`OCR (Tesseract): failed to decode frame ${file}: ${imgErr?.message || imgErr}`, 'warn', messageId);
          continue;
        }
        try {
          const result = await worker.recognize(img);
          const text = (result?.data?.text || '').trim();
          if (!text) continue;
          const startSec = parsePtsFromFilename(file);
          const nextStart = i < frameFiles.length - 1 ? parsePtsFromFilename(frameFiles[i + 1]) : null;
          const endSec = Number.isFinite(nextStart) && nextStart > (startSec || 0)
            ? nextStart
            : (startSec || 0) + DEFAULT_DURATION;
          cues.push({ start: startSec || 0, end: endSec, text });
        } catch (ocrErr) {
          sendOffscreenLog(`OCR (Tesseract): failed on ${file}: ${ocrErr?.message || ocrErr}`, 'warn', messageId);
        }
      }

      for (const f of frameFiles) {
        try { ffmpeg.FS('unlink', f); } catch (_) { }
      }

      if (!cues.length) {
        sendOffscreenLog(`OCR (Tesseract): no text produced for ${copyName}`, 'warn', messageId);
        continue;
      }

      const srtContent = cuesToSrt(cues);
      tracks.push({
        id: String(trackNo),
        label: `OCR Track ${trackNo} (Tesseract)`,
        language: 'eng',
        codec: 'srt',
        source: 'ocr',
        binary: false,
        byteLength: srtContent.length,
        content: srtContent
      });
    }
  } finally {
    try { await worker.terminate(); } catch (_) { }
  }

  return tracks;
}

async function runPaddleOcrOnCopiedTracks(ffmpeg, copiedTracks, messageId) {
  const ocr = await ensurePaddleOcrLoaded(messageId);
  const tracks = [];
  const MAX_FRAMES = 2000;
  const DEFAULT_DURATION = 4; // seconds

  let trackNo = 0;
  for (const copyName of copiedTracks) {
    trackNo += 1;
    sendOffscreenLog(`OCR: exporting bitmaps for ${copyName}...`, 'info', messageId);
    const framePrefix = `ocr_${String(trackNo).padStart(2, '0')}_`;
    // Extract all subtitle bitmaps with pts in filenames
    await ffmpeg.run(
      '-y',
      '-analyzeduration', '60M',
      '-probesize', '60M',
      '-i', copyName,
      '-map', '0:s:0',
      '-vsync', '0',
      '-frame_pts', '1',
      `${framePrefix}%05d.png`
    );

    let frameFiles = ffmpeg.FS('readdir', '/')
      .filter(f => f.startsWith(framePrefix) && f.endsWith('.png'))
      .sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));

    if (!frameFiles.length) {
      sendOffscreenLog(`OCR: no bitmap frames exported for ${copyName}`, 'warn', messageId);
      continue;
    }

    if (frameFiles.length > MAX_FRAMES) {
      sendOffscreenLog(`OCR: limiting frames for ${copyName} to ${MAX_FRAMES} (had ${frameFiles.length})`, 'warn', messageId);
      frameFiles = frameFiles.slice(0, MAX_FRAMES);
    }

    const cues = [];
    for (let i = 0; i < frameFiles.length; i++) {
      const file = frameFiles[i];
      const data = ffmpeg.FS('readFile', file);
      let img = null;
      try {
        img = await decodePngToImage(data, messageId);
      } catch (imgErr) {
        sendOffscreenLog(`OCR: failed to decode frame ${file}: ${imgErr?.message || imgErr}`, 'warn', messageId);
        continue;
      }

      let result = null;
      if (typeof ocr?.detect === 'function') {
        result = await ocr.detect(img);
      } else if (typeof ocr?.recognize === 'function') {
        result = await ocr.recognize(img);
      } else {
        throw new Error('PaddleOCR API missing (detect/recognize not found)');
      }

      const texts = Array.isArray(result?.text) ? result.text : Array.isArray(result) ? result.map(r => r?.text || r).filter(Boolean) : [];
      const text = (texts || []).filter(Boolean).map(String).join('\n').trim();
      if (!text) {
        continue;
      }
      const startSec = parsePtsFromFilename(file);
      const nextStart = i < frameFiles.length - 1 ? parsePtsFromFilename(frameFiles[i + 1]) : null;
      const endSec = Number.isFinite(nextStart) && nextStart > (startSec || 0)
        ? nextStart
        : (startSec || 0) + DEFAULT_DURATION;
      cues.push({ start: startSec || 0, end: endSec, text });
    }

    // Cleanup frames to keep FS tidy
    for (const f of frameFiles) {
      try { ffmpeg.FS('unlink', f); } catch (_) { }
    }

    if (!cues.length) {
      sendOffscreenLog(`OCR: no text produced for ${copyName}`, 'warn', messageId);
      continue;
    }

    const srtContent = cuesToSrt(cues);
    tracks.push({
      id: String(trackNo),
      label: `OCR Track ${trackNo} (PaddleOCR)`,
      language: 'und',
      codec: 'srt',
      source: 'ocr',
      binary: false,
      byteLength: srtContent.length,
      content: srtContent
    });
  }

  return tracks;
}

function isHttpUrl(url) {
  return /^https?:\/\//i.test(String(url || ''));
}

async function loadBareFfmpegCore(messageId) {
  if (_bareFfmpegModule && _ffmpegInstance) return _ffmpegInstance;
  const coreUrl = chrome.runtime.getURL('assets/lib/ffmpeg-core.js');
  sendOffscreenLog('Loading direct FFmpeg core...', 'info', messageId);
  throwIfOffscreenJobAborted(messageId);
  await loadScriptTag(coreUrl, 'ffmpeg-core.js', messageId);
  if (typeof self.createFFmpegCore !== 'function') {
    throw new Error('createFFmpegCore not found after loading core script');
  }
  throwIfOffscreenJobAborted(messageId);
  const module = await withTimeout(self.createFFmpegCore({
    locateFile: (path) => {
      if (path.endsWith('.wasm')) return chrome.runtime.getURL('assets/lib/ffmpeg-core.wasm');
      if (path.endsWith('.worker.js')) return chrome.runtime.getURL('assets/lib/ffmpeg-core.worker.js');
      return chrome.runtime.getURL(`assets/lib/${path}`);
    },
    print: (msg) => sendOffscreenLog(msg, 'info', messageId),
    printErr: (msg) => sendOffscreenLog(msg, 'warn', messageId)
  }), 120000, 'Bare FFmpeg core load timed out');

  let userLogger = null;
  let userProgress = null;
  let lastRunLogs = [];
  const MAX_CAPTURED_LOGS = 400;

  const relayModuleLog = (entry) => {
    if (entry?.message) {
      lastRunLogs.push(entry);
      if (lastRunLogs.length > MAX_CAPTURED_LOGS) {
        lastRunLogs.shift();
      }
    }
    if (typeof userLogger === 'function') {
      try {
        userLogger(entry);
      } catch (_) { /* ignore logger failures */ }
    }
  };

  if (typeof module.setLogger === 'function') {
    module.setLogger(relayModuleLog);
  }
  if (typeof module.setProgress === 'function') {
    module.setProgress((entry) => {
      if (typeof userProgress === 'function') {
        try {
          userProgress(entry);
        } catch (_) { /* ignore progress failures */ }
      }
    });
  }

  const buildRunError = (ret, fallbackLabel) => {
    const stderrLines = lastRunLogs
      .filter((entry) => String(entry?.type || '').toLowerCase().includes('stderr') && entry?.message)
      .map((entry) => String(entry.message || '').trim())
      .filter(Boolean);
    const classified = classifyOffscreenFfmpegError(
      stderrLines.slice(-12).join('\n'),
      `${fallbackLabel} exited with code ${ret}`
    );
    const message = classified.summary || `${fallbackLabel} exited with code ${ret}`;
    const err = new Error(message);
    err.code = ret;
    err.ffmpegCategory = classified.category;
    err.ffmpegLogs = lastRunLogs.slice();
    return err;
  };

  const ffmpeg = {
    FS: (cmd, ...args) => {
      const target = module.FS || module;
      const fn = target?.[cmd];
      if (typeof fn === 'function') return fn.apply(target, args);
      if (typeof target.FS === 'function') return target.FS(cmd, ...args);
      throw new Error(`FFmpeg FS command unavailable: ${cmd}`);
    },
    mount: (fsType, options = {}, mountPoint) => {
      const target = module.FS || module;
      const mountImpl = typeof fsType === 'string'
        ? (module[fsType] || target?.[fsType] || target?.filesystems?.[fsType])
        : fsType;
      if (!mountImpl || typeof target?.mount !== 'function') {
        throw new Error(`FFmpeg mount unavailable for fs type: ${fsType}`);
      }
      return target.mount(mountImpl, options, mountPoint);
    },
    unmount: (mountPoint) => {
      const target = module.FS || module;
      if (typeof target?.unmount !== 'function') {
        throw new Error('FFmpeg unmount unavailable');
      }
      return target.unmount(mountPoint);
    },
    setLogger: (logger) => {
      userLogger = typeof logger === 'function' ? logger : null;
    },
    setProgress: (handler) => {
      userProgress = typeof handler === 'function' ? handler : null;
    },
    setLogLevel: () => { /* bare core does not expose log levels */ },
    reset: () => {
      if (typeof module.reset === 'function') {
        module.reset();
      }
    },
    run: async (...args) => {
      const rawArgv = Array.isArray(args[0]) ? args[0] : args;
      const argv = prependDefaultFfmpegArgs(rawArgv);
      lastRunLogs = [];
      if (typeof module.reset === 'function') {
        module.reset();
      }
      if (typeof module.exec === 'function') {
        const ret = module.exec(...argv);
        if (typeof ret === 'number' && ret !== 0) {
          throw buildRunError(ret, 'FFmpeg');
        }
      } else if (typeof module.callMain === 'function') {
        const ret = module.callMain(argv);
        if (typeof ret === 'number' && ret !== 0) {
          throw buildRunError(ret, 'FFmpeg');
        }
      } else {
        throw new Error('FFmpeg bare core has no exec or callMain entry point and cannot run commands');
      }
    },
    ffprobe: async (...args) => {
      const argv = Array.isArray(args[0]) ? args[0] : args;
      lastRunLogs = [];
      if (typeof module.reset === 'function') {
        module.reset();
      }
      if (typeof module.ffprobe === 'function') {
        const ret = module.ffprobe(...argv);
        if (typeof ret === 'number' && ret !== 0) {
          throw buildRunError(ret, 'FFprobe');
        }
        return ret;
      }
      throw new Error('FFmpeg bare core has no ffprobe entry point');
    }
  };

  _bareFfmpegModule = module;
  _ffmpegInstance = ffmpeg;
  _ffmpegMode = 'single-thread-direct';
  sendOffscreenLog('Bare FFmpeg core ready (single-thread, no worker)', 'info', messageId);
  return ffmpeg;
}

async function getFFmpeg(messageId) {
  if (_ffmpegInstance) {
    sendOffscreenLog(`FFmpeg already loaded (${_ffmpegMode})`, 'info', messageId);
    return _ffmpegInstance;
  }
  if (_ffmpegLoadPromise) {
    return _ffmpegLoadPromise;
  }

  const sabAvailable = typeof SharedArrayBuffer !== 'undefined';
  const coi = self.crossOriginIsolated;
  sendOffscreenLog(`FFmpeg loading... (SAB:${sabAvailable ? 'yes' : 'no'}, COI:${coi === false ? 'no' : 'yes'})`, 'info', messageId);
  sendOffscreenLog(
    'Using direct FFmpeg core in the offscreen page.',
    'info',
    messageId
  );
  _ffmpegLoadPromise = (async () => {
    const ffmpeg = await loadBareFfmpegCore(messageId);
    _ffmpegInstance = ffmpeg;
    return ffmpeg;
  })();
  try {
    return await _ffmpegLoadPromise;
  } finally {
    _ffmpegLoadPromise = null;
  }
}

function formatWorkerBootstrapError(event, label = 'direct') {
  const base = event?.message || event?.error?.message || 'Failed to fetch';
  const file = event?.filename ? ` @ ${event.filename}` : '';
  const line = Number.isFinite(event?.lineno) ? `:${event.lineno}` : '';
  const col = Number.isFinite(event?.colno) ? `:${event.colno}` : '';
  return `Demux worker bootstrap (${label}) failed: ${base}${file}${line}${col}`;
}

function createDemuxWorkerAttempt(workerUrl, mode = 'direct') {
  try {
    return {
      mode,
      worker: new Worker(workerUrl, { name: 'ffmpeg-demux-worker' }),
      revoke: () => {}
    };
  } catch (err) {
    throw new Error(`Failed to create demux worker (${mode}): ${err?.message || err}`);
  }
}

async function bootDemuxWorker(workerUrl, messageId) {
  const attempts = ['direct'];
  let lastError = null;

  for (const mode of attempts) {
    let attempt = null;
    try {
      attempt = createDemuxWorkerAttempt(workerUrl, mode);
      const worker = attempt.worker;
      await new Promise((resolve, reject) => {
        let settled = false;
        const timeoutId = setTimeout(() => {
          if (settled) return;
          settled = true;
          reject(new Error(`Demux worker bootstrap (${mode}) timed out before signaling readiness.`));
        }, 5000);

        const cleanup = () => {
          clearTimeout(timeoutId);
          worker.onmessage = null;
          worker.onerror = null;
        };

        worker.onmessage = (event) => {
          const data = event?.data || {};
          if (data.type !== 'BOOT') {
            return;
          }
          if (settled) return;
          settled = true;
          cleanup();
          resolve();
        };

        worker.onerror = (event) => {
          if (settled) return;
          settled = true;
          cleanup();
          reject(new Error(formatWorkerBootstrapError(event, mode)));
        };
      });

      sendOffscreenLog(`Dedicated demux worker bootstrapped (${mode}).`, 'info', messageId);
      return attempt;
    } catch (err) {
      lastError = err;
      try { attempt?.worker?.terminate?.(); } catch (_) { /* ignore */ }
      try { attempt?.revoke?.(); } catch (_) { /* ignore */ }
      sendOffscreenLog(`Direct demux worker bootstrap failed (${err?.message || err})`, 'warn', messageId);
    }
  }

  throw lastError || new Error('Unable to bootstrap demux worker');
}

async function runDemuxInWorker(source, messageId, opts = {}) {
  if (!isOpfsTempInputSource(source)) {
    throw new Error('Demux worker requires an OPFS temp-file source');
  }
  const tempName = String(source.opfsTempName || '').trim();
  if (!tempName) {
    throw new Error('Missing OPFS temp file name for demux worker');
  }

  const root = await navigator.storage.getDirectory();
  const fileHandle = await root.getFileHandle(tempName, { create: false });
  const file = await fileHandle.getFile();
  const workerUrl = chrome.runtime.getURL('pages/offscreen/ffmpeg-demux-worker.js');

  return await new Promise((resolve, reject) => {
    let settled = false;
    let worker = null;
    let revokeWorker = () => {};

    const finish = (fn, value, terminateWorker = true) => {
      if (settled) return;
      settled = true;
      if (_activeDemuxWorkers.get(messageId)?.worker === worker) {
        _activeDemuxWorkers.delete(messageId);
      }
      if (worker) {
        worker.onmessage = null;
        worker.onerror = null;
      }
      if (terminateWorker && worker) {
        try { worker.terminate(); } catch (_) { /* ignore */ }
      }
      try { revokeWorker(); } catch (_) { /* ignore */ }
      fn(value);
    };

    (async () => {
      try {
        const booted = await bootDemuxWorker(workerUrl, messageId);
        worker = booted.worker;
        revokeWorker = typeof booted.revoke === 'function' ? booted.revoke : (() => {});

        _activeDemuxWorkers.set(messageId, {
          worker,
          reject: (err) => finish(reject, err, true)
        });

        worker.onmessage = (event) => {
          const data = event?.data || {};
          if (data.type === 'LOG') {
            sendOffscreenLog(data.message || '', data.level || 'info', messageId);
            return;
          }
          if (data.type === 'RESULT') {
            finish(resolve, data.result || {}, true);
            return;
          }
          if (data.type === 'ERROR') {
            finish(reject, new Error(data.error || 'Demux worker failed'), true);
          }
        };

        worker.onerror = (event) => {
          finish(reject, new Error(formatWorkerBootstrapError(event, 'runtime')), true);
        };

        worker.postMessage({
          type: 'START',
          coreUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.js'),
          wasmUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.wasm'),
          coreWorkerUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.worker.js'),
          messageId,
          source: {
            kind: 'file',
            file,
            byteLength: Number(source?.byteLength) || file.size || 0
          },
          streamPlans: Array.isArray(opts.streamPlans) ? opts.streamPlans : [],
          textStreamPlans: Array.isArray(opts.textStreamPlans) ? opts.textStreamPlans : [],
          inputArgs: Array.isArray(opts.inputArgs) ? opts.inputArgs : [],
          skipFlatCueRepair: opts.skipFlatCueRepair === true,
          skipCopyTracks: opts.skipCopyTracks === true
        });
      } catch (err) {
        finish(reject, err, true);
      }
    })();
  });
}

async function runAudioDecodeInWorker(source, windows, messageId, opts = {}) {
  if (!isOpfsTempInputSource(source)) {
    throw new Error('Audio decode worker requires an OPFS temp-file source');
  }
  const tempName = String(source.opfsTempName || '').trim();
  if (!tempName) {
    throw new Error('Missing OPFS temp file name for audio decode worker');
  }

  const root = await navigator.storage.getDirectory();
  const fileHandle = await root.getFileHandle(tempName, { create: false });
  const file = await fileHandle.getFile();
  const workerUrl = chrome.runtime.getURL('pages/offscreen/ffmpeg-demux-worker.js');

  return await new Promise((resolve, reject) => {
    let settled = false;
    let worker = null;
    let revokeWorker = () => {};

    const finish = (fn, value, terminateWorker = true) => {
      if (settled) return;
      settled = true;
      if (_activeDemuxWorkers.get(messageId)?.worker === worker) {
        _activeDemuxWorkers.delete(messageId);
      }
      if (worker) {
        worker.onmessage = null;
        worker.onerror = null;
      }
      if (terminateWorker && worker) {
        try { worker.terminate(); } catch (_) { /* ignore */ }
      }
      try { revokeWorker(); } catch (_) { /* ignore */ }
      fn(value);
    };

    (async () => {
      try {
        const booted = await bootDemuxWorker(workerUrl, messageId);
        worker = booted.worker;
        revokeWorker = typeof booted.revoke === 'function' ? booted.revoke : (() => {});

        _activeDemuxWorkers.set(messageId, {
          worker,
          reject: (err) => finish(reject, err, true)
        });

        worker.onmessage = (event) => {
          const data = event?.data || {};
          if (data.type === 'LOG') {
            sendOffscreenLog(data.message || '', data.level || 'info', messageId);
            return;
          }
          if (data.type === 'RESULT') {
            finish(resolve, data.result || {}, true);
            return;
          }
          if (data.type === 'ERROR') {
            finish(reject, new Error(data.error || 'Audio decode worker failed'), true);
          }
        };

        worker.onerror = (event) => {
          finish(reject, new Error(formatWorkerBootstrapError(event, 'runtime')), true);
        };

        worker.postMessage({
          type: 'START',
          action: 'audio-decode',
          coreUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.js'),
          wasmUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.wasm'),
          coreWorkerUrl: chrome.runtime.getURL('assets/lib/ffmpeg-core.worker.js'),
          messageId,
          audioStreamIndex: Number.isInteger(opts?.audioStreamIndex) ? opts.audioStreamIndex : 0,
          source: {
            kind: 'file',
            file,
            byteLength: Number(source?.byteLength) || file.size || 0
          },
          windows: (windows || []).map((win) => ({
            startSec: win?.startSec,
            durSec: win?.durSec,
            seekToSec: win?.seekToSec
          }))
        });
      } catch (err) {
        finish(reject, err, true);
      }
    })();
  });
}

async function runOcrOnBinaryCopiedTracks(copyTracks, messageId) {
  if (!Array.isArray(copyTracks) || !copyTracks.length) {
    return [];
  }
  throwImageSubtitleOcrNotImplemented(messageId, copyTracks.length);
}

async function decodeAudioWindows(windows, mode, messageId, opts = {}) {
  const sharedBuffer = windows.length > 1 && windows.every(w => w.buffer === windows[0].buffer);
  const sharedOpfsSource = windows.length >= 1
    && windows.every((w) => w.buffer === windows[0].buffer)
    && isOpfsTempInputSource(windows[0]?.buffer)
    ? windows[0].buffer
    : null;
  let sharedInputSource = null;
  const audioStreamIndex = Number.isInteger(opts.audioStreamIndex) ? opts.audioStreamIndex : 0;
  sendOffscreenLog(`Audio decode mapping: 0:a:${audioStreamIndex}`, 'info', messageId);

  if (sharedOpfsSource) {
    try {
      sendOffscreenLog('Dispatching shared OPFS audio decode to dedicated FFmpeg worker.', 'info', messageId);
      const workerResult = await runAudioDecodeInWorker(sharedOpfsSource, windows, messageId, { audioStreamIndex });
      const audioWindows = Array.isArray(workerResult?.audioWindows) ? workerResult.audioWindows : [];
      if (audioWindows.length) {
        sendOffscreenLog(`Dedicated audio worker decoded ${audioWindows.length} window(s).`, 'info', messageId);
        return audioWindows.map((win) => ({
          audioBytes: win?.audioBytes instanceof Uint8Array
            ? win.audioBytes
            : new Uint8Array(win?.audioBytes || []),
          startMs: Math.round(win?.startMs || 0)
        }));
      }
      throw new Error('Dedicated audio worker returned no windows');
    } catch (workerErr) {
      const sourceBytes = Number(sharedOpfsSource?.byteLength) || Number(sharedOpfsSource?.totalBytes) || 0;
      if (sourceBytes > OPFS_STAGED_COPY_MAX_BYTES) {
        throw workerErr;
      }
      sendOffscreenLog(`Dedicated audio worker failed; falling back to direct offscreen core (${workerErr?.message || workerErr})`, 'warn', messageId);
    }
  }

  const ffmpeg = await getFFmpeg(messageId);
  const results = [];

  for (let i = 0; i < windows.length; i++) {
    const win = windows[i];
    const outputName = `win_${i}.wav`;
    let inputSource = sharedInputSource;
    const buildArgs = () => {
      const inputName = inputSource?.inputName || `win_${i}.bin`;
      const base = ['-i', inputName, '-vn'];
      if (Number.isInteger(audioStreamIndex) && audioStreamIndex >= 0) {
        base.push('-map', `0:a:${audioStreamIndex}`);
      }
      base.push('-acodec', 'pcm_s16le', '-ar', '16000');
      // Standard mono downmix is more robust across stereo layouts than forcing left only.
      base.push('-ac', '1');
      const args = [...base];
      if (typeof win.durSec === 'number' && win.durSec > 0) {
        args.push('-t', String(win.durSec));
      }
      args.push(outputName);
      if (typeof win.seekToSec === 'number' && win.seekToSec > 0) {
        args.unshift('-ss', String(win.seekToSec));
      }
      return args;
    };

    try {
      if (!inputSource) {
        inputSource = await buildDemuxInputSource(ffmpeg, win.buffer, messageId);
        if (sharedBuffer) {
          sharedInputSource = inputSource;
        }
      }
      const args = buildArgs();
      await ffmpeg.run(...args);
      const data = ffmpeg.FS('readFile', outputName);
      if (!data?.byteLength) {
        throw new Error(`FFmpeg produced empty audio for window ${i + 1}`);
      }
      if (data.byteLength < 44) {
        throw new Error(`FFmpeg produced too-small audio for window ${i + 1} (${data.byteLength} bytes)`);
      }
      results.push({
        audioBytes: data,
        startMs: Math.round(((win.startSec ?? win.seekToSec ?? 0) || 0) * 1000)
      });
    } catch (err) {
      const msg = err?.message || String(err);
      const sourceBytes = typeof win?.buffer?.byteLength === 'number'
        ? win.buffer.byteLength
        : (typeof win?.buffer?.totalBytes === 'number' ? win.buffer.totalBytes : 0);
      throw new Error(
        `FFmpeg decode failed at window ${i + 1}/${windows.length} (start=${win?.startSec ?? 'n/a'}s seek=${win?.seekToSec ?? 0}s dur=${win?.durSec ?? 'n/a'}s bytes=${sourceBytes || 0}): ${msg}`
      );
    } finally {
      try { ffmpeg.FS('unlink', outputName); } catch (_) { /* ignore */ }
      if (!sharedBuffer && inputSource?.cleanup) {
        try { inputSource.cleanup(); } catch (_) { /* ignore */ }
      }
    }
  }

  if (sharedInputSource?.cleanup) {
    try { sharedInputSource.cleanup(); } catch (_) { /* ignore */ }
  }

  if (!results.length) {
    throw new Error('FFmpeg could not decode any audio window');
  }

  return results;
}

function cleanupFsFile(ffmpeg, file) {
  if (!file) return;
  try {
    ffmpeg.FS('unlink', file);
  } catch (_) { /* ignore */ }
}

function readFsFileIfPresent(ffmpeg, file) {
  if (!file) return null;
  try {
    return ffmpeg.FS('readFile', file);
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

function recoverPartialFfmpegOutput(ffmpeg, file, err, messageId, label) {
  const data = readFsFileIfPresent(ffmpeg, file);
  if (!data?.byteLength || !shouldKeepPartialFfmpegOutput(err?.message || err)) {
    cleanupFsFile(ffmpeg, file);
    return false;
  }
  const sizeKb = Math.max(1, Math.round(data.byteLength / 1024));
  sendOffscreenLog(`${label} kept ${sizeKb} KB of partial output after FFmpeg reported a truncated input.`, 'warn', messageId);
  return true;
}

function ensureFsDirectory(ffmpeg, dir) {
  if (!dir || dir === '/') return;
  try {
    ffmpeg.FS('mkdir', dir);
  } catch (err) {
    const msg = String(err?.message || err || '');
    if (!/File exists|ErrnoError/i.test(msg)) {
      throw err;
    }
  }
}

function cleanupFsDirectory(ffmpeg, dir) {
  if (!dir || dir === '/') return;
  try {
    ffmpeg.FS('rmdir', dir);
  } catch (_) { /* ignore */ }
}

const OPFS_DEMUX_HEADER_BYTES = 96 * 1024 * 1024;
const OPFS_INPUT_STREAM_CHUNK_BYTES = 8 * 1024 * 1024;
const OPFS_STAGED_COPY_MAX_BYTES = 1536 * 1024 * 1024;

function isOpfsTempInputSource(source) {
  return !!(source && typeof source === 'object' && typeof source.opfsTempName === 'string' && source.opfsTempName.trim());
}

async function buildDemuxInputSource(ffmpeg, source, messageId) {
  if (isOpfsTempInputSource(source)) {
    const tempName = String(source.opfsTempName || '').trim();
    let file;
    try {
      const root = await navigator.storage.getDirectory();
      const fileHandle = await root.getFileHandle(tempName);
      file = await fileHandle.getFile();
    } catch (err) {
      throw new Error(`Failed to open OPFS temp file ${tempName}: ${err?.message || err}`);
    }

    const byteLength = Number(source?.byteLength) || file?.size || 0;
    if (!byteLength) {
      throw new Error(`OPFS temp file ${tempName} is empty.`);
    }

    let headerView = new Uint8Array();
    const headerBytes = Math.min(byteLength, OPFS_DEMUX_HEADER_BYTES);
    if (headerBytes > 0) {
      try {
        headerView = new Uint8Array(await file.slice(0, headerBytes).arrayBuffer());
      } catch (err) {
        throw new Error(`Failed to read OPFS header sample ${tempName}: ${err?.message || err}`);
      }
    }

    if (typeof ffmpeg?.mount === 'function' && typeof ffmpeg?.unmount === 'function' && typeof FileReaderSync === 'function') {
      const mountPoint = `/opfs_input_${Date.now()}_${Math.random().toString(16).slice(2, 8)}`;
      const mountedName = `${mountPoint}/${file.name || 'embedded_input.bin'}`;
      try {
        ensureFsDirectory(ffmpeg, mountPoint);
        ffmpeg.mount('WORKERFS', { files: [file] }, mountPoint);
        sendOffscreenLog('Mounted OPFS temp file via WORKERFS.', 'info', messageId);
        return {
          byteLength,
          headerView,
          inputName: mountedName,
          cleanup: () => {
            try { ffmpeg.unmount(mountPoint); } catch (_) { /* ignore */ }
            cleanupFsDirectory(ffmpeg, mountPoint);
          }
        };
      } catch (err) {
        try { ffmpeg.unmount(mountPoint); } catch (_) { /* ignore */ }
        cleanupFsDirectory(ffmpeg, mountPoint);
        sendOffscreenLog(`WORKERFS mount failed; falling back to staged copy (${err?.message || err})`, 'warn', messageId);
      }
    }

    const inputName = 'embedded_input.bin';
    cleanupFsFile(ffmpeg, inputName);
    let stream = null;
    let writtenBytes = 0;
    let nextLoggedPct = 25;

    const logProgress = () => {
      if (!byteLength) return;
      const pct = Math.min(100, Math.floor((writtenBytes / byteLength) * 100));
      while (nextLoggedPct <= 100 && pct >= nextLoggedPct) {
        sendOffscreenLog(`Streaming full file into FFmpeg FS... ${nextLoggedPct}%`, 'info', messageId);
        nextLoggedPct += 25;
      }
    };

    try {
      if (byteLength > OPFS_STAGED_COPY_MAX_BYTES) {
        const sizeMb = Math.round((byteLength / (1024 * 1024)) * 10) / 10;
        const limitMb = Math.round((OPFS_STAGED_COPY_MAX_BYTES / (1024 * 1024)) * 10) / 10;
        throw new Error(`OPFS temp file is too large for staged FFmpeg FS copy in the offscreen page (~${sizeMb} MB > ${limitMb} MB).`);
      }
      sendOffscreenLog(`Streaming OPFS temp file into FFmpeg FS (~${Math.round((byteLength / (1024 * 1024)) * 10) / 10} MB)...`, 'info', messageId);
      stream = ffmpeg.FS('open', inputName, 'w+');
      if (!stream) {
        throw new Error('FFmpeg FS could not open the input file for writing.');
      }

      if (typeof file.stream === 'function') {
        const reader = file.stream().getReader();
        while (true) {
          throwIfOffscreenJobAborted(messageId);
          const { done, value } = await reader.read();
          if (done) break;
          const chunk = value instanceof Uint8Array ? value : new Uint8Array(value || []);
          if (!chunk.byteLength) continue;
          const wrote = ffmpeg.FS('write', stream, chunk, 0, chunk.byteLength, writtenBytes);
          writtenBytes += (typeof wrote === 'number' && wrote > 0) ? wrote : chunk.byteLength;
          logProgress();
        }
      } else {
        while (writtenBytes < byteLength) {
          throwIfOffscreenJobAborted(messageId);
          const end = Math.min(byteLength, writtenBytes + OPFS_INPUT_STREAM_CHUNK_BYTES);
          const chunk = new Uint8Array(await file.slice(writtenBytes, end).arrayBuffer());
          if (!chunk.byteLength) break;
          const wrote = ffmpeg.FS('write', stream, chunk, 0, chunk.byteLength, writtenBytes);
          writtenBytes += (typeof wrote === 'number' && wrote > 0) ? wrote : chunk.byteLength;
          logProgress();
        }
      }

      if (!writtenBytes) {
        throw new Error('No bytes were copied from the OPFS temp file.');
      }
      if (writtenBytes < byteLength) {
        sendOffscreenLog(`OPFS input copy stopped early (${writtenBytes}/${byteLength} bytes)`, 'warn', messageId);
      }

      ffmpeg.FS('close', stream);
      stream = null;

      return {
        byteLength,
        headerView,
        inputName,
        cleanup: () => cleanupFsFile(ffmpeg, inputName)
      };
    } catch (err) {
      try { ffmpeg.FS('close', stream); } catch (_) { /* ignore */ }
      cleanupFsFile(ffmpeg, inputName);
      throw new Error(`Failed to stream OPFS temp file into FFmpeg FS: ${err?.message || err}`);
    }
  }

  const byteLength = typeof source?.byteLength === 'number'
    ? source.byteLength
    : (typeof source?.size === 'number' ? source.size : 0);
  if (!source || !byteLength) {
    throw new Error('Empty buffer received for demux.');
  }
  const headerView = source instanceof Uint8Array ? source : new Uint8Array(source);
  const inputName = 'embedded_input.bin';
  sendOffscreenLog('Writing input buffer to FFmpeg FS...', 'info', messageId);
  ffmpeg.FS('writeFile', inputName, headerView);
  return {
    byteLength,
    headerView,
    inputName,
    cleanup: () => cleanupFsFile(ffmpeg, inputName)
  };
}

async function loadDemuxHeaderView(source) {
  if (isOpfsTempInputSource(source)) {
    const byteLength = typeof source?.byteLength === 'number'
      ? source.byteLength
      : 0;
    if (!byteLength) return new Uint8Array(0);
    const root = await navigator.storage.getDirectory();
    const fileHandle = await root.getFileHandle(String(source.opfsTempName || '').trim(), { create: false });
    const file = await fileHandle.getFile();
    const headerBytes = Math.min(byteLength, OPFS_DEMUX_HEADER_BYTES);
    return headerBytes > 0
      ? new Uint8Array(await file.slice(0, headerBytes).arrayBuffer())
      : new Uint8Array(0);
  }
  if (source instanceof Uint8Array) return source;
  if (source instanceof ArrayBuffer) return new Uint8Array(source);
  if (ArrayBuffer.isView(source)) {
    return source.byteOffset === 0 && source.byteLength === source.buffer.byteLength
      ? new Uint8Array(source.buffer)
      : new Uint8Array(source.buffer.slice(source.byteOffset, source.byteOffset + source.byteLength));
  }
  return new Uint8Array(0);
}

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

async function extractSubtitleCopyTracks(ffmpeg, inputName, messageId, opts = {}) {
  const copiedTracks = [];
  const targets = getSubtitleExtractionTargets(opts);
  for (const target of targets) {
    throwIfOffscreenJobAborted(messageId);
    const streamIndex = target.streamIndex;
    const outputIndex = target.outputIndex;
    const outName = formatExtractedName(outputIndex, 'mkv');
    cleanupFsFile(ffmpeg, outName);
    try {
      await ffmpeg.run(
        '-y',
        '-analyzeduration', '60M',
        '-probesize', '60M',
        '-i', inputName,
        '-map', `0:s:${streamIndex}`,
        '-c:s', 'copy',
        outName
      );
      const data = ffmpeg.FS('readFile', outName);
      if (data?.byteLength > 0) {
        copiedTracks.push(outName);
        continue;
      }
      cleanupFsFile(ffmpeg, outName);
      break;
    } catch (err) {
      if (isNoSubtitleStreamErrorMessage(err?.message || err)) {
        cleanupFsFile(ffmpeg, outName);
        break;
      }
      if (recoverPartialFfmpegOutput(ffmpeg, outName, err, messageId, `Subtitle copy for stream ${streamIndex + 1}`)) {
        copiedTracks.push(outName);
        continue;
      }
      sendOffscreenLog(`Subtitle copy failed for stream ${streamIndex + 1}: ${err?.message || err}`, 'warn', messageId);
    }
  }
  return copiedTracks;
}

async function extractSubtitleTextTracks(ffmpeg, inputName, messageId, opts = {}) {
  const variant = opts.variant || '';
  const extracted = [];
  const targets = getSubtitleExtractionTargets(opts);
  const outputArgs = Array.isArray(opts.outputArgs) ? opts.outputArgs : [];
  const inputArgs = Array.isArray(opts.inputArgs) ? opts.inputArgs : [];
  let skippedKindMismatches = 0;
  for (const target of targets) {
    throwIfOffscreenJobAborted(messageId);
    const streamIndex = target.streamIndex;
    const outputIndex = target.outputIndex;
    const outputPlan = resolveTextSubtitleOutputPlan(target);
    const outName = formatExtractedName(outputIndex, outputPlan.ext, variant);
    cleanupFsFile(ffmpeg, outName);
    try {
      await ffmpeg.run(
        '-y',
        ...inputArgs,
        '-i', inputName,
        '-map', `0:s:${streamIndex}`,
        '-c:s', outputPlan.ffmpegCodec,
        ...outputArgs,
        outName
      );
      const data = ffmpeg.FS('readFile', outName);
      if (data?.byteLength > 0) {
        extracted.push(outName);
      } else {
        cleanupFsFile(ffmpeg, outName);
      }
    } catch (err) {
      if (isNoSubtitleStreamErrorMessage(err?.message || err)) {
        cleanupFsFile(ffmpeg, outName);
        break;
      }
      if (recoverPartialFfmpegOutput(ffmpeg, outName, err, messageId, `Text subtitle conversion for stream ${streamIndex + 1}`)) {
        extracted.push(outName);
        continue;
      }
      const classified = classifyOffscreenFfmpegError(err?.message || err, 'FFmpeg failed to convert the subtitle stream to text output.');
      if (classified.category === 'subtitle-kind-mismatch') {
        skippedKindMismatches += 1;
        continue;
      }
      sendOffscreenLog(`Text subtitle conversion failed for stream ${streamIndex + 1}: ${classified.summary}`, 'warn', messageId);
    }
  }
  if (skippedKindMismatches > 0) {
    sendOffscreenLog(
      `Skipped direct text extraction for ${skippedKindMismatches} stream(s) that FFmpeg reported as non-text/bitmap mismatches.`,
      'info',
      messageId
    );
  }
  return extracted;
}

function readExistingExtractedTextOutputs(ffmpeg, outputs) {
  const extracted = [];
  for (const output of outputs || []) {
    if (!output?.outName) {
      continue;
    }
    try {
      const data = ffmpeg.FS('readFile', output.outName);
      if (data?.byteLength > 0) {
        extracted.push(output.outName);
        continue;
      }
    } catch (_) { /* ignore */ }
    cleanupFsFile(ffmpeg, output.outName);
  }
  return extracted;
}

async function extractSubtitleTextTracksBatch(ffmpeg, inputName, messageId, opts = {}) {
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
    cleanupFsFile(ffmpeg, output.outName);
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
    await ffmpeg.run(argv);
  } catch (err) {
    const classified = classifyOffscreenFfmpegError(err?.message || err, 'FFmpeg batch text extraction failed.');
    const retryReason = classified.category === 'subtitle-kind-mismatch'
      ? 'FFmpeg hit one or more streams that cannot be converted directly to text output.'
      : classified.summary;
    sendOffscreenLog(`Batch text extraction failed; retrying streams individually (${retryReason})`, 'warn', messageId);
    return await extractSubtitleTextTracks(ffmpeg, inputName, messageId, opts);
  }

  const extracted = readExistingExtractedTextOutputs(ffmpeg, outputs);
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
    sendOffscreenLog(
      `Batch text extraction produced ${extracted.length}/${outputs.length} output(s); retrying ${missingTargets.length} missing stream(s) individually...`,
      'warn',
      messageId
    );
    const recovered = await extractSubtitleTextTracks(ffmpeg, inputName, messageId, {
      ...opts,
      streamPlans: missingTargets
    });
    return [...extracted, ...recovered].sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
  }

  return extracted.sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
}

async function demuxSubtitles(source, messageId, opts = {}) {
  if (!isOpfsTempInputSource(source)) {
    return await demuxSubtitlesDirect(source, messageId, opts);
  }

  const byteLength = typeof source?.byteLength === 'number'
    ? source.byteLength
    : (typeof source?.size === 'number' ? source.size : 0);
  const sizeMb = Math.round(((byteLength || 0) / (1024 * 1024)) * 10) / 10;
  const sourceLabel = isOpfsTempInputSource(source) ? 'OPFS temp file' : 'buffer';
  sendOffscreenLog(`Starting demux (${sourceLabel} ~${sizeMb} MB)`, 'info', messageId);
  if (!source || !byteLength) {
    sendOffscreenLog('Received empty input for demux; aborting.', 'error', messageId);
    throw new Error('Empty buffer received for demux.');
  }

  const headerView = await loadDemuxHeaderView(source);
  const mkvProbe = probeMkvSubtitleMetadata(headerView);
  const subtitlePlan = buildMkvSubtitleExtractionPlan(mkvProbe);
  const plannedTextStreams = subtitlePlan.filter((entry) => entry.kind === 'text');
  const plannedBitmapStreams = subtitlePlan.filter((entry) => entry.kind !== 'text');
  if (mkvProbe) {
    const scanMb = Math.round((mkvProbe.scanBytes / (1024 * 1024)) * 10) / 10;
    const summaryBits = [
      `tracks=${mkvProbe.tracks.length}`,
      `subtitleTracks=${mkvProbe.subtitleTracks.length}`,
      `subtitleAttachments=${mkvProbe.subtitleAttachments.length}`
    ];
    sendOffscreenLog(`MKV header probe (${scanMb} MB scan): ${summaryBits.join(', ')}`, 'info', messageId);
    const trackSummary = mkvProbe.tracks
      .slice(0, 8)
      .map(formatMkvTrackProbe)
      .filter(Boolean)
      .join(' | ');
    if (trackSummary) {
      sendOffscreenLog(`MKV track entries: ${trackSummary}`, 'info', messageId);
    }
    if (subtitlePlan.length) {
      sendOffscreenLog(
        `MKV subtitle plan: ${plannedTextStreams.length} text, ${plannedBitmapStreams.length} bitmap/unknown`,
        'info',
        messageId
      );
    }
  }

  if (plannedBitmapStreams.length && !plannedTextStreams.length) {
    throwImageSubtitleOcrNotImplemented(messageId, plannedBitmapStreams.length);
  }

  try {
    sendOffscreenLog('Dispatching OPFS demux to a dedicated FFmpeg worker for mounted-file access...', 'info', messageId);
    const workerResult = await runDemuxInWorker(source, messageId, {
      streamPlans: Array.isArray(opts.streamPlans) && opts.streamPlans.length ? opts.streamPlans : subtitlePlan,
      textStreamPlans: Array.isArray(opts.textStreamPlans) && opts.textStreamPlans.length ? opts.textStreamPlans : plannedTextStreams,
      inputArgs: Array.isArray(opts.inputArgs) ? opts.inputArgs : [],
      skipFlatCueRepair: opts.skipFlatCueRepair === true,
      skipCopyTracks: opts.skipCopyTracks === true
    });
    let tracks = Array.isArray(workerResult?.textTracks) ? workerResult.textTracks : [];
    const copyTracks = Array.isArray(workerResult?.copyTracks) ? workerResult.copyTracks : [];

    if (!tracks.length) {
      if (copyTracks.length) {
        if (plannedTextStreams.length) {
          sendOffscreenLog(
            `Detected ${plannedTextStreams.length} text subtitle stream(s) in the container, but FFmpeg produced no usable text output. Skipping OCR because this is not a bitmap-only stream.`,
            'error',
            messageId
          );
          throw new Error('Text subtitle streams were detected, but FFmpeg could not extract them.');
        }
        await runOcrOnBinaryCopiedTracks(copyTracks, messageId);
      } else {
        const advertisedSubtitles = (mkvProbe?.subtitleTracks?.length || 0) + (mkvProbe?.subtitleAttachments?.length || 0);
        if (!advertisedSubtitles) {
          sendOffscreenLog('FFmpeg found no subtitle streams and the MKV header probe found none.', 'warn', messageId);
          throw new Error('No subtitle streams found in media.');
        }
        sendOffscreenLog(`No extracted text tracks were produced, but the MKV header probe advertised ${advertisedSubtitles} subtitle item(s). The current buffer likely does not contain enough subtitle packets yet.`, 'warn', messageId);
        throw new Error('Subtitle tracks were advertised in the MKV header, but no extractable subtitle packets were present in the current buffer.');
      }
    }

    const headerLangs = collectSubtitleLanguagesFromHeader(headerView);
    if (headerLangs.length) {
      tracks = applyHeaderLanguagesToTracks(tracks, headerLangs);
    }
    tracks = applyContentLanguageGuesses(tracks);
    tracks = normalizeExtractedTracks(tracks);

    const skippedCopies = Number.isFinite(workerResult?.skippedCopies)
      ? workerResult.skippedCopies
      : copyTracks.length;
    const copyNote = skippedCopies ? `; omitted ${skippedCopies} MKV copy track(s) from output` : '';
    sendOffscreenLog(`Demux finished and cleaned up (${tracks.length} track(s)${copyNote})`, 'info', messageId);
    return tracks;
  } catch (workerErr) {
    if (isAbortError(workerErr)) {
      throw workerErr;
    }
    if (byteLength > OPFS_STAGED_COPY_MAX_BYTES) {
      sendOffscreenLog(
        `Mounted OPFS demux worker failed and direct staged-copy fallback is not viable for this file size (${workerErr?.message || workerErr})`,
        'error',
        messageId
      );
      throw workerErr;
    }
    sendOffscreenLog(`Mounted OPFS demux worker failed; falling back to the direct offscreen core (${workerErr?.message || workerErr})`, 'warn', messageId);
    return await demuxSubtitlesDirect(source, messageId, opts);
  }
}

async function demuxSubtitlesDirect(source, messageId, opts = {}) {
  const byteLength = typeof source?.byteLength === 'number'
    ? source.byteLength
    : (typeof source?.size === 'number' ? source.size : 0);
  const sizeMb = Math.round(((byteLength || 0) / (1024 * 1024)) * 10) / 10;
  const sourceLabel = isOpfsTempInputSource(source) ? 'OPFS temp file' : 'buffer';
  sendOffscreenLog(`Starting demux (${sourceLabel} ~${sizeMb} MB)`, 'info', messageId);
  if (!source || !byteLength) {
    sendOffscreenLog('Received empty input for demux; aborting.', 'error', messageId);
    throw new Error('Empty buffer received for demux.');
  }
  const headerView = await loadDemuxHeaderView(source);
  const mkvProbe = probeMkvSubtitleMetadata(headerView);
  const subtitlePlan = buildMkvSubtitleExtractionPlan(mkvProbe);
  const plannedTextStreams = subtitlePlan.filter((entry) => entry.kind === 'text');
  const plannedBitmapStreams = subtitlePlan.filter((entry) => entry.kind !== 'text');
  const inputArgs = Array.isArray(opts.inputArgs) && opts.inputArgs.length
    ? opts.inputArgs
    : ['-analyzeduration', '60M', '-probesize', '60M'];
  if (mkvProbe) {
    const scanMb = Math.round((mkvProbe.scanBytes / (1024 * 1024)) * 10) / 10;
    const summaryBits = [
      `tracks=${mkvProbe.tracks.length}`,
      `subtitleTracks=${mkvProbe.subtitleTracks.length}`,
      `subtitleAttachments=${mkvProbe.subtitleAttachments.length}`
    ];
    sendOffscreenLog(`MKV header probe (${scanMb} MB scan): ${summaryBits.join(', ')}`, 'info', messageId);
    const trackSummary = mkvProbe.tracks
      .slice(0, 8)
      .map(formatMkvTrackProbe)
      .filter(Boolean)
      .join(' | ');
    if (trackSummary) {
      sendOffscreenLog(`MKV track entries: ${trackSummary}`, 'info', messageId);
    }
    if (subtitlePlan.length) {
      sendOffscreenLog(
        `MKV subtitle plan: ${plannedTextStreams.length} text, ${plannedBitmapStreams.length} bitmap/unknown`,
        'info',
        messageId
      );
    }
  }
  if (plannedBitmapStreams.length && !plannedTextStreams.length) {
    throwImageSubtitleOcrNotImplemented(messageId, plannedBitmapStreams.length);
  }
  const ffmpeg = await getFFmpeg(messageId);
  throwIfOffscreenJobAborted(messageId);
  if (ffmpeg?.setLogger) {
    ffmpeg.setLogger(({ type, message }) => {
      const lowerType = String(type || '').toLowerCase();
      const level = (lowerType === 'fferr' || lowerType === 'stderr') ? 'warn' : 'info';
      sendOffscreenLog(message, level, messageId);
    });
  }
  if (ffmpeg?.setLogLevel) {
    ffmpeg.setLogLevel('warning');
  }
  let inputSource = null;
  let inputName = 'embedded_input.bin';
  let copiedTracks = [];
  let files = [];
  const convertedSrts = [];
  try {
    inputSource = await buildDemuxInputSource(ffmpeg, source, messageId);
    inputName = inputSource.inputName;
    try {
      sendOffscreenLog('Running FFmpeg to extract subtitle streams...', 'info', messageId);
      if ((!subtitlePlan.length || plannedBitmapStreams.length) && opts.skipCopyTracks !== true) {
        copiedTracks = await extractSubtitleCopyTracks(ffmpeg, inputName, messageId, {
          ...(plannedBitmapStreams.length ? { streamPlans: plannedBitmapStreams } : {})
        });
      }
      if (plannedTextStreams.length || !subtitlePlan.length) {
        files = await extractSubtitleTextTracksBatch(ffmpeg, inputName, messageId, {
          ...(plannedTextStreams.length ? { streamPlans: plannedTextStreams } : {}),
          inputArgs
        });
      }
      if (copiedTracks.length) {
        sendOffscreenLog(`Preserved ${copiedTracks.length} subtitle stream(s) as MKV copy for bitmap-only detection.`, 'info', messageId);
      }
    } catch (err) {
      const errMsg = err?.message || String(err);
      console.error('[Offscreen] FFmpeg demux failed:', err);
      sendOffscreenLog(`FFmpeg demux failed: ${errMsg}`, 'error', messageId);
      if (
        /^No subtitle streams found in media\.?$/i.test(errMsg)
        || /^Image-based subtitle streams were detected, but OCR extraction is not implemented yet\.?$/i.test(errMsg)
        || /^FFmpeg demux failed:/i.test(errMsg)
        || isAbortError(err)
      ) {
        throw err;
      }
      throw new Error(`FFmpeg demux failed: ${errMsg}`);
    }

  if (!copiedTracks.length && !files.length) {
    if (plannedTextStreams.length) {
      sendOffscreenLog(
        `Detected ${plannedTextStreams.length} text subtitle stream(s) in the container, but FFmpeg could not extract or copy them.`,
        'error',
        messageId
      );
      throw new Error('Text subtitle streams were detected, but FFmpeg could not extract them.');
    }
    const advertisedSubtitles = (mkvProbe?.subtitleTracks?.length || 0) + (mkvProbe?.subtitleAttachments?.length || 0);
    if (!advertisedSubtitles) {
      sendOffscreenLog('FFmpeg found no subtitle streams and the MKV header probe found none.', 'warn', messageId);
      throw new Error('No subtitle streams found in media.');
    }
    sendOffscreenLog(`No extracted text tracks were produced, but the MKV header probe advertised ${advertisedSubtitles} subtitle item(s). The current buffer likely does not contain enough subtitle packets yet.`, 'warn', messageId);
    throw new Error('Subtitle tracks were advertised in the MKV header, but no extractable subtitle packets were present in the current buffer.');
  }

  // Try to convert copied text tracks into their native text container when possible.
  if (copiedTracks.length) {
    const existingIds = new Set(files.map((file) => parseExtractedOutputIndex(file)).filter((value) => Number.isInteger(value) && value > 0));
    let skippedCopyTextConversions = 0;
    for (const copyName of copiedTracks) {
      const trackIdx = parseExtractedOutputIndex(copyName);
      if (trackIdx !== null && existingIds.has(trackIdx)) {
        continue; // already have text output for this track
      }
      const target = findExtractionTargetByOutputIndex(plannedTextStreams, trackIdx);
      const outputPlan = resolveTextSubtitleOutputPlan(target || {});
      const textName = copyName.replace(/\.mkv$/i, `.${outputPlan.ext}`);
      try {
        await ffmpeg.run(
          '-y',
          '-analyzeduration', '60M',
          '-probesize', '60M',
          '-i', copyName,
          '-map', '0:s:0',
          '-c:s', outputPlan.ffmpegCodec,
          textName
        );
        const data = ffmpeg.FS('readFile', textName);
        if (data?.byteLength) {
          convertedSrts.push(textName);
        } else {
          try { ffmpeg.FS('unlink', textName); } catch (_) { }
        }
      } catch (convErr) {
        cleanupFsFile(ffmpeg, textName);
        const classified = classifyOffscreenFfmpegError(convErr?.message || convErr, 'FFmpeg could not convert the copied subtitle stream to text output.');
        if (classified.category === 'subtitle-kind-mismatch') {
          skippedCopyTextConversions += 1;
          continue;
        }
        sendOffscreenLog(`Failed to convert ${copyName} to text subtitle output: ${classified.summary}`, 'warn', messageId);
      }
    }
    if (skippedCopyTextConversions > 0) {
      sendOffscreenLog(
        `Left ${skippedCopyTextConversions} copied subtitle stream(s) as MKV because FFmpeg could not convert them directly to text output.`,
        'info',
        messageId
      );
    }
    if (convertedSrts.length) {
      files = [...files, ...convertedSrts].sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
    }
  }
  const skippedCopies = copiedTracks.length;

  if (!files.length) {
    if (copiedTracks.length) {
      if (plannedTextStreams.length) {
        sendOffscreenLog(
          `Detected ${plannedTextStreams.length} text subtitle stream(s) in the container, but FFmpeg produced no usable text output. Skipping OCR because this is not a bitmap-only stream.`,
          'error',
          messageId
        );
        throw new Error('Text subtitle streams were detected, but FFmpeg could not extract them.');
      }
      await runOcrOnBinaryCopiedTracks(copiedTracks, messageId);
    }
    sendOffscreenLog('FFmpeg completed but no subtitle streams were found.', 'warn', messageId);
    throw new Error('No subtitle streams found in media.');
  }
  sendOffscreenLog(`FFmpeg demux produced ${files.length} track file(s)`, 'info', messageId);

  const decoder = new TextDecoder();
  let tracks = files.map((file) => {
    const data = ffmpeg.FS('readFile', file);
    if (/\.mkv$/i.test(file)) {
      const outputIndex = parseExtractedOutputIndex(file);
      const target = findExtractionTargetByOutputIndex(plannedTextStreams, outputIndex);
      return {
        id: Number.isInteger(outputIndex) ? String(outputIndex) : file.replace(/\..*$/, ''),
        label: target?.name || file,
        language: target?.language || 'und',
        codec: 'copy',
        source: 'copy',
        binary: true,
        mime: 'video/x-matroska',
        byteLength: data.byteLength,
        contentBase64: uint8ToBase64(data)
      };
    }
    const outputIndex = parseExtractedOutputIndex(file);
    const target = findExtractionTargetByOutputIndex(plannedTextStreams, outputIndex);
    return {
      ...buildExtractedTextTrack(file, data, target, decoder),
      source: normalizeSubtitleFormatHint(file)
    };
  });

  // If timelines look broken (e.g., all cues share the same timestamp), retry with a PTS-normalized conversion.
  const timelineStatus = analyzeCueTimelines(tracks);
  const skipFlatCueRepair = opts?.skipFlatCueRepair === true;
  if (timelineStatus.flatCueStarts && skipFlatCueRepair && !timelineStatus.nonMonotonicCues) {
    sendOffscreenLog('Detected flat cue timestamps in a bounded demux pass; skipping PTS normalization for this slice.', 'info', messageId);
  } else if (timelineStatus.flatCueStarts || timelineStatus.nonMonotonicCues) {
    sendOffscreenLog(
      `Detected ${timelineStatus.flatCueStarts ? 'flat' : 'non-monotonic'} cue timestamps; retrying with PTS normalization...`,
      'warn',
      messageId
    );
    try {
      // Remove prior extracted text outputs to avoid mixing old/new
      for (const f of ffmpeg.FS('readdir', '/')) {
        if (/^extracted_sub_(fix_)?\d+\.[a-z0-9]+$/i.test(f) && !/\.mkv$/i.test(f)) {
          try { ffmpeg.FS('unlink', f); } catch (_) { }
        }
      }
      const fixedFiles = await extractSubtitleTextTracksBatch(ffmpeg, inputName, messageId, {
        ...(plannedTextStreams.length ? { streamPlans: plannedTextStreams } : {}),
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
          const data = ffmpeg.FS('readFile', file);
          const outputIndex = parseExtractedOutputIndex(file);
          const target = findExtractionTargetByOutputIndex(plannedTextStreams, outputIndex);
          return buildExtractedTextTrack(file, data, target, decoder);
        });
        const mergedTracks = mergeReplacementTracks(tracks, fixedTracks);
        const fixedStatus = analyzeCueTimelines(mergedTracks);
        if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
          if (mergedTracks.length === tracks.length) {
            sendOffscreenLog('PTS-normalized retry improved timelines; using fixed tracks.', 'info', messageId);
          } else {
            sendOffscreenLog(
              `PTS-normalized retry improved ${fixedTracks.length} track(s); keeping ${Math.max(0, tracks.length - fixedTracks.length)} original track(s) that were not regenerated.`,
              'info',
              messageId
            );
          }
          tracks = mergedTracks;
        } else {
          sendOffscreenLog('PTS-normalized retry still looks broken; keeping original tracks.', 'warn', messageId);
        }
      } else {
        sendOffscreenLog('PTS-normalized retry produced no replacement text outputs.', 'warn', messageId);
      }
    } catch (normErr) {
      sendOffscreenLog(`PTS-normalized retry failed: ${normErr?.message || normErr}`, 'error', messageId);
    }
  }

  // If still broken, try per-stream remux + setpts-style reset before text conversion.
  const postNormStatus = analyzeCueTimelines(tracks);
  if (postNormStatus.nonMonotonicCues || (postNormStatus.flatCueStarts && !skipFlatCueRepair)) {
    sendOffscreenLog('Timelines still broken after PTS normalization; trying per-stream remux...', 'warn', messageId);
    try {
      const remuxed = [];
      const remuxTargets = plannedTextStreams.length
        ? plannedTextStreams
        : getSubtitleExtractionTargets({});
      for (const target of remuxTargets) {
        const streamIndex = target.streamIndex;
        const outputIndex = target.outputIndex;
        const outName = `remux_sub_${String(outputIndex - 1).padStart(2, '0')}.mkv`;
        try {
          await ffmpeg.run(
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
          const data = ffmpeg.FS('readFile', outName);
          if (data?.byteLength) remuxed.push(outName);
        } catch (_) {
          try { ffmpeg.FS('unlink', outName); } catch (_) { }
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
          await ffmpeg.run(
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
          const data = ffmpeg.FS('readFile', textName);
          if (data?.byteLength) {
            fixedTracks.push(buildExtractedTextTrack(textName, data, target, decoder));
          }
        } catch (convErr) {
          sendOffscreenLog(`Remux conversion failed for ${remuxName}: ${convErr?.message || convErr}`, 'warn', messageId);
        }
      }

          if (fixedTracks.length) {
            const mergedTracks = mergeReplacementTracks(tracks, fixedTracks);
            const fixedStatus = analyzeCueTimelines(mergedTracks);
            if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
              if (mergedTracks.length === tracks.length) {
                sendOffscreenLog('Per-stream remux fixed timelines; using remuxed tracks.', 'info', messageId);
              } else {
                sendOffscreenLog(
                  `Per-stream remux fixed ${fixedTracks.length} track(s); keeping ${Math.max(0, tracks.length - fixedTracks.length)} prior track(s) that were not regenerated.`,
                  'info',
                  messageId
                );
              }
              tracks = mergedTracks;
            } else {
              sendOffscreenLog('Per-stream remux still looks broken; keeping prior tracks.', 'warn', messageId);
            }
      } else {
        sendOffscreenLog('Per-stream remux produced no usable tracks.', 'warn', messageId);
      }
    } catch (remuxErr) {
      sendOffscreenLog(`Per-stream remux attempt failed: ${remuxErr?.message || remuxErr}`, 'error', messageId);
    }
  }

  // Attach language metadata from container headers before returning
  const headerLangs = collectSubtitleLanguagesFromHeader(headerView);
  if (headerLangs.length) {
    tracks = applyHeaderLanguagesToTracks(tracks, headerLangs);
  }
  tracks = applyContentLanguageGuesses(tracks);

  // Apply consistent naming/numbering for all outputs
  tracks = normalizeExtractedTracks(tracks);

  const copyNote = skippedCopies ? `; omitted ${skippedCopies} MKV copy track(s) from output` : '';
  sendOffscreenLog(`Demux finished and cleaned up (${tracks.length} track(s)${copyNote})`, 'info', messageId);

  return tracks;
  } finally {
    try {
      for (const file of ffmpeg.FS('readdir', '/')) {
        if (/^(?:embedded_input\.bin|extracted_sub_(?:fix_)?\d+\.[a-z0-9]+|remux_sub_\d+\.mkv)$/i.test(file)) {
          cleanupFsFile(ffmpeg, file);
        }
      }
      inputSource?.cleanup?.();
    } catch (_) { /* ignore */ }
  }
}

function withTimeout(promise, ms, label) {
  let timer;
  const timeout = new Promise((_, reject) => {
    timer = setTimeout(() => reject(new Error(label || `Operation timed out after ${ms}ms`)), ms);
  });
  return Promise.race([promise.finally(() => clearTimeout(timer)), timeout]);
}

const DIRECT_AUDIO_DECODE_TIMEOUT_MS = 3 * 60 * 1000;
const OPFS_AUDIO_DECODE_BASE_TIMEOUT_MS = 12 * 60 * 1000;
const OPFS_AUDIO_DECODE_MAX_TIMEOUT_MS = 30 * 60 * 1000;
const OPFS_AUDIO_DECODE_EXTRA_TIMEOUT_PER_GIB_MS = 6 * 60 * 1000;

function computeAudioDecodeTimeoutMs(windows) {
  const hasOpfsInput = (windows || []).some((win) => isOpfsTempInputSource(win?.buffer));
  if (!hasOpfsInput) {
    return DIRECT_AUDIO_DECODE_TIMEOUT_MS;
  }
  const maxBytes = (windows || []).reduce((max, win) => {
    const bytes = Number(win?.buffer?.byteLength) || Number(win?.buffer?.totalBytes) || 0;
    return Math.max(max, bytes);
  }, 0);
  const oneGiB = 1024 * 1024 * 1024;
  if (maxBytes <= oneGiB) {
    return OPFS_AUDIO_DECODE_BASE_TIMEOUT_MS;
  }
  const extraGiB = Math.ceil((maxBytes - oneGiB) / oneGiB);
  return Math.min(
    OPFS_AUDIO_DECODE_MAX_TIMEOUT_MS,
    OPFS_AUDIO_DECODE_BASE_TIMEOUT_MS + (extraGiB * OPFS_AUDIO_DECODE_EXTRA_TIMEOUT_PER_GIB_MS)
  );
}

/**
 * Extract subtitles using HTML5 Video element and TextTrack API
 * This is the preferred method as it gets complete subtitle tracks without downloading the entire video
 */
async function extractSubtitlesViaVideo(streamUrl, mode, messageId) {
  const normalizedMode = 'single';
  sendOffscreenLog(`Starting video-based subtitle extraction (${normalizedMode} mode)...`, 'info', messageId);
  sendOffscreenLog(`Target URL: ${streamUrl.substring(0, 100)}${streamUrl.length > 100 ? '...' : ''}`, 'info', messageId);

  return new Promise((resolve, reject) => {
    const video = document.createElement('video');
    video.crossOrigin = 'use-credentials'; // allow cookie-authenticated hosts (falls back to anonymous on error)
    video.preload = 'metadata';
    video.style.display = 'none';
    document.body.appendChild(video);

    const tracks = [];
    let tracksLoaded = 0;
    let tracksExpected = 0;
    let metadataLoaded = false;
    let cleanupDone = false;
    let retriedAnonymous = false;
    let settled = false;
    let cancelPoll = null;
    const pendingTimers = new Set();

    const finish = (fn, value) => {
      if (settled) return;
      settled = true;
      cleanup();
      fn(value);
    };

    const scheduleTimer = (fn, ms) => {
      const timer = setTimeout(() => {
        pendingTimers.delete(timer);
        fn();
      }, ms);
      pendingTimers.add(timer);
      return timer;
    };

    const abortIfRequested = () => {
      try {
        throwIfOffscreenJobAborted(messageId);
        return false;
      } catch (err) {
        sendOffscreenLog(`Video extraction cancelled: ${err?.message || err}`, 'warn', messageId);
        finish(reject, err);
        return true;
      }
    };

    const timeout = setTimeout(() => {
      if (!cleanupDone) {
        const msg = tracks.length > 0
          ? `Extraction timed out but found ${tracks.length} track(s)`
          : 'Extraction timed out - no tracks found';
        sendOffscreenLog(msg, tracks.length > 0 ? 'warn' : 'error', messageId);
        if (tracks.length > 0) {
          finish(resolve, tracks);
        } else {
          finish(reject, new Error('Video subtitle extraction timed out'));
        }
      }
    }, 120000);

    function cleanup() {
      if (cleanupDone) return;
      cleanupDone = true;
      clearTimeout(timeout);
      if (cancelPoll) clearInterval(cancelPoll);
      for (const timer of pendingTimers) {
        clearTimeout(timer);
      }
      pendingTimers.clear();
      try {
        for (let i = 0; i < (video.textTracks?.length || 0); i++) {
          video.textTracks[i].mode = 'disabled';
        }
      } catch (_) { /* ignore */ }
      video.pause();
      video.src = '';
      video.load();
      try {
        document.body.removeChild(video);
      } catch (_) { }
    }

    function convertVttCuesToSrt(cues) {
      let srt = '';
      let index = 1;

      for (const cue of cues) {
        const startMs = Math.floor(cue.startTime * 1000);
        const endMs = Math.floor(cue.endTime * 1000);

        const startHours = Math.floor(startMs / 3600000);
        const startMinutes = Math.floor((startMs % 3600000) / 60000);
        const startSeconds = Math.floor((startMs % 60000) / 1000);
        const startMillis = startMs % 1000;

        const endHours = Math.floor(endMs / 3600000);
        const endMinutes = Math.floor((endMs % 3600000) / 60000);
        const endSeconds = Math.floor((endMs % 60000) / 1000);
        const endMillis = endMs % 1000;

        const startTime = `${String(startHours).padStart(2, '0')}:${String(startMinutes).padStart(2, '0')}:${String(startSeconds).padStart(2, '0')},${String(startMillis).padStart(3, '0')}`;
        const endTime = `${String(endHours).padStart(2, '0')}:${String(endMinutes).padStart(2, '0')}:${String(endSeconds).padStart(2, '0')},${String(endMillis).padStart(3, '0')}`;

        srt += `${index}\n${startTime} --> ${endTime}\n${cue.text}\n\n`;
        index++;
      }

      return srt.trim();
    }

    function extractTrackContent(track, trackIndex) {
      return new Promise((resolveTrack) => {
        let trackSettled = false;
        let fallbackTimer = null;
        const finishTrack = (value) => {
          if (trackSettled) return;
          trackSettled = true;
          if (fallbackTimer) {
            clearTimeout(fallbackTimer);
            pendingTimers.delete(fallbackTimer);
          }
          resolveTrack(value);
        };
        const trackObj = video.textTracks[trackIndex];
        if (!trackObj) {
          sendOffscreenLog(`Track ${trackIndex} not accessible`, 'warn', messageId);
          finishTrack(null);
          return;
        }

        const handleCueChange = () => {
          if (settled || cleanupDone) {
            finishTrack(null);
            return;
          }
          try {
            const cues = Array.from(trackObj.cues || []);
            if (cues.length === 0) {
              sendOffscreenLog(`Track ${trackIndex} loaded but has no cues`, 'warn', messageId);
              finishTrack(null);
              return;
            }

            const content = convertVttCuesToSrt(cues);
            const sizeKb = Math.round((content.length / 1024) * 10) / 10;
            sendOffscreenLog(`Track ${trackIndex}: extracted ${cues.length} cues (${sizeKb} KB)`, 'info', messageId);

            const langFromTrack = normalizeTrackLanguageCode(track.srclang || trackObj.language);
            const langGuess = detectLanguageFromLabel(track.label || trackObj.label || '');
            const langFromContent = detectLanguageFromContent(content);
            const language = langFromTrack || langFromContent || langGuess || 'und';

            finishTrack({
              id: String(trackIndex + 1),
              label: track.label || trackObj.label || `Track ${trackIndex + 1}`,
              language,
              codec: 'srt',
              binary: false,
              byteLength: content.length,
              content: content
            });
          } catch (err) {
            sendOffscreenLog(`Failed to extract track ${trackIndex}: ${err?.message || err}`, 'error', messageId);
            finishTrack(null);
          } finally {
            trackObj.removeEventListener('cuechange', handleCueChange);
            trackObj.mode = 'disabled';
          }
        };

        // Enable the track to trigger cue loading
        trackObj.mode = 'hidden';
        trackObj.addEventListener('cuechange', handleCueChange);

        // If cues are already loaded, trigger immediately
        if (trackObj.cues && trackObj.cues.length > 0) {
          fallbackTimer = scheduleTimer(handleCueChange, 100);
        } else {
          // Set a fallback timeout for this specific track
          fallbackTimer = scheduleTimer(() => {
            if (settled || cleanupDone) {
              finishTrack(null);
              return;
            }
            if (trackObj.cues && trackObj.cues.length > 0) {
              handleCueChange();
            } else {
              sendOffscreenLog(`Track ${trackIndex} timed out without loading cues`, 'warn', messageId);
              trackObj.removeEventListener('cuechange', handleCueChange);
              finishTrack(null);
            }
          }, 30000);
        }
      });
    }

    if (abortIfRequested()) {
      return;
    }
    cancelPoll = setInterval(() => {
      abortIfRequested();
    }, 250);

    video.addEventListener('loadedmetadata', async () => {
      if (metadataLoaded || settled || abortIfRequested()) return;
      metadataLoaded = true;

      sendOffscreenLog(`Video metadata loaded - duration: ${Math.round(video.duration)}s, ${video.videoWidth}x${video.videoHeight}`, 'info', messageId);
      sendOffscreenLog(`Video readyState: ${video.readyState}, networkState: ${video.networkState}`, 'info', messageId);

      // Check for text tracks
      tracksExpected = video.textTracks.length;
      sendOffscreenLog(`video.textTracks.length = ${tracksExpected}`, 'info', messageId);

      // Log all available tracks for debugging
      if (video.textTracks && video.textTracks.length > 0) {
        for (let i = 0; i < video.textTracks.length; i++) {
          const track = video.textTracks[i];
          sendOffscreenLog(`  Track ${i}: kind=${track.kind}, label="${track.label}", lang=${track.language}, mode=${track.mode}`, 'info', messageId);
        }
      }

      // Check for video tracks (informational)
      if (video.videoTracks) {
        sendOffscreenLog(`video.videoTracks.length = ${video.videoTracks.length}`, 'info', messageId);
      }

      // Check for audio tracks (informational)
      if (video.audioTracks) {
        sendOffscreenLog(`video.audioTracks.length = ${video.audioTracks.length}`, 'info', messageId);
      }

      if (tracksExpected === 0) {
        sendOffscreenLog('No text tracks found - video.textTracks is empty', 'warn', messageId);
        sendOffscreenLog('IMPORTANT: video.textTracks only exposes tracks added via <track> HTML elements, NOT embedded subtitle streams in the video container (MKV/MP4)', 'warn', messageId);
        sendOffscreenLog('This is expected behavior - FFmpeg fallback will extract embedded streams', 'info', messageId);
        finish(reject, new Error('No embedded subtitle tracks found in video'));
        return;
      }

      sendOffscreenLog(`Found ${tracksExpected} text track(s), extracting...`, 'info', messageId);

      // Extract each track
      const trackPromises = [];
      for (let i = 0; i < tracksExpected; i++) {
        const track = video.textTracks[i];
        trackPromises.push(extractTrackContent(track, i));
      }

      try {
        const results = await Promise.all(trackPromises);
        if (settled || abortIfRequested()) return;
        const validTracks = results.filter(t => t !== null);

        if (validTracks.length === 0) {
          finish(reject, new Error('Failed to extract any subtitle content from tracks'));
          return;
        }

        sendOffscreenLog(`Successfully extracted ${validTracks.length}/${tracksExpected} track(s)`, 'info', messageId);
        const namedTracks = normalizeExtractedTracks(validTracks);
        finish(resolve, namedTracks);
      } catch (err) {
        finish(reject, err);
      }
    });

    video.addEventListener('error', (e) => {
      if (settled || abortIfRequested()) return;
      const error = video.error;
      let errorDetails = 'Unknown error';
      if (error) {
        const errorCodes = {
          1: 'MEDIA_ERR_ABORTED - fetch aborted by user',
          2: 'MEDIA_ERR_NETWORK - network error',
          3: 'MEDIA_ERR_DECODE - decoding error',
          4: 'MEDIA_ERR_SRC_NOT_SUPPORTED - format not supported'
        };
        errorDetails = errorCodes[error.code] || `code ${error.code}`;
        if (error.message) errorDetails += ` - ${error.message}`;
      }
      const msg = `Video element error: ${errorDetails}`;
      sendOffscreenLog(msg, 'error', messageId);
      // If CORS/credentials caused the failure, retry once without credentials
      if (!retriedAnonymous) {
        retriedAnonymous = true;
        sendOffscreenLog('Retrying video load with crossOrigin=anonymous after error...', 'warn', messageId);
        try {
          video.pause();
          video.removeAttribute('src');
          video.load();
          video.crossOrigin = 'anonymous';
          video.src = streamUrl;
          video.load();
          return;
        } catch (_) {
          // fall through to failure
        }
      }
      finish(reject, new Error(msg));
    });

    // Add event listeners for tracking video load progress
    video.addEventListener('loadstart', () => {
      sendOffscreenLog('Video load started', 'info', messageId);
    });

    let progressCount = 0;
    video.addEventListener('progress', () => {
      // Only log every 5th progress event to avoid spam
      if (++progressCount % 5 === 0) {
        const buffered = video.buffered.length > 0 ? Math.round(video.buffered.end(0) * 10) / 10 : 0;
        sendOffscreenLog(`Video loading progress: ${buffered}s buffered`, 'info', messageId);
      }
    });

    video.addEventListener('stalled', () => {
      sendOffscreenLog('Video load stalled', 'warn', messageId);
    });
    video.addEventListener('suspend', () => {
      sendOffscreenLog('Video load suspended (network idle)', 'info', messageId);
    });
    video.addEventListener('waiting', () => {
      sendOffscreenLog('Video waiting for more data', 'info', messageId);
    });
    video.addEventListener('abort', () => {
      sendOffscreenLog('Video load aborted', 'warn', messageId);
    });

    video.addEventListener('canplay', () => {
      sendOffscreenLog('Video is ready to play', 'info', messageId);
    });

    // Listen for track additions (this would fire if tracks are added dynamically)
    if (video.textTracks) {
      video.textTracks.addEventListener('addtrack', (e) => {
        sendOffscreenLog(`Text track added: kind=${e.track?.kind}, label="${e.track?.label}", lang=${e.track?.language}`, 'info', messageId);
      });
    }

    // Start loading
    sendOffscreenLog('Initializing video element with stream URL...', 'info', messageId);
    video.src = streamUrl;
    video.load();
    sendOffscreenLog('Waiting for video metadata to load...', 'info', messageId);
  });
}

chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  console.log('[Offscreen] Message received', {
    type: message?.type,
    messageId: message?.messageId,
    transferId: message?.transferId,
    fromTab: sender?.tab?.id,
    frameId: sender?.frameId,
    hasBuffer: !!message?.buffer,
    windowCount: Array.isArray(message?.windows) ? message.windows.length : undefined
  });
  if (message?.type === 'OFFSCREEN_PING') {
    try { sendResponse?.({ ok: true, ts: Date.now() }); } catch (_) { }
    return false;
  }
  if (message?.type === 'OFFSCREEN_FFMPEG_BUFFER_CHUNK') {
    const res = stashChunk(message.transferId, message.chunkIndex, message.totalChunks, message.chunk, message.expectedBytes, message.chunkArray);
    const shouldLogChunk = message.totalChunks <= 20 || message.chunkIndex === 0 || message.chunkIndex === message.totalChunks - 1 || ((message.chunkIndex + 1) % 25 === 0);
    if (shouldLogChunk) {
      console.log('[Offscreen] Buffer chunk received', {
        transferId: message.transferId,
        idx: message.chunkIndex + 1,
        total: message.totalChunks,
        complete: res?.complete
      });
    }
    sendResponse(res);
    return false;
  }

  if (message?.type === 'OFFSCREEN_CANCEL') {
    const aborted = markOffscreenJobAborted(message?.messageId, message?.reason || 'Operation cancelled');
    if (message?.transferId) {
      _chunkedBuffers.delete(message.transferId);
    }
    try { sendResponse?.({ ok: true, aborted }); } catch (_) { }
    return false;
  }

  if (message?.type === 'OFFSCREEN_FFMPEG_EXTRACT') {
    const requestId = message?.messageId;
    beginOffscreenJob(requestId);
    console.log('[Offscreen] Handling OFFSCREEN_FFMPEG_EXTRACT', {
      requestId,
      hasBuffer: !!message?.buffer,
      transferId: message?.transferId,
      transferMethod: message?.transferMethod
    });
    (async () => {
      let responded = false;
      const respond = (payload) => {
        if (responded) return;
        responded = true;
        console.log('[Offscreen] Responding to demux request', {
          requestId,
          success: payload?.success,
          hasTracks: Array.isArray(payload?.tracks)
        });
        const slim = payload ? {
          success: payload.success,
          error: payload.error,
          messageId: requestId,
          chunked: payload.chunked === true
        } : undefined;
        try { sendResponse(slim); } catch (err) { console.warn('[Offscreen] sendResponse failed:', err); }
        try {
          chrome.runtime.sendMessage({
            type: 'OFFSCREEN_FFMPEG_RESULT',
            messageId: requestId,
            ...payload
          });
        } catch (err) {
          console.warn('[Offscreen] Failed to push demux result to background:', err);
        }
      };
      try {
        let incomingBuffer = message?.buffer;
        const transferMethod = message?.transferMethod || '';
        const transferId = message?.transferId || (incomingBuffer && incomingBuffer.transferId);
        throwIfOffscreenJobAborted(requestId);

        if (transferMethod === 'opfs') {
          incomingBuffer = {
            opfsTempName: String(message?.opfsTempName || ''),
            byteLength: Number.isFinite(message?.byteLength) ? message.byteLength : 0
          };
        } else if (transferMethod === 'idb' && transferId) {
          try {
            incomingBuffer = await SubMakerTransfer.loadTransferBuffer(transferId);
            // Clean up immediately after loading
            SubMakerTransfer.deleteTransferBuffer(transferId).catch(e => console.warn('Failed to delete transfer buffer', e));
          } catch (err) {
            throw new Error(`Failed to load IDB transfer buffer: ${err.message}`);
          }
        } else if (!incomingBuffer && transferId) {
          incomingBuffer = consumeChunkedBuffer(transferId);
          if (!incomingBuffer) {
            throw new Error('Chunked buffer incomplete or missing for demux request');
          }
        }
        if (incomingBuffer && incomingBuffer.transferId) {
          incomingBuffer = consumeChunkedBuffer(incomingBuffer.transferId);
        }
        if (!incomingBuffer) throw new Error('Missing buffer in offscreen request');
        throwIfOffscreenJobAborted(requestId);
        const requestBytes = incomingBuffer?.byteLength || incomingBuffer?.size || 0;
        const sizeMb = Math.round((requestBytes / (1024 * 1024)) * 10) / 10;
        const timeoutMs = computeOffscreenDemuxTimeoutMs(transferMethod, requestBytes);
        sendOffscreenLog(`Received demux request (job ${requestId || 'n/a'}), size: ${sizeMb} MB${transferMethod === 'opfs' ? ' via OPFS' : ''}`, 'info', requestId);
        sendOffscreenLog(`Offscreen env: SAB=${typeof SharedArrayBuffer !== 'undefined' ? 'yes' : 'no'}, COI=${self.crossOriginIsolated === false ? 'no' : 'yes'}`, 'info', requestId);
        const tracks = await withTimeout(
          demuxSubtitles(incomingBuffer, requestId, {
            inputArgs: Array.isArray(message?.inputArgs) ? message.inputArgs : [],
            skipCopyTracks: message?.skipCopyTracks === true,
            skipFlatCueRepair: message?.skipFlatCueRepair === true,
            streamPlans: Array.isArray(message?.streamPlans) ? message.streamPlans : [],
            textStreamPlans: Array.isArray(message?.textStreamPlans) ? message.textStreamPlans : []
          }),
          timeoutMs,
          `FFmpeg demux timed out in offscreen page${requestId ? ` (job ${requestId})` : ''}`
        );
        throwIfOffscreenJobAborted(requestId);
        const prepared = await prepareTracksForSend(tracks, requestId);
        throwIfOffscreenJobAborted(requestId);
        respond({ success: true, tracks: prepared.tracks, chunked: prepared.chunked });
      } catch (err) {
        const errMessage = err?.message || String(err);
        if (/timed out/i.test(errMessage)) {
          markOffscreenJobAborted(requestId, errMessage);
        }
        const level = isAbortError(err) ? 'warn' : 'error';
        console[level === 'error' ? 'error' : 'warn']('[Offscreen] Extraction failed:', err);
        sendOffscreenLog(`Demux failed: ${errMessage}`, level, requestId);
        respond({ success: false, error: errMessage });
      } finally {
        finishOffscreenJob(requestId);
      }
    })();
    return true; // async
  }

  if (message?.type === 'OFFSCREEN_FFMPEG_DECODE') {
    const requestId = message?.messageId;
    beginOffscreenJob(requestId);
    console.log('[Offscreen] Handling OFFSCREEN_FFMPEG_DECODE', {
      requestId,
      windowCount: Array.isArray(message?.windows) ? message.windows.length : 0,
      audioStreamIndex: message?.audioStreamIndex
    });
    (async () => {
      let responded = false;
      const cloneAudioWindows = (wins) => {
        if (!Array.isArray(wins)) return [];
        return wins.map((w) => {
          const bytes = w?.audioBytes;
          let cloned = null;
          if (bytes instanceof Uint8Array) {
            cloned = bytes.slice();
          } else if (bytes && typeof bytes.byteLength === 'number') {
            cloned = new Uint8Array(bytes);
          } else if (Array.isArray(bytes)) {
            cloned = Uint8Array.from(bytes);
          }
          return {
            audioBytes: cloned || new Uint8Array(0),
            startMs: Math.round(w?.startMs || 0)
          };
        });
      };
      const respond = (payload) => {
        if (responded) return;
        responded = true;
        console.log('[Offscreen] Responding to decode request', {
          requestId,
          success: payload?.success,
          windows: payload?.audioWindows?.length
        });
        const slim = payload ? {
          success: payload.success,
          error: payload.error,
          messageId: requestId,
          chunked: payload.chunked === true
        } : undefined;
        try { sendResponse(slim); } catch (err) { console.warn('[Offscreen] sendResponse failed:', err); }
        try {
          chrome.runtime.sendMessage({
            type: 'OFFSCREEN_FFMPEG_RESULT',
            messageId: requestId,
            ...payload
          });
        } catch (err) {
          console.warn('[Offscreen] Failed to push decode result to background:', err);
        }
      };

      try {
        const rawWindows = Array.isArray(message?.windows) ? message.windows : [];
        if (!rawWindows.length) {
          throw new Error('No audio windows provided for decode');
        }
        throwIfOffscreenJobAborted(requestId);

        // Some decode requests reuse the same transferId across multiple windows to avoid
        // duplicating large buffers. Cache each loaded buffer so we only consume IDB/chunks once.
        const bufferCache = new Map();
        const normalizeOpfsBuffer = (value) => {
          if (!isOpfsTempInputSource(value)) {
            return null;
          }
          const opfsTempName = String(value.opfsTempName || '').trim();
          const byteLength = Number(value?.byteLength) || Number(value?.totalBytes) || 0;
          if (!opfsTempName || !byteLength) {
            return null;
          }
          const cacheKey = `opfs:${opfsTempName}:${byteLength}`;
          const cached = bufferCache.get(cacheKey);
          if (cached) {
            return cached;
          }
          const normalized = {
            opfsTempName,
            byteLength,
            totalBytes: Number(value?.totalBytes) || byteLength,
            contentType: value?.contentType || ''
          };
          bufferCache.set(cacheKey, normalized);
          return normalized;
        };

        const windows = [];
        for (let idx = 0; idx < rawWindows.length; idx++) {
          const w = rawWindows[idx];
          let buf = w?.buffer;
          const transferMethod = w?.transferMethod || (buf && buf.transferMethod);
          const transferId = w?.transferId || (buf && buf.transferId);

          const loadFromTransfer = async (id, method) => {
            if (bufferCache.has(id)) {
              return bufferCache.get(id);
            }
            let loaded = null;
            if (method === 'idb') {
              try {
                loaded = await SubMakerTransfer.loadTransferBuffer(id);
                SubMakerTransfer.deleteTransferBuffer(id).catch(e => console.warn('Failed to delete transfer buffer', e));
              } catch (err) {
                throw new Error(`Failed to load IDB transfer buffer for window ${idx + 1}: ${err?.message || err}`);
              }
            } else {
              loaded = consumeChunkedBuffer(id);
            }
            const normalized = loaded instanceof Uint8Array ? loaded : (loaded ? new Uint8Array(loaded) : null);
            if (normalized) {
              bufferCache.set(id, normalized);
            }
            return normalized;
          };

          const directOpfsBuffer = normalizeOpfsBuffer(buf);
          if (directOpfsBuffer) {
            throwIfOffscreenJobAborted(requestId);
            windows.push({
              buffer: directOpfsBuffer,
              startSec: w?.startSec,
              durSec: w?.durSec,
              seekToSec: w?.seekToSec
            });
            continue;
          }

          if (transferId) {
            buf = await loadFromTransfer(transferId, transferMethod);
          } else if (buf && buf.transferId) {
            buf = await loadFromTransfer(buf.transferId, buf.transferMethod || transferMethod);
          }
          if (!buf) {
            throw new Error(`Missing buffer for window ${idx + 1}`);
          }
          throwIfOffscreenJobAborted(requestId);
          windows.push({
            buffer: buf instanceof Uint8Array ? buf : new Uint8Array(buf),
            startSec: w?.startSec,
            durSec: w?.durSec,
            seekToSec: w?.seekToSec
          });
        }

        const decodeTimeoutMs = computeAudioDecodeTimeoutMs(windows);
        const decoded = await withTimeout(
          decodeAudioWindows(windows, 'single', requestId, { audioStreamIndex: message?.audioStreamIndex }),
          decodeTimeoutMs,
          `FFmpeg audio decode timed out${requestId ? ` (job ${requestId})` : ''}`
        );
        throwIfOffscreenJobAborted(requestId);
        const safeWindows = cloneAudioWindows(decoded);

        const prepared = [];
        for (let i = 0; i < safeWindows.length; i++) {
          const win = safeWindows[i];
          const bytes = win?.audioBytes instanceof Uint8Array ? win.audioBytes : new Uint8Array(win?.audioBytes || []);
          const transferId = `adec_${requestId || Date.now()}_${i}_${Math.random().toString(16).slice(2)}`;
          await sendResultChunksToBackground(transferId, bytes, requestId, `audio_${i + 1}`);
          prepared.push({
            transferId,
            totalBytes: bytes.byteLength,
            startMs: Math.round(win?.startMs || 0),
            chunked: true
          });
        }

        throwIfOffscreenJobAborted(requestId);
        respond({ success: true, audioWindows: prepared, chunked: true });
      } catch (err) {
        const level = isAbortError(err) ? 'warn' : 'error';
        console[level === 'error' ? 'error' : 'warn']('[Offscreen] Audio decode failed:', err);
        sendOffscreenLog(`Audio decode failed: ${err?.message || err}`, level, requestId);
        respond({ success: false, error: err?.message || String(err) });
      } finally {
        finishOffscreenJob(requestId);
      }
    })();
    return true;
  }

  if (message?.type === 'OFFSCREEN_VIDEO_EXTRACT') {
    const requestId = message?.messageId;
    beginOffscreenJob(requestId);
    console.log('[Offscreen] Handling OFFSCREEN_VIDEO_EXTRACT', {
      requestId,
      streamUrl: message?.streamUrl?.substring(0, 80)
    });
    (async () => {
      let responded = false;
      const respond = (payload) => {
        if (responded) return;
        responded = true;
        console.log('[Offscreen] Responding to video extract', {
          requestId,
          success: payload?.success,
          tracks: payload?.tracks?.length
        });
        const slim = payload ? {
          success: payload.success,
          error: payload.error,
          messageId: requestId,
          chunked: payload.chunked === true
        } : undefined;
        try { sendResponse(slim); } catch (err) { console.warn('[Offscreen] sendResponse failed:', err); }
        try {
          chrome.runtime.sendMessage({
            type: 'OFFSCREEN_VIDEO_RESULT',
            messageId: requestId,
            ...payload
          });
        } catch (err) {
          console.warn('[Offscreen] Failed to push video extract result to background:', err);
        }
      };

      try {
        const streamUrl = message?.streamUrl;
        const mode = 'single';

        if (!streamUrl) {
          throw new Error('Missing streamUrl for video extraction');
        }
        throwIfOffscreenJobAborted(requestId);

        sendOffscreenLog(`Starting video-based extraction for ${streamUrl.substring(0, 60)}...`, 'info', requestId);

        const tracks = await withTimeout(
          extractSubtitlesViaVideo(streamUrl, mode, requestId),
          180000,
          `Video extraction timed out${requestId ? ` (job ${requestId})` : ''}`
        );

        throwIfOffscreenJobAborted(requestId);
        const prepared = await prepareTracksForSend(tracks, requestId);
        respond({ success: true, tracks: prepared.tracks, chunked: prepared.chunked });
      } catch (err) {
        const level = isAbortError(err) ? 'warn' : 'error';
        console[level === 'error' ? 'error' : 'warn']('[Offscreen] Video extraction failed:', err);
        sendOffscreenLog(`Video extraction failed: ${err?.message || err}`, level, requestId);
        respond({ success: false, error: err?.message || String(err) });
      } finally {
        finishOffscreenJob(requestId);
      }
    })();
    return true;
  }
});

console.log('[Offscreen] Ready for FFmpeg demux and video extraction requests');
