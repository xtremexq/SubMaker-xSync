/**
 * SubMaker xSync - Background Service Worker
 * Handles audio extraction and subtitle synchronization
 */

console.log('[SubMaker xSync Background] Service worker initialized');
const BOOTSTRAP_MODE = self.__xsyncBootstrapped === true;

// Catch-all to surface unexpected errors that can silently kill the service worker
self.addEventListener('error', (evt) => {
  try {
    console.error('[Background] Unhandled error event:', evt?.message || evt?.error || evt);
  } catch (_) { }
});
self.addEventListener('unhandledrejection', (evt) => {
  try {
    console.error('[Background] Unhandled rejection:', evt?.reason || evt);
  } catch (_) { }
});

const _workerBootTs = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
console.log('[Background][Timing] worker boot at', _workerBootTs);
// Heavy libraries (FFmpeg/IDB helpers) now load lazily to keep popup open quickly.

// Detect whether eval/new Function is blocked by CSP (MV3 disallows unsafe-eval in extension pages).
let WHISPER_EVAL_ALLOWED = true;
let WHISPER_EVAL_REASON = '';
try {
  // eslint-disable-next-line no-new-func
  new Function('return true;')();
} catch (e) {
  WHISPER_EVAL_ALLOWED = false;
  WHISPER_EVAL_REASON = e?.message || 'unsafe-eval blocked by CSP';
  console.warn('[Background] Whisper disabled because eval is blocked by CSP:', WHISPER_EVAL_REASON);
}

// Preload alass wrapper + glue at startup to avoid MV3 importScripts restrictions/CSP eval fallbacks.
let _alassPreloaded = false;
let _alassPreloadError = null;

// Lazy WASM loaders
let _ffmpegInstance = null;
let _ffmpegMode = 'uninitialized';
let _alassReady = false;
let _alassApi = null;
let _ffsubsyncReady = false;
let _ffsubsyncApi = null;
let _offscreenCreated = false;
let _offscreenReady = false;
let _offscreenReadyPromise = null;
let _offscreenActive = 0;
let _offscreenCleanupTimer = null;
const _offscreenResultChunks = new Map();
const OFFSCREEN_IDLE_CLOSE_MS = 15000;
const MAX_EMBEDDED_EXTRACTS_TOTAL = 2;
const MAX_EMBEDDED_EXTRACTS_PER_TAB = 1;
const RESULT_CHUNK_TTL_MS = 5 * 60 * 1000;
const ASSEMBLY_POLL_TIMEOUT_MS = 5 * 60 * 1000;
const ASSEMBLY_POLL_INTERVAL_MS = 3000;

function logOffscreenLifecycle(event, extra = {}) {
  console.log('[Background][Offscreen]', event, {
    ...extra,
    created: _offscreenCreated,
    ready: _offscreenReady,
    active: _offscreenActive
  });
}

function pingOffscreen(timeoutMs = 2000) {
  return new Promise((resolve, reject) => {
    let settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      reject(new Error('Offscreen ping timed out'));
    }, timeoutMs);
    try {
      chrome.runtime.sendMessage({ type: 'OFFSCREEN_PING' }, (resp) => {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
        if (chrome.runtime.lastError) {
          return reject(new Error(chrome.runtime.lastError.message));
        }
        if (resp?.ok) return resolve(true);
        reject(new Error('Offscreen ping failed'));
      });
    } catch (err) {
      if (!settled) {
        settled = true;
        clearTimeout(timer);
        reject(err);
      }
    }
  });
}

async function waitForOffscreenReady(force = false, timeoutMs = 6000) {
  if (_offscreenReady && !force) return true;
  if (_offscreenReadyPromise) {
    return _offscreenReadyPromise;
  }
  const started = Date.now();
  let attempt = 0;
  _offscreenReadyPromise = (async () => {
    while (Date.now() - started < timeoutMs) {
      attempt += 1;
      try {
        await pingOffscreen();
        _offscreenReady = true;
        return true;
      } catch (err) {
        _offscreenReady = false;
        if (Date.now() - started >= timeoutMs) throw err;
        await new Promise((r) => setTimeout(r, 150 * attempt));
      }
    }
    throw new Error('Offscreen did not respond to ping');
  })();
  try {
    return await _offscreenReadyPromise;
  } finally {
    _offscreenReadyPromise = null;
  }
}

function stashResultChunk(transferId, chunkIndex, totalChunks, chunkArray, expectedBytes) {
  if (!transferId || totalChunks <= 0 || chunkIndex < 0 || chunkIndex >= totalChunks) {
    return { ok: false, error: 'Invalid chunk metadata' };
  }
  const part = Array.isArray(chunkArray) ? Uint8Array.from(chunkArray) : null;
  const partBytes = part?.byteLength || 0;
  if (!partBytes) return { ok: false, error: 'Empty result chunk' };
  if (expectedBytes && partBytes !== expectedBytes) {
    return { ok: false, error: `Chunk size mismatch (expected ${expectedBytes}, got ${partBytes})` };
  }
  let entry = _offscreenResultChunks.get(transferId);
  if (!entry || entry.totalChunks !== totalChunks) {
    entry = { totalChunks, parts: new Array(totalChunks), received: 0, timer: null };
    _offscreenResultChunks.set(transferId, entry);
  }
  if (!entry.parts[chunkIndex]) {
    entry.received += 1;
  }
  entry.parts[chunkIndex] = part;
  if (entry.timer) clearTimeout(entry.timer);
  entry.timer = setTimeout(() => _offscreenResultChunks.delete(transferId), RESULT_CHUNK_TTL_MS);
  const complete = entry.received === entry.totalChunks && entry.parts.every(Boolean);
  return { ok: true, complete, received: entry.received, total: entry.totalChunks };
}

function consumeResultBuffer(transferId) {
  const entry = _offscreenResultChunks.get(transferId);
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
  _offscreenResultChunks.delete(transferId);
  return merged;
}

// State management
let activeSyncJobs = new Map();
let activeExtractJobs = new Map();

// Reset active stats on startup to prevent stuck "Syncing now" state
chrome.storage.local.set({ activeSyncs: 0 }).catch(() => { });

function cleanupExtractJobsForTab(tabId) {
  if (!tabId) return 0;
  let removed = 0;
  activeExtractJobs.forEach((job, key) => {
    if (job?.tabId === tabId) {
      activeExtractJobs.delete(key);
      removed += 1;
    }
  });
  return removed;
}

const DEBUG_FLAG_KEY = 'debugLogsEnabled';
let DEBUG_LOGS_ENABLED = true; // default to verbose so users can see extraction issues without a manual toggle
function refreshDebugFlag() {
  try {
    chrome.storage.local.get([DEBUG_FLAG_KEY]).then((res) => {
      const stored = res?.[DEBUG_FLAG_KEY];
      if (typeof stored === 'boolean') {
        DEBUG_LOGS_ENABLED = stored;
      }
    }).catch(() => { });
  } catch (_) { /* ignore */ }
}
refreshDebugFlag();
chrome.storage.onChanged.addListener((changes, area) => {
  if (area === 'local' && Object.prototype.hasOwnProperty.call(changes, DEBUG_FLAG_KEY)) {
    const next = changes[DEBUG_FLAG_KEY]?.newValue;
    DEBUG_LOGS_ENABLED = typeof next === 'boolean' ? next : true;
  }
});
const debugEnabled = () => DEBUG_LOGS_ENABLED === true;
const shouldBroadcastLevel = (level = 'info', force = false) => force || debugEnabled() || level === 'error' || level === 'warn';

// Whisper WASM (autosync)
const WHISPER_MODEL_FILE = 'whisper.bin';
const WHISPER_MODEL_URL = chrome.runtime.getURL('assets/lib/ggml-tiny.en-q5_1.bin');
const WHISPER_JS_URL = chrome.runtime.getURL('assets/lib/whisper-main.js');
let whisperModuleReady = null;
let whisperInstance = null;
let whisperBusy = false;
let _whisperPreloaded = false;
let _whisperPreloadError = null;

// Vosk (CTC/DTW aligner)
const VOSK_JS_URL = chrome.runtime.getURL('assets/lib/vosk-browser.js');
const VOSK_MODEL_ARCHIVE_URL = chrome.runtime.getURL('assets/models/vosk-model-small-en-us-0.15.tar.gz');
const VOSK_SAMPLE_RATE = 16000;
let voskModelPromise = null;
let voskModelInstance = null;
let voskLoadError = null;

function isHttpUrl(url) {
  return /^https?:\/\//i.test(String(url || ''));
}

function normalizeExtractMode(mode) {
  const cleaned = String(mode || '')
    .trim()
    .toLowerCase()
    .replace(/[-_\s]*v2$/, '')      // strip legacy -v2/_v2 suffix
    .replace(/[-_\s]+/g, '-');      // align separators for comparisons
  if (cleaned === 'complete' || cleaned === 'full' || cleaned === 'fullfetch') return 'complete';
  if (cleaned === 'smart') return 'smart';
  return 'smart';
}

// Preload the IDB transfer helper at boot so MV3 doesn't block late importScripts calls.
let _transferHelperReady = false;
let _transferHelperError = null;
try {
  if (typeof importScripts === 'function') {
    const preloadUrl = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/idb-transfer.js') : 'assets/lib/idb-transfer.js';
    importScripts(preloadUrl);
    _transferHelperReady = !!self.SubMakerTransfer;
  }
} catch (err) {
  _transferHelperError = err;
  console.warn('[Background] Failed to preload IDB transfer helper:', err?.message || err);
}

async function safeFetch(url, options = {}) {
  const opts = {
    cache: 'no-store',
    redirect: 'follow',
    referrerPolicy: 'no-referrer',
    credentials: 'include',
    ...options
  };
  const host = (() => { try { return new URL(url).hostname; } catch (_) { return url; } })();
  const attempts = [];

  // Attempt 1: as-is
  attempts.push({ label: 'default', opts });

  // Attempt 2: omit credentials if first attempt fails
  if (opts.credentials === 'include') {
    attempts.push({ label: 'omit-credentials', opts: { ...opts, credentials: 'omit' } });
  }

  // Attempt 3: force https if url is http
  try {
    const parsed = new URL(url);
    if (parsed.protocol === 'http:') {
      parsed.protocol = 'https:';
      attempts.push({ label: 'https-upgrade', url: parsed.toString(), opts });
    }
  } catch (_) { /* ignore */ }

  let lastErr = null;
  for (const attempt of attempts) {
    const attemptUrl = attempt.url || url;
    console.log('[Background] safeFetch attempt', {
      url: attemptUrl,
      attempt: attempt.label,
      credentials: attempt.opts.credentials,
      hasHeaders: !!attempt.opts.headers
    });
    try {
      const res = await fetch(attemptUrl, attempt.opts);
      if (attempt.label !== 'default') {
        console.warn('[Background] Fetch succeeded after retry', { url: attemptUrl, attempt: attempt.label });
      }
      return res;
    } catch (err) {
      lastErr = err;
      console.warn('[Background] Fetch attempt failed', {
        url: attemptUrl,
        attempt: attempt.label,
        credentials: attempt.opts.credentials,
        headers: !!attempt.opts.headers,
        message: err?.message || String(err)
      });
    }
  }

  throw new Error(`Network fetch failed for ${host}: ${lastErr?.message || lastErr}`);
}

function mergeHeaders(base, extra) {
  const merged = new Headers();
  const appendAll = (hdrs) => {
    if (!hdrs) return;
    if (hdrs instanceof Headers) {
      hdrs.forEach((v, k) => merged.set(k, v));
    } else {
      Object.entries(hdrs).forEach(([k, v]) => {
        if (v != null) merged.set(k, v);
      });
    }
  };
  appendAll(base);
  appendAll(extra);
  return merged;
}

async function fetchWithBackoff(url, opts, retries = 4, delayMs = 1500) {
  let attempt = 0;
  let lastRes = null;
  let lastErr = null;
  while (attempt <= retries) {
    try {
      const res = await safeFetch(url, opts);
      lastRes = res;
      if (res.ok || res.status === 206) return res;
      if (res.status === 429 && attempt < retries) {
        const backoff = delayMs * (attempt + 1);
        await new Promise(r => setTimeout(r, backoff + Math.floor(Math.random() * 400)));
        attempt += 1;
        continue;
      }
      return res;
    } catch (err) {
      lastErr = err;
      if (attempt >= retries) throw err;
      const backoff = delayMs * (attempt + 1);
      await new Promise(r => setTimeout(r, backoff + Math.floor(Math.random() * 300)));
      attempt += 1;
    }
  }
  if (lastErr) throw lastErr;
  return lastRes;
}

async function loadWorkerScript(url) {
  if (!url) throw new Error('Missing script URL');
  if (typeof importScripts !== 'function') {
    throw new Error('importScripts unavailable for worker script load');
  }
  importScripts(url);
}

// Defensive helper: try importScripts first, then fall back to fetch + Blob if parsing fails
async function importScriptSafe(url, label = '') {
  if (!url) throw new Error('Missing script URL');
  const display = label || url;
  try {
    importScripts(url);
    return true;
  } catch (err) {
    console.warn(`[Background] importScripts failed for ${display}:`, err?.message || err);
  }
  try {
    const res = await fetch(url, { cache: 'no-store' });
    if (!res.ok) throw new Error(`HTTP ${res.status} ${res.statusText}`);
    const code = await res.text();
    const blobUrl = URL.createObjectURL(new Blob([code], { type: 'text/javascript' }));
    try {
      importScripts(blobUrl);
      console.log(`[Background] Loaded ${display} via fetch fallback`);
      return true;
    } finally {
      URL.revokeObjectURL(blobUrl);
    }
  } catch (err2) {
    console.error(`[Background] Fallback import failed for ${display}:`, err2?.message || err2);
    const enriched = new Error(`Failed to load ${display}: ${err2?.message || err2}`);
    enriched.cause = err2;
    throw enriched;
  }
}

/**
 * Ensure FFmpeg factory (createFFmpeg) is available without depending on CDN.
 */
async function ensureFfmpegFactory() {
  const wireUpWasmShim = () => {
    if (!self.createFFmpeg && self.FFmpegWASM?.FFmpeg) {
      // Some builds expose FFmpeg under FFmpegWASM only; create a compatible factory.
      self.FFmpeg = self.FFmpegWASM;
      self.createFFmpeg = (opts = {}) => new self.FFmpegWASM.FFmpeg(opts);
    }
    return self.createFFmpeg || (self.FFmpeg && self.FFmpeg.createFFmpeg);
  };

  let factory = self.createFFmpeg || (self.FFmpeg && self.FFmpeg.createFFmpeg) || wireUpWasmShim();
  if (factory) return factory;

  const tryLoad = async (url, label) => {
    if (!url) return;
    try {
      const canUseImportScripts = typeof importScripts === 'function' && (url.startsWith('chrome-extension://') || url.startsWith('assets/lib/'));
      if (canUseImportScripts) {
        // Some ffmpeg builds expect DOM globals; stub minimal document/window for worker context.
        if (typeof document === 'undefined' || !self.document) {
          self.document = { baseURI: self.location?.href || '', currentScript: null };
        }
        if (typeof window === 'undefined' || !self.window) {
          self.window = self;
        }
        await importScriptSafe(url, label || url);
      } else {
        if (typeof document === 'undefined' && !self.document) {
          // Some FFmpeg builds expect document to exist; stub it for worker context.
          self.document = { baseURI: self.location?.href || '', currentScript: null };
        }
        await importScriptSafe(url, label || url);
      }
      factory = self.createFFmpeg || (self.FFmpeg && self.FFmpeg.createFFmpeg) || wireUpWasmShim();
      if (factory) {
        console.log(`[Background] FFmpeg loader ready via ${label}`);
      }
    } catch (err) {
      console.warn(`[Background] Failed to load FFmpeg loader from ${label}:`, err?.message || err);
    }
  };

  // Prefer bundled loader (works in module service workers too).
  if (chrome?.runtime?.getURL) {
    await tryLoad(chrome.runtime.getURL('assets/lib/ffmpeg.js'), 'bundled ffmpeg.js');
  }

  if (!factory && typeof importScripts === 'function') {
    await tryLoad('assets/lib/ffmpeg.js', 'importScripts(ffmpeg.js)');
  }

  if (!factory) {
    throw new Error('FFmpeg loader unavailable. Ensure assets/lib/ffmpeg.js is bundled with the extension.');
  }

  return factory;
}

async function ensureTransferHelper() {
  if (self.SubMakerTransfer) return self.SubMakerTransfer;
  if (_transferHelperError) {
    throw new Error(`IDB transfer helper unavailable: ${_transferHelperError?.message || _transferHelperError}`);
  }
  const url = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/idb-transfer.js') : 'assets/lib/idb-transfer.js';
  if (typeof importScripts !== 'function') {
    throw new Error('IDB transfer helper unavailable (no importScripts)');
  }
  await importScriptSafe(url, 'idb-transfer.js');
  if (!self.SubMakerTransfer) {
    throw new Error('IDB transfer helper failed to load');
  }
  return self.SubMakerTransfer;
}

// ---------- Whisper WASM helpers ----------
async function ensureWhisperModule(ctx = null) {
  if (whisperModuleReady) return whisperModuleReady;

  whisperModuleReady = new Promise((resolve, reject) => {
    try {
      if (!WHISPER_EVAL_ALLOWED) {
        const err = new Error(`Whisper unavailable: ${WHISPER_EVAL_REASON || 'eval blocked by CSP'}`);
        if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, err.message, 'error');
        whisperModuleReady = null;
        throw err;
      }
      const isModuleReady = () => typeof Module !== 'undefined' && typeof Module.init === 'function';
      const loadWhisperScript = () => {
        if (typeof importScripts !== 'function') {
          throw new Error('Whisper loader unavailable (no importScripts)');
        }
        return importScriptSafe(WHISPER_JS_URL, 'whisper-main.js');
        _whisperPreloaded = true;
      };

      // Configure Module before loading script (merge, don't overwrite).
      self.Module = self.Module || {};
      const m = self.Module;
      m.print = m.print || ((...args) => console.log('[Whisper]', ...args));
      m.printErr = m.printErr || ((...args) => console.error('[Whisper]', ...args));
      m.locateFile = m.locateFile || ((path) => chrome.runtime.getURL('assets/lib/' + path));

      const waitReady = () => {
        if (typeof Module !== 'undefined' && Module.calledRun) {
          resolve(Module);
        } else if (typeof Module !== 'undefined' && Module.onRuntimeInitialized) {
          Module.onRuntimeInitialized = () => resolve(Module);
        } else {
          setTimeout(waitReady, 50);
        }
      };

      const start = async () => {
        if (_whisperPreloadError) {
          const err = new Error(`Whisper preload failed: ${_whisperPreloadError?.message || _whisperPreloadError}`);
          if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, err.message, 'error');
          throw err;
        }

        // If preload ran but Module is missing bindings, reload once.
        if (_whisperPreloaded && !isModuleReady()) {
          console.warn('[Background] Whisper preloaded but bindings missing; reloading script');
          if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, 'Whisper bindings missing; reloading whisper-main.js', 'warn');
          await loadWhisperScript();
        } else if (!_whisperPreloaded) {
          await loadWhisperScript();
        }

        if (!isModuleReady()) {
          // Wait for runtime init
          waitReady();
          return;
        }

        waitReady();
      };

      start().catch((err) => {
        whisperModuleReady = null;
        reject(err);
      });
    } catch (err) {
      whisperModuleReady = null;
      reject(err);
    }
  });

  return whisperModuleReady;
}

async function ensureWhisperModelLoaded(ctx = null) {
  const module = await ensureWhisperModule(ctx);
  if (!module || typeof module.init !== 'function') {
    whisperModuleReady = null; // allow a clean retry
    throw new Error('Whisper module not initialized (init missing)');
  }
  if (whisperInstance) return whisperInstance;

  const resp = await fetch(WHISPER_MODEL_URL);
  if (!resp.ok) throw new Error(`Failed to load Whisper model: ${resp.status}`);

  const buffer = new Uint8Array(await resp.arrayBuffer());
  try {
    module.FS_unlink('/' + WHISPER_MODEL_FILE);
  } catch (_) {
    /* ignore */
  }
  module.FS_createDataFile('/', WHISPER_MODEL_FILE, buffer, true, true);

  let instanceIndex = null;
  try {
    instanceIndex = module.init(WHISPER_MODEL_FILE);
  } catch (initErr) {
    // Reset so a subsequent attempt can reload the module if bindings were incomplete.
    whisperModuleReady = null;
    const msg = initErr?.message || String(initErr);
    throw new Error(`Whisper init failed: ${msg}`);
  }
  if (!instanceIndex) {
    throw new Error('Whisper init failed (no instance)');
  }

  whisperInstance = instanceIndex;
  console.log('[Whisper] Model loaded and instance ready');
  return whisperInstance;
}

function decodeWavToFloat32(arrayBuffer) {
  const view = new DataView(arrayBuffer);
  if (view.byteLength < 44) {
    throw new Error(`Invalid WAV: buffer too small (${view.byteLength} bytes)`);
  }
  if (view.getUint32(0, false) !== 0x52494646) {
    throw new Error('Invalid WAV: missing RIFF');
  }
  if (view.getUint32(8, false) !== 0x57415645) {
    throw new Error('Invalid WAV: missing WAVE');
  }

  let offset = 12;
  let audioFormat = 1;
  let numChannels = 1;
  let sampleRate = 16000;
  let bitsPerSample = 16;
  let dataOffset = -1;
  let dataSize = 0;

  while (offset < view.byteLength) {
    const chunkId = view.getUint32(offset, false);
    const chunkSize = view.getUint32(offset + 4, true);
    const chunkStart = offset + 8;

    if (chunkId === 0x666d7420) {
      audioFormat = view.getUint16(chunkStart, true);
      numChannels = view.getUint16(chunkStart + 2, true);
      sampleRate = view.getUint32(chunkStart + 4, true);
      bitsPerSample = view.getUint16(chunkStart + 14, true);
    } else if (chunkId === 0x64617461) {
      dataOffset = chunkStart;
      dataSize = chunkSize;
      break;
    }

    offset = chunkStart + chunkSize;
  }

  if (dataOffset < 0) throw new Error('Invalid WAV: missing data');
  if (audioFormat !== 1) throw new Error('Unsupported WAV format (not PCM)');
  if (numChannels !== 1) throw new Error('Only mono audio supported for Whisper');

  const bytesPerSample = bitsPerSample / 8;
  const sampleCount = dataSize / bytesPerSample;
  const pcm = new Float32Array(sampleCount);

  for (let i = 0; i < sampleCount; i++) {
    const value = bitsPerSample === 16
      ? view.getInt16(dataOffset + i * 2, true) / 32768
      : view.getInt8(dataOffset + i) / 128;
    pcm[i] = value;
  }

  return { pcm, sampleRate };
}

function resampleTo16kHz(pcm, inputRate) {
  if (inputRate === 16000) return pcm;
  const ratio = 16000 / inputRate;
  const newLength = Math.floor(pcm.length * ratio);
  const out = new Float32Array(newLength);
  for (let i = 0; i < newLength; i++) {
    const srcPos = i / ratio;
    const srcIdx = Math.floor(srcPos);
    const frac = srcPos - srcIdx;
    const next = srcIdx + 1 < pcm.length ? pcm[srcIdx + 1] : pcm[srcIdx];
    out[i] = pcm[srcIdx] * (1 - frac) + next * frac;
  }
  return out;
}

function limitAudioByMode(pcm, sampleRate, mode) {
  // Single mode: keep full audio (no trimming)
  const limits = { single: 0 };
  const seconds = limits[mode] ?? 0;
  if (!seconds || seconds <= 0) return pcm;
  const maxSamples = seconds * sampleRate;
  return pcm.length <= maxSamples ? pcm : pcm.subarray(0, maxSamples);
}

function parseWhisperSegments(logLines) {
  const segments = [];
  const timeRe = /\\[(\\d+):(\\d+):(\\d+\\.\\d+)\\s+-->\\s+(\\d+):(\\d+):(\\d+\\.\\d+)\\]\\s*(.*)/;
  for (const line of logLines) {
    const m = line.match(timeRe);
    if (!m) continue;
    const [_, sh, sm, ss, eh, em, es, text] = m;
    const toMs = (h, m, s) => (parseInt(h, 10) * 3600 + parseInt(m, 10) * 60 + parseFloat(s)) * 1000;
    segments.push({
      startMs: toMs(sh, sm, ss),
      endMs: toMs(eh, em, es),
      text: (text || '').trim(),
    });
  }
  return segments;
}

function normalizeText(txt) {
  return String(txt || '')
    .toLowerCase()
    .replace(/[^\\p{L}\\p{N}\\s]/gu, ' ')
    .replace(/\\s+/g, ' ')
    .trim();
}

function tokenSimilarity(aTokens, bTokens) {
  if (!aTokens.length || !bTokens.length) return 0;
  const setA = new Set(aTokens);
  const setB = new Set(bTokens);
  let inter = 0;
  for (const t of setA) {
    if (setB.has(t)) inter += 1;
  }
  return inter / Math.max(setA.size, setB.size);
}

function robustTimelineTransform(matches) {
  if (!matches.length) return { slope: 1, intercept: 0 };

  const fit = (pts) => {
    let sumX = 0, sumY = 0, sumXY = 0, sumXX = 0;
    for (const { source, target } of pts) {
      sumX += source;
      sumY += target;
      sumXY += source * target;
      sumXX += source * source;
    }
    const n = pts.length;
    const denom = n * sumXX - sumX * sumX;
    if (Math.abs(denom) < 1e-6) {
      const offset = (sumY / n) - (sumX / n);
      return { slope: 1, intercept: offset };
    }
    const slope = (n * sumXY - sumX * sumY) / denom;
    const intercept = (sumY - slope * sumX) / n;
    return { slope, intercept };
  };

  let current = [...matches];
  for (let iter = 0; iter < 3; iter++) {
    const model = fit(current);
    const residuals = current.map(m => Math.abs(m.target - (model.slope * m.source + model.intercept)));
    const median = residuals.slice().sort((a, b) => a - b)[Math.floor(residuals.length / 2)] || 0;
    const mad = residuals.map(r => Math.abs(r - median)).sort((a, b) => a - b)[Math.floor(residuals.length / 2)] || 1;
    const threshold = Math.max(1500, median + 4 * mad);
    const filtered = current.filter((m, idx) => residuals[idx] <= threshold);
    if (filtered.length < 4) break;
    current = filtered;
  }

  return fit(current);
}

function alignSubtitlesWithTranscript(subtitleContent, transcriptSegments) {
  const subtitles = parseSRT(subtitleContent);
  if (!subtitles.length) {
    throw new Error('No subtitles to align');
  }

  const matches = [];
  const transcriptTokens = transcriptSegments.map(seg => normalizeText(seg.text).split(' ').filter(Boolean));
  let transcriptIdx = 0;
  const stride = Math.max(1, Math.floor(subtitles.length / 320)); // downsample for very long subs

  for (let i = 0; i < subtitles.length; i++) {
    const sub = subtitles[i];
    const subTokens = normalizeText(sub.text).split(' ').filter(Boolean);
    if (!subTokens.length) continue;
    if (i % stride !== 0 && matches.length > 0) continue;

    // Primary search window near last match
    let best = { score: 0, idx: transcriptIdx };
    const primaryStart = Math.max(0, transcriptIdx - 20);
    const primaryEnd = Math.min(transcriptSegments.length, transcriptIdx + 80);
    for (let j = primaryStart; j < primaryEnd; j++) {
      const sim = tokenSimilarity(subTokens, transcriptTokens[j]);
      if (sim > best.score) best = { score: sim, idx: j };
    }

    // Wider search every 10th subtitle to escape ads/drifts
    if (best.score < 0.24 && i % 10 === 0) {
      const wideStart = Math.max(0, transcriptIdx - 80);
      const wideEnd = Math.min(transcriptSegments.length, transcriptIdx + 200);
      for (let j = wideStart; j < wideEnd; j++) {
        const sim = tokenSimilarity(subTokens, transcriptTokens[j]);
        if (sim > best.score) best = { score: sim, idx: j };
      }
    }

    if (best.score >= 0.22) {
      matches.push({
        source: sub.start,
        target: transcriptSegments[best.idx].startMs,
        score: best.score,
      });
      transcriptIdx = best.idx;
    }
  }

  // Ensure anchors near start and end
  if (matches.length >= 2) {
    const first = transcriptSegments[0];
    const last = transcriptSegments[transcriptSegments.length - 1];
    matches.unshift({ source: subtitles[0].start, target: first.startMs, score: 1 });
    matches.push({ source: subtitles[subtitles.length - 1].start, target: last.startMs, score: 1 });
  }

  if (matches.length < 8) {
    throw new Error('Insufficient matches for alignment');
  }

  const globalModel = robustTimelineTransform(matches);

  // Piecewise drift correction for bitrate changes/ads/scene cuts
  const totalDuration = subtitles[subtitles.length - 1].end || matches[matches.length - 1].source || 0;
  const chunkSize = Math.max(6 * 60 * 1000, totalDuration / 8);

  const rebuilt = subtitles.map((sub, i) => {
    const chunkIndex = Math.floor(sub.start / chunkSize);
    const localAnchors = matches.filter(m => Math.floor(m.source / chunkSize) === chunkIndex);
    const model = localAnchors.length >= 3 ? robustTimelineTransform(localAnchors) : globalModel;

    const newStart = Math.max(0, model.slope * sub.start + model.intercept);
    const duration = Math.max(0, sub.end - sub.start);
    const newEnd = Math.max(newStart, model.slope * (sub.end) + model.intercept || newStart + duration);
    return {
      ...sub,
      start: newStart,
      end: newEnd,
      index: i + 1,
    };
  });

  let result = '';
  for (const sub of rebuilt) {
    result += `${sub.index}\\n`;
    result += `${formatTime(sub.start)} --> ${formatTime(sub.end)}\\n`;
    result += sub.text.trim() + '\\n\\n';
  }
  return result.trim();
}

async function transcribeWithWhisper(pcm, sampleRate, mode, offsetMs = 0, onProgress, ctx = null) {
  if (!WHISPER_EVAL_ALLOWED) {
    const err = new Error(`Whisper unavailable due to CSP (${WHISPER_EVAL_REASON || 'unsafe-eval blocked'})`);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, err.message, 'error');
    }
    throw err;
  }
  if (whisperBusy) throw new Error('Another Whisper job is running');
  whisperBusy = true;
  try {
    onProgress?.(60, 'Loading Whisper (WASM) ...');
    await ensureWhisperModelLoaded(ctx);

    const module = await ensureWhisperModule(ctx);
    const readyPcm = limitAudioByMode(resampleTo16kHz(pcm, sampleRate), 16000, mode);
    const threads = Math.min(8, Math.max(2, (navigator?.hardwareConcurrency || 4)));

    const logs = [];
    const originalPrint = module.print;
    module.print = (...args) => {
      const line = args.join(' ');
      logs.push(line);
      if (logs.length > 5000) {
        logs.splice(0, logs.length - 5000);
      }
      console.log('[Whisper]', line);
    };

    const durationSec = pcm.length / sampleRate;
    const ctxLabel = ctx?.messageId ? `job ${ctx.messageId}` : '';
    console.log('[Whisper] Starting transcription', { durationSec: Math.round(durationSec * 10) / 10, sampleRate, offsetMs, ctx: ctxLabel });
    onProgress?.(72, 'Transcribing audio with Whisper...');
    const ret = module.full_default(whisperInstance, readyPcm, 'en', threads, false);
    if (ret !== 0) {
      throw new Error(`Whisper returned code ${ret}`);
    }

    // Wait for output to settle (no new logs for ~1.5s or max 10 minutes)
    const startTime = Date.now();
    let stableCount = 0;
    let lastSize = logs.length;
    while (stableCount < 3) {
      await new Promise((resolve) => setTimeout(resolve, 500));
      if (logs.length === lastSize) {
        stableCount += 1;
      } else {
        stableCount = 0;
        lastSize = logs.length;
      }
      if (Date.now() - startTime > 600000) break;
    }
    module.print = originalPrint;

    const segments = parseWhisperSegments(logs);
    if (!segments.length) {
      throw new Error('Whisper produced no segments');
    }
    const shifted = segments.map(s => ({
      ...s,
      startMs: s.startMs + offsetMs,
      endMs: s.endMs + offsetMs
    }));
    onProgress?.(85, `Parsed ${segments.length} transcript segments`);
    return shifted;
  } catch (err) {
    const durationSec = pcm.length / sampleRate;
    console.error('[Whisper] Transcription failed', { message: err?.message, stack: err?.stack, durationSec, sampleRate, offsetMs });
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Whisper transcription failed (${err?.message || err}) [duration=${Math.round(durationSec * 10) / 10}s, offset=${offsetMs}ms]`, 'error');
    }
    throw err;
  } finally {
    whisperBusy = false;
  }
}

async function transcribeAudioWindows(audioWindows, mode, onProgress, ctx = null) {
  if (!Array.isArray(audioWindows) || !audioWindows.length) {
    throw new Error('No audio windows to transcribe');
  }

  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };

  const transcript = [];
  for (let i = 0; i < audioWindows.length; i++) {
    const win = audioWindows[i];
    const startedAt = Date.now();
    let audioData = null;
    try {
      audioData = await win.audioBlob.arrayBuffer();
      const { pcm, sampleRate } = decodeWavToFloat32(audioData);
      const startOffset = win.startMs || 0;
      const share = Math.max(1, Math.floor(40 / audioWindows.length));
      const durationSec = pcm.length / sampleRate;
      console.log('[Background] Transcribing window', {
        idx: i + 1,
        total: audioWindows.length,
        durationSec: Math.round(durationSec * 10) / 10,
        sampleRate,
        startOffset
      });
      onProgress?.(20 + i * share, `Transcribing window ${i + 1}/${audioWindows.length}...`);
      logToPage(`Transcribing window ${i + 1}/${audioWindows.length} (duration ~${Math.round(durationSec * 10) / 10}s, start=${startOffset}ms)`, 'info');
      const segs = await transcribeWithWhisper(pcm, sampleRate, mode, startOffset, (pct, status) => {
        onProgress?.(20 + i * share + (pct * share) / 100, status);
      }, ctx);
      transcript.push(...segs);
      logToPage(`Window ${i + 1} produced ${segs.length} segment(s) in ${Date.now() - startedAt}ms`, 'info');
    } catch (err) {
      const sizeKb = audioData ? Math.round(audioData.byteLength / 1024) : 0;
      const reason = err?.message || String(err);
      console.error('[Background] Failed to transcribe window', i + 1, { reason, sizeKb });
      logToPage(`Transcription failed on window ${i + 1}/${audioWindows.length}: ${reason} (size ~${sizeKb}KB)`, 'error');
      const enriched = new Error(`Window ${i + 1} transcription failed: ${reason}`);
      enriched.cause = err;
      throw enriched;
    }
  }

  transcript.sort((a, b) => a.startMs - b.startMs);
  return transcript;
}

function formatTimestampForSrt(seconds = 0) {
  const clamped = Math.max(0, Number(seconds) || 0);
  const hrs = Math.floor(clamped / 3600);
  const mins = Math.floor((clamped % 3600) / 60);
  const secs = Math.floor(clamped % 60);
  const ms = Math.floor((clamped - Math.floor(clamped)) * 1000);
  const pad = (v, len = 2) => String(v).padStart(len, '0');
  return `${pad(hrs)}:${pad(mins)}:${pad(secs)},${pad(ms, 3)}`;
}

function segmentsToSrt(segments = []) {
  if (!Array.isArray(segments) || segments.length === 0) return '';
  const lines = [];
  segments.forEach((seg, idx) => {
    const start = formatTimestampForSrt(seg.start || seg.start_time || 0);
    const end = formatTimestampForSrt(seg.end || seg.end_time || (Number(seg.start || 0) + 4));
    const text = (seg.text || seg.transcript || '').toString().trim() || '[...]';
    lines.push(String(idx + 1));
    lines.push(`${start} --> ${end}`);
    lines.push(text);
    lines.push('');
  });
  return lines.join('\n');
}

async function runCloudflareTranscription(audioBlob, opts = {}, ctx = null) {
  const accountId = (opts.accountId || '').trim();
  const token = (opts.token || '').trim();
  if (!accountId || !token) {
    throw new Error('Cloudflare Workers AI credentials are missing');
  }
  const model = (opts.model || '@cf/openai/whisper').trim();
  const endpoint = `https://api.cloudflare.com/client/v4/accounts/${accountId}/ai/run/${encodeURI(model)}`;
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), 60000);
  const audioBuffer = await audioBlob.arrayBuffer();
  const contentType = audioBlob?.type || 'audio/wav';
  let response;
  let raw = '';
  let attemptedJson = false;
  const mustUseJson = opts.forceJson === true || !!opts.sourceLanguage || opts.diarization === true;
  const sendBinary = async () => {
    response = await fetch(endpoint, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${token}`,
        Accept: 'application/json',
        'Content-Type': contentType
      },
      body: audioBuffer,
      signal: controller.signal
    });
    raw = await response.text();
  };
  const sendJsonArray = async () => {
    attemptedJson = true;
    const payload = {
      audio: Array.from(new Uint8Array(audioBuffer))
    };
    if (opts.sourceLanguage) payload.language = opts.sourceLanguage;
    if (opts.diarization) payload.diarization = true;
    response = await fetch(endpoint, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${token}`,
        Accept: 'application/json',
        'Content-Type': 'application/json'
      },
      body: JSON.stringify(payload),
      signal: controller.signal
    });
    raw = await response.text();
  };

  try {
    // Cloudflare's /ai/run whisper endpoint expects either raw binary audio or a JSON array payload.
    // Multipart form uploads are not accepted and lead to "Invalid audio input" errors.
    if (mustUseJson) {
      await sendJsonArray();
    } else {
      await sendBinary();
      if (!response?.ok) {
        const bodyLower = (raw || '').toLowerCase();
        const retryable =
          response.status === 415 ||
          response.status === 400 ||
          bodyLower.includes('invalid audio') ||
          bodyLower.includes('unsupported audio input') ||
          bodyLower.includes('different language') ||
          bodyLower.includes('language');
        if (retryable && !attemptedJson) {
          await sendJsonArray();
        }
      }
    }
  } catch (err) {
    clearTimeout(timer);
    if (err?.name === 'AbortError') {
      throw new Error('Cloudflare transcription timed out');
    }
    throw new Error(err?.message || 'Cloudflare request failed');
  }
  clearTimeout(timer);
  let data = null;
  try {
    data = raw ? JSON.parse(raw) : null;
  } catch (_) {
    data = null;
  }
  if (!response?.ok) {
    const cfMessage =
      data?.errors?.[0]?.message ||
      data?.result?.errors?.[0]?.message ||
      data?.error ||
      data?.message ||
      (raw ? raw.slice(0, 400) : '');
    const error = new Error(cfMessage || `Cloudflare Workers AI request failed (${response?.status || 'n/a'})`);
    error.cfStatus = response?.status || null;
    error.cfBody = raw || '';
    throw error;
  }
  const result = data?.result || data?.data || data;
  const segments = Array.isArray(result?.segments) ? result.segments : [];
  const language = result?.language || result?.detected_language || result?.detectedLanguage || '';
  return {
    segments,
    language,
    status: response?.status || null,
    raw: result,
    cfBody: raw ? raw.slice(0, 400) : ''
  };
}

async function transcribeWindowsWithCloudflare(audioWindows, opts = {}, onProgress, ctx = null) {
  if (!Array.isArray(audioWindows) || !audioWindows.length) {
    throw new Error('No audio windows to transcribe');
  }
  if (ctx?.tabId) {
    const totalBytes = audioWindows.reduce((sum, w) => sum + (w?.audioBlob?.size || 0), 0);
    sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare transcription starting (${audioWindows.length} window(s), totalBytes=${totalBytes})`, 'info');
  }
  const allSegments = [];
  let lastStatus = null;
  let lastBody = '';
  let detectedLang = '';
  let forcedLang = (opts.sourceLanguage || '').trim() || null;
  const langCandidates = Array.from(new Set(['en', 'ja'])); // common alternates for mixed content
  const totalBytes = audioWindows.reduce((sum, w) => sum + (w?.audioBlob?.size || 0), 0);
  const CF_MAX_WAV_BYTES = 4 * 1024 * 1024; // Guard below observed effective limit despite docs quoting higher
  audioWindows.forEach((win, idx) => {
    const size = win?.audioBlob?.size || 0;
    if (size > CF_MAX_WAV_BYTES) {
      const mb = Math.round((size / (1024 * 1024)) * 10) / 10;
      throw new Error(`Audio window ${idx + 1} is too large for Cloudflare (~${mb} MB > ~5 MB limit); use shorter windows.`);
    }
  });
  // Detect language on the first window if not provided
  let startIdx = 0;
  if (!forcedLang && audioWindows.length) {
    const firstWin = audioWindows[0];
    const offsetSec = Number(firstWin?.startMs || 0) / 1000;
    onProgress?.(15, `Detecting language on window 1/${audioWindows.length}...`);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare (detect): window 1/${audioWindows.length}, offset=${Math.round(offsetSec * 1000) / 1000}s, size=${firstWin?.audioBlob?.size || 0} bytes`, 'info');
    }
    let detectRes = null;
    let langAttemptIdx = 0;
    try {
      detectRes = await runCloudflareTranscription(firstWin.audioBlob, {
        accountId: opts.accountId,
        token: opts.token,
        model: opts.model,
        sourceLanguage: undefined,
        diarization: opts.diarization,
        filename: opts.filename ? `${opts.filename}_1.wav` : `audio_1.wav`
      }, ctx);
    } catch (err) {
      const msg = (err?.message || '').toLowerCase();
      const needsForcedLang = msg.includes('different language') || msg.includes('unsupported audio input') || msg.includes('language');
      const fallbackLang = langCandidates[langAttemptIdx] || 'en';
      if (needsForcedLang) {
        if (ctx?.tabId) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare detect failed (${err?.message || err}); retrying with forced language=${fallbackLang}`, 'warn');
        }
        forcedLang = fallbackLang;
        let lastErr = err;
        while (langAttemptIdx < langCandidates.length) {
          const lang = langCandidates[langAttemptIdx];
          langAttemptIdx += 1;
          try {
            detectRes = await runCloudflareTranscription(firstWin.audioBlob, {
              accountId: opts.accountId,
              token: opts.token,
              model: opts.model,
              sourceLanguage: lang,
              diarization: opts.diarization,
              filename: opts.filename ? `${opts.filename}_1.wav` : `audio_1.wav`,
              forceJson: true // ensure language is honored
            }, ctx);
            forcedLang = lang;
            break;
          } catch (langErr) {
            lastErr = langErr;
            if (ctx?.tabId) {
              sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare detect retry failed for lang=${lang}: ${langErr?.message || langErr}`, 'warn');
            }
          }
        }
        if (!detectRes) {
          throw lastErr || err;
        }
      } else {
        throw err;
      }
    }
    lastStatus = detectRes.status || lastStatus;
    lastBody = detectRes.cfBody || lastBody;
    detectedLang = detectRes.language || '';
    forcedLang = detectRes.language || forcedLang || null;
    const segs = Array.isArray(detectRes.segments) ? detectRes.segments : [];
    const adjusted = segs.map((seg) => ({
      ...seg,
      start: (seg.start || seg.start_time || 0) + offsetSec,
      end: (seg.end || seg.end_time || (Number(seg.start || 0) + 4)) + offsetSec
    }));
    allSegments.push(...adjusted);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare detect complete (${segs.length} segments, lang=${detectRes.language || 'n/a'})`, 'info');
      if (!segs.length) {
        sendDebugLog(ctx.tabId, ctx.messageId, 'First window returned no segments; retrying with per-window autodetect for all windows.', 'warn');
      }
    }
    // If detection produced no segments, retry window 1 in the main loop so it also benefits from the per-window autodetect order.
    startIdx = segs.length ? 1 : 0;
  }

  if (!forcedLang) {
    // Fallback to user-provided hint if detection failed
    forcedLang = (opts.sourceLanguage || '').trim() || null;
  }

  for (let i = startIdx; i < audioWindows.length; i++) {
    const win = audioWindows[i];
    const offsetSec = Number(win?.startMs || 0) / 1000;
    onProgress?.(15 + ((i / audioWindows.length) * 50), `Transcribing window ${i + 1}/${audioWindows.length}...`);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare: window ${i + 1}/${audioWindows.length}, offset=${Math.round(offsetSec * 1000) / 1000}s, size=${win?.audioBlob?.size || 0} bytes`, 'info');
    }
    const langOrder = (() => {
      const order = [];
      const seen = new Set();
      const push = (lang) => {
        const key = lang || 'auto';
        if (seen.has(key)) return;
        order.push(lang);
        seen.add(key);
      };
      // Always allow Cloudflare to auto-detect per window before falling back to hints.
      push(forcedLang || null);
      push(null);
      langCandidates.forEach(push);
      return order;
    })();
    let res = null;
    let lastErr = null;
    for (const lang of langOrder) {
      try {
        res = await runCloudflareTranscription(win.audioBlob, {
          accountId: opts.accountId,
          token: opts.token,
          model: opts.model,
          sourceLanguage: lang || undefined,
          diarization: opts.diarization,
          filename: opts.filename ? `${opts.filename}_${i + 1}.wav` : `audio_${i + 1}.wav`,
          forceJson: !!lang
        }, ctx);
        forcedLang = lang || forcedLang; // stick with the last successful language (still allow auto attempts next window)
        break;
      } catch (err) {
        lastErr = err;
        const msg = (err?.message || '').toLowerCase();
        const needsSwitch = msg.includes('different language') || msg.includes('unsupported audio input') || msg.includes('language');
        if (!needsSwitch) {
          throw err;
        }
        if (ctx?.tabId) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare window ${i + 1} failed for lang=${lang || 'auto'}: ${err?.message || err}`, 'warn');
        }
      }
    }
    if (!res) {
      throw lastErr || new Error('Cloudflare transcription failed for all language attempts');
    }
    lastStatus = res.status || lastStatus;
    lastBody = res.cfBody || lastBody;
    detectedLang = res.language || detectedLang || forcedLang || '';
    const segs = Array.isArray(res.segments) ? res.segments : [];
    const adjusted = segs.map((seg) => ({
      ...seg,
      start: (seg.start || seg.start_time || 0) + offsetSec,
      end: (seg.end || seg.end_time || (Number(seg.start || 0) + 4)) + offsetSec
    }));
    allSegments.push(...adjusted);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare window ${i + 1} complete (${segs.length} segments, offset=${offsetSec.toFixed(3)}s, lang=${res.language || forcedLang || 'n/a'})`, 'info');
    }
  }
  allSegments.sort((a, b) => (a.start || 0) - (b.start || 0));
  onProgress?.(70, 'Building transcript...');
  const srt = segmentsToSrt(allSegments);
  if (ctx?.tabId) {
    sendDebugLog(ctx.tabId, ctx.messageId, `Cloudflare transcription complete (${allSegments.length} segments, lang=${detectedLang || opts.sourceLanguage || 'und'}, status=${lastStatus || 'n/a'})`, 'info');
  }
  return {
    srt,
    languageCode: detectedLang || opts.sourceLanguage || 'und',
    segmentCount: allSegments.length,
    cfStatus: lastStatus,
    cfBody: lastBody,
    model: opts.model || '@cf/openai/whisper',
    audioBytes: totalBytes,
    audioSource: 'extension',
    contentType: 'audio/wav'
  };
}

/**
 * Handle messages from content script
 */
function __xsyncHandleMessage(message, sender, sendResponse) {
  const reply = (payload) => {
    try {
      sendResponse?.(payload);
    } catch (err) {
      console.error('[Background] Failed to send response:', err?.message || err);
    }
  };

  try {
    const nowTs = Date.now();
    console.log('[Background] Received message:', {
      type: message?.type,
      messageId: message?.messageId,
      fromTab: sender?.tab?.id,
      frameId: sender?.frameId,
      hasPayload: !!message,
      recvTs: nowTs
    });

    if (message?.type === 'RESET_EMBEDDED_PAGE') {
      const cleared = cleanupExtractJobsForTab(sender?.tab?.id);
      forceCloseOffscreenDocument(message?.reason || 'page-reset')
        .catch(() => { })
        .finally(() => reply({ success: true, cleared }));
      return true;
    }

    if (message?.type === 'GET_STATUS') {
      const now = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
      console.log('[Background][Timing] GET_STATUS after boot', (now - _workerBootTs).toFixed(1), 'ms', 'wall', nowTs);
      reply({
        active: activeSyncJobs.size,
        extracting: activeExtractJobs.size
      });
      return false; // synchronous response
    }

    if (message?.type === 'SYNC_REQUEST') {
      handleSyncRequest(message, sender.tab?.id)
        .then(reply)
        .catch((error) => {
          console.error('[Background] Sync error:', error);
          reply({ success: false, error: error?.message || 'Unknown error' });
        });
      // Explicitly keep the message channel alive for the async response.
      return true;
    }

    if (message?.type === 'AUTOSUB_REQUEST') {
      if (message?.data?.useAssembly) {
        handleAssemblyAutoSubRequest(message, sender.tab?.id)
          .then(reply)
          .catch((error) => {
            console.error('[Background] Auto-sub (Assembly) error:', error);
            reply({ success: false, error: error?.message || 'Unknown error' });
          });
      } else {
        handleAutoSubRequest(message, sender.tab?.id)
          .then(reply)
          .catch((error) => {
            console.error('[Background] Auto-sub error:', error);
            reply({ success: false, error: error?.message || 'Unknown error' });
          });
      }
      return true;
    }

    if (!message?.type) {
      console.warn('[Background] Received message with no type; ignoring.');
      return false;
    }

    if (message.type === 'EXTRACT_SUBS_REQUEST') {
      console.log('[Background] Processing EXTRACT_SUBS_REQUEST:', {
        messageId: message.messageId,
        streamUrl: message.streamUrl?.substring(0, 50) + '...',
        mode: message.mode
      });
      handleExtractSubsRequest(message, sender.tab?.id, 'single')
        .then((result) => {
          console.log('[Background] Extract completed:', { success: result.success, trackCount: result.tracks?.length });
          reply(result);
        })
        .catch((error) => {
          console.error('[Background] Extract error:', error);
          const errorMsg = error?.message || 'Unknown error';
          console.error('[Background] Full error stack:', error?.stack);
          reply({ success: false, error: errorMsg });
        });
      return true;
    }

    console.warn('[Background] Unhandled message type:', message.type);
    // Do not keep the channel open for unknown messages
    return false;
  } catch (outerErr) {
    console.error('[Background] onMessage handler crashed:', outerErr?.message || outerErr);
    reply({ success: false, error: outerErr?.message || 'Background handler failed' });
    // Keep channel open only if we attempted to respond
    return true;
  }
}
// If we were loaded directly (MV3 default), register the listener here.
// When loaded via the lightweight bootstrap, that script delegates messages
// directly to __xsyncHandleMessage to avoid duplicate listeners.
if (!BOOTSTRAP_MODE) {
  chrome.runtime.onMessage.addListener(__xsyncHandleMessage);
}

/**
 * Handle sync request
 */
async function handleSyncRequest(message, tabId) {
  const { messageId, streamUrl, subtitleContent, preferAlass, preferFfsubsync, preferCtc, plan: incomingPlan, mode, pageHeaders } = message;
  const normalizedPlan = normalizeSyncPlan(incomingPlan, mode);
  const normalizedMode = 'single';
  const startedAt = Date.now();
  const syncCtx = { tabId, messageId, streamUrl, preferAlass: preferAlass === true, preferFfsubsync: preferFfsubsync === true, preferCtc: preferCtc === true, plan: normalizedPlan, pageHeaders };

  console.log('[Background] Starting sync job:', messageId);
  if (tabId) {
    sendDebugLog(tabId, messageId, 'Background received sync request', 'info');
    const host = (() => { try { return new URL(streamUrl || '').hostname; } catch (_) { return streamUrl || ''; } })();
    sendDebugLog(tabId, messageId, `Sync context: host=${host || 'n/a'}, preferAlass=${preferAlass === true}, preferFfsubsync=${preferFfsubsync === true}, preferCtc=${preferCtc === true}, subtitleSize=${subtitleContent ? subtitleContent.length : 0} chars`, 'info');
    sendDebugLog(tabId, messageId, describePlanForLog(normalizedPlan), 'info');
  }

  let lastPct = 0;
  const progressLogger = (pct, status) => {
    const normalized = Math.max(0, Math.min(100, Math.round(Number(pct) || 0)));
    const clamped = Math.max(lastPct, normalized);
    lastPct = clamped;

    let statusToSend = status;
    if (statusToSend && /%/.test(statusToSend)) {
      statusToSend = statusToSend.replace(/\d+%/, `${clamped}%`);
    }

    sendProgress(tabId, messageId, clamped, statusToSend);
    if (statusToSend) {
      sendDebugLog(tabId, messageId, statusToSend, 'info');
    }
  };

  // Store job info
  activeSyncJobs.set(messageId, {
    tabId,
    startTime: Date.now(),
    status: 'starting'
  });
  try { await incStat('activeSyncs', 1); } catch (_) { }

  try {
    // Step 1: Extract audio from stream
    progressLogger(8, `Fetching video (${normalizedMode})...`);
    const audioWindows = await extractAudioFromStream(streamUrl, normalizedPlan, (progress) => {
      const pct = 8 + (progress * 0.42);
      progressLogger(pct, `Extracting audio: ${Math.round(progress)}%`);
    }, syncCtx);
    const windowMeta = (audioWindows || []).map((w, idx) => ({
      idx: idx + 1,
      startMs: Math.round(w?.startMs || 0),
      sizeKb: Math.round((w?.audioBlob?.size || 0) / 1024)
    }));
    console.log('[Background] Audio windows ready with metadata:', windowMeta);
    if (tabId && windowMeta.length) {
      const sizes = windowMeta.map(w => (typeof w.sizeKb === 'number' ? w.sizeKb : 0));
      const sizeSummary = sizes.length ? `${Math.min(...sizes)}-${Math.max(...sizes)}KB` : 'n/a';
      const zeroCount = sizes.filter(s => s === 0).length;
      const sizeLabel = zeroCount ? `${sizeSummary} (${zeroCount} empty)` : sizeSummary;
      sendDebugLog(tabId, messageId, `Audio windows ready (${windowMeta.length}); size range ${sizeLabel}`, 'info');
    }
    if (tabId) {
      await logAudioWindowDiagnostics(audioWindows, syncCtx, normalizedPlan, 'post-extract');
    }

    let workingSubtitle = subtitleContent;

    const prepassEnabled = normalizedPlan.useFingerprintPrepass !== false && !preferFfsubsync;
    if (prepassEnabled) {
      const prepass = await runFingerprintPrepass(audioWindows, workingSubtitle, normalizedPlan, syncCtx, progressLogger);
      if (prepass?.applied && prepass.subtitleContent) {
        workingSubtitle = prepass.subtitleContent;
      }
    } else if (preferFfsubsync) {
      sendDebugLog(tabId, messageId, 'Skipping fingerprint pre-pass (ffsubsync already primary)', 'info');
    } else {
      sendDebugLog(tabId, messageId, 'Fingerprint pre-pass disabled by user', 'info');
    }

    // Step 2: Synchronize subtitle using Whisper autosync (with optional ffsubsync/alass preference)
    const prefLabel = preferCtc ? ' (Vosk CTC/DTW preferred)' : preferFfsubsync ? ' (FFSUBSYNC preferred)' : preferAlass ? ' (ALASS preferred)' : '';
    const syncStart = 60;
    const syncSpan = 40;
    progressLogger(syncStart, `Synchronizing subtitle with audio...${prefLabel}`);
    const syncedSubtitle = await synchronizeSubtitle(audioWindows, workingSubtitle, normalizedMode, (progress, status) => {
      const clamped = Math.max(0, Math.min(100, progress || 0));
      const pct = syncStart + (clamped * (syncSpan / 100));
      progressLogger(pct, status || `Syncing: ${Math.round(clamped)}%`);
    }, preferAlass === true, syncCtx, { preferFfsubsync: preferFfsubsync === true, preferCtc: preferCtc === true, ffsubsyncOptions: message.ffsubsyncOptions || {} });

    progressLogger(100, 'Sync complete!');

    // Clean up
    activeSyncJobs.delete(messageId);

    console.log('[Background] Sync job completed:', messageId, { durationMs: Date.now() - startedAt });
    if (tabId) {
      sendDebugLog(tabId, messageId, 'Sync job completed', 'info');
    }
    try {
      await incStat('totalSynced', 1);
      await incStat('activeSyncs', -1);
    } catch (_) { }

    return {
      success: true,
      syncedSubtitle: syncedSubtitle
    };

  } catch (error) {
    console.error('[Background] Sync job failed:', error, { durationMs: Date.now() - startedAt });
    if (tabId) {
      sendDebugLog(tabId, messageId, `Sync job failed: ${error?.message || error}`, 'error');
      if (error?.stack) {
        sendDebugLog(tabId, messageId, `Stack: ${String(error.stack).slice(0, 9000)}`, 'error');
      }
    }
    activeSyncJobs.delete(messageId);
    try { await incStat('activeSyncs', -1); } catch (_) { }
    lastSyncProgress.delete(messageId);

    return {
      success: false,
      error: error.message || 'Sync failed'
    };
  }
}

/**
 * Handle embedded subtitle extraction request
 */
async function handleExtractSubsRequest(message, tabId, mode) {
  const { messageId, streamUrl } = message;
  const normalizedMode = normalizeExtractMode(message.mode || mode);
  const startedAt = Date.now();
  const baseHeaders = mergeHeaders(null, message?.pageHeaders || null);

  console.log('[Background] Starting extraction job:', { messageId, streamUrl: streamUrl?.substring(0, 60), mode: normalizedMode });
  const activeForTab = tabId ? [...activeExtractJobs.values()].filter((job) => job?.tabId === tabId).length : 0;
  if (activeForTab >= MAX_EMBEDDED_EXTRACTS_PER_TAB) {
    const err = 'Only one embedded extraction is allowed per tab. Wait for the current run to finish.';
    sendExtractProgress(tabId, messageId, 100, err);
    sendExtractResult(tabId, messageId, { success: false, error: err });
    return { success: false, error: err };
  }
  if (activeExtractJobs.size >= MAX_EMBEDDED_EXTRACTS_TOTAL) {
    const err = `Too many embedded extractions running (limit ${MAX_EMBEDDED_EXTRACTS_TOTAL}).`;
    sendExtractProgress(tabId, messageId, 100, err);
    sendExtractResult(tabId, messageId, { success: false, error: err });
    return { success: false, error: err };
  }

  activeExtractJobs.set(messageId, { tabId, messageId, startTime: Date.now(), status: 'starting' });
  let resolution = null;

  try {
    sendExtractProgress(tabId, messageId, 3, 'Validating stream URL...');
    console.log('[Background] Validating URL...');
    if (!isHttpUrl(streamUrl)) {
      throw new Error('Only http(s) stream URLs are supported.');
    }

    console.log('[Background] Resolving stream URL...');
    resolution = await resolveStreamUrl(streamUrl, tabId, messageId);
    console.log('[Background] Stream resolved:', { streamUrl: resolution.streamUrl?.substring(0, 60), isHls: resolution.isHls, isDash: resolution.isDash });

    sendExtractProgress(tabId, messageId, 10, 'Fetching stream...');
    console.log('[Background] Calling extractEmbeddedSubtitles...');
    const tracks = await extractEmbeddedSubtitles(resolution.streamUrl, normalizedMode, tabId, messageId, { ...resolution, pageHeaders: message.pageHeaders || null });
    console.log('[Background] Extraction successful, found', tracks?.length, 'tracks', { durationMs: Date.now() - startedAt });
    sendExtractProgress(tabId, messageId, 100, 'Extraction complete');
    const result = { success: true, tracks };
    sendExtractResult(tabId, messageId, result);
    return result;
  } catch (error) {
    console.error('[Background] Extraction failed:', error, { durationMs: Date.now() - startedAt });
    console.error('[Background] Error details:', {
      message: error.message,
      stack: error.stack,
      name: error.name
    });
    sendDebugLog(tabId, messageId, `Extraction failed: ${error.message || error}`, 'error');
    const errorMsg = error.message || 'Extraction failed';
    sendExtractProgress(tabId, messageId, 100, 'Extraction failed: ' + errorMsg);
    const resolutionHost = (() => {
      try { return new URL(resolution?.streamUrl || streamUrl || '').hostname; } catch (_) { return resolution?.streamUrl || streamUrl || ''; }
    })();
    const result = {
      success: false,
      error: `${errorMsg}${resolutionHost ? ` (stream host: ${resolutionHost})` : ''}`
    };
    sendExtractResult(tabId, messageId, result);
    return result;
  } finally {
    activeExtractJobs.delete(messageId);
    if (!activeExtractJobs.size) {
      await forceCloseOffscreenDocument('extract-finished');
    } else {
      scheduleOffscreenCleanup();
    }
  }
}

/**
 * Extract audio from video stream
 */

async function extractAudioFromStream(streamUrl, planInput, onProgress, ctx = null, opts = {}) {
  const normalizedPlan = normalizeSyncPlan(planInput);
  const normalizedMode = 'single';
  console.log('[Background] Extracting audio from:', streamUrl, 'plan:', normalizedPlan);
  if (ctx?.tabId) {
    const host = (() => { try { return new URL(streamUrl || '').hostname; } catch (_) { return streamUrl || ''; } })();
    sendDebugLog(ctx.tabId, ctx.messageId, `Extract request: host=${host || 'n/a'} plan=${describePlanForLog(normalizedPlan)}`, 'info');
  }
  const baseHeaders = (() => {
    const h = ctx?.pageHeaders || {};
    const headers = {};
    if (h.referer) headers['Referer'] = h.referer;
    if (h.cookie) headers['Cookie'] = h.cookie;
    if (h.userAgent) headers['User-Agent'] = h.userAgent;
    return Object.keys(headers).length ? headers : null;
  })();
  if (ctx?.tabId && baseHeaders) {
    sendDebugLog(ctx.tabId, ctx.messageId, `Using page headers for extract (referer=${baseHeaders.Referer ? 'yes' : 'no'}, ua=${baseHeaders['User-Agent'] ? 'yes' : 'no'}, cookies=${baseHeaders.Cookie ? 'yes' : 'no'})`, 'info');
  }

  try {
    const isHls = /\.m3u8(\?|$)/i.test(streamUrl);
    const isDash = /\.mpd(\?|$)/i.test(streamUrl);
    const wantsFullStream = normalizedPlan.fullScan === true || normalizedPlan.coveragePct >= 0.99 || normalizedPlan.preset === 'complete';
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Stream type detection: HLS=${isHls} DASH=${isDash}`, 'info');
    }
    let detectedDuration = Number.isFinite(normalizedPlan.durationSeconds) ? normalizedPlan.durationSeconds : null;
    let audioWindows = [];

    if (isDash && !detectedDuration) {
      const dashDur = await probeDashDuration(streamUrl);
      if (dashDur) detectedDuration = dashDur;
    }

    if (isHls) {
      onProgress(8);
      const hlsResult = await fetchHlsWindows(streamUrl, (p) => onProgress(8 + p * 0.45), normalizedPlan, baseHeaders);
      detectedDuration = detectedDuration || hlsResult.totalDurationSec || null;
      if (detectedDuration) {
        onProgress(12, `Detected runtime ~${formatSecondsShort(detectedDuration)}`);
      }
      const { windows: windowSpecs, plan: effectivePlan } = planWindows(
        detectedDuration || hlsResult.totalDurationSec,
        normalizeSyncPlan({ ...normalizedPlan, durationSeconds: detectedDuration || hlsResult.totalDurationSec })
      );
      if (effectivePlan) {
        onProgress(18, `Sync plan: ${describePlanForLog(effectivePlan)}`);
      }
      onProgress(60);
      audioWindows = await decodeWindowsWithFFmpeg(
        windowSpecs,
        normalizedMode,
        (p) => onProgress(60 + p * 0.35),
        ctx,
        { strictWhenTooFew: true, allowPartialOnStrictFail: false, requireAll: true, audioStreamIndex: opts?.audioStreamIndex }
      );
      onProgress(96);
      return audioWindows;
    }

    const probedDuration = !detectedDuration ? await probeDurationHead(streamUrl, baseHeaders) : null;
    if (probedDuration && !detectedDuration) detectedDuration = probedDuration;

    const sampleOpts = normalizedPlan.fullScan ? { minBytes: 192 * 1024 * 1024, maxBytesCap: 768 * 1024 * 1024 } : {};
    let sample = null;
    let fullFetchedUpfront = false;

    if (wantsFullStream && !isHls) {
      const statusMsg = 'Complete mode: downloading full stream...';
      try {
        onProgress(10, statusMsg);
        const full = await fetchFullStreamBuffer(streamUrl, (p) => onProgress(10 + p * 0.4, statusMsg), baseHeaders);
        const fullBuf = full?.buffer || full;
        sample = {
          ...full,
          buffer: fullBuf,
          partial: false,
          durationSec: probeContainerDuration(fullBuf) || detectedDuration || null
        };
        if (sample?.durationSec && !detectedDuration) {
          detectedDuration = sample.durationSec;
        }
        fullFetchedUpfront = true;
        if (ctx?.tabId) {
          const sizeMb = fullBuf?.byteLength ? Math.round(fullBuf.byteLength / (1024 * 1024)) : 'unknown';
          sendDebugLog(ctx.tabId, ctx.messageId, `Complete mode: fetched full stream first (~${sizeMb} MB)`, 'info');
        }
      } catch (fullErr) {
        console.warn('[Background] Upfront full fetch failed, falling back to ranged sample:', fullErr?.message || fullErr);
        if (ctx?.tabId) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Full fetch upfront failed (${fullErr?.message || fullErr}); falling back to range sample`, 'warn');
        }
      }
    }

    if (!sample) {
      onProgress(10);
      sample = await fetchByteRangeSample(streamUrl, (p) => onProgress(10 + p * 0.4), sampleOpts, baseHeaders);
      if (sample?.durationSec) {
        detectedDuration = detectedDuration || sample.durationSec;
      }
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Byte-range sample: duration=${sample?.durationSec || 'n/a'}s partial=${sample?.partial === true} totalBytes=${sample?.totalBytes || 'n/a'}`, 'info');
      }
    }
    if (detectedDuration) {
      onProgress(14, `Detected runtime ~${formatSecondsShort(detectedDuration)}`);
    }

    const sampleBytes = sample?.buffer?.byteLength || sample?.byteLength || 0;
    const declaredTotal = sample?.totalBytes || null;
    const looksPartial = sample?.partial === true || (wantsFullStream && declaredTotal && sampleBytes && sampleBytes < declaredTotal * 0.98);
    if (wantsFullStream && looksPartial && !fullFetchedUpfront) {
      const sizeGuardBytes = declaredTotal || sampleBytes || 0;
      const allowFullFetch = !sizeGuardBytes || sizeGuardBytes <= 4 * 1024 * 1024 * 1024; // allow multi-GB streams; only skip if clearly extreme
      if (ctx?.tabId) {
        const humanSize = sizeGuardBytes ? `${Math.round(sizeGuardBytes / (1024 * 1024))}MB` : 'unknown size';
        sendDebugLog(ctx.tabId, ctx.messageId, `Sample looks partial (${humanSize}); fetching full stream for complete coverage...`, allowFullFetch ? 'warn' : 'error');
      }
      if (allowFullFetch) {
        const statusMsg = 'Sample looks partial; downloading full stream for complete coverage...';
        try {
          const full = await fetchFullStreamBuffer(streamUrl, (p) => onProgress(48 + p * 0.18, statusMsg), baseHeaders);
          const fullBuf = full?.buffer || full;
          sample = {
            ...sample,
            ...full,
            buffer: fullBuf,
            partial: false,
            totalBytes: full?.totalBytes || declaredTotal || null,
            durationSec: probeContainerDuration(fullBuf) || sample?.durationSec || detectedDuration || null
          };
          if (sample?.durationSec && !detectedDuration) {
            detectedDuration = sample.durationSec;
          }
          if (ctx?.tabId) {
            const sizeMb = fullBuf?.byteLength ? Math.round(fullBuf.byteLength / (1024 * 1024)) : 'unknown';
            sendDebugLog(ctx.tabId, ctx.messageId, `Full stream fetched (~${sizeMb} MB); continuing with complete buffer`, 'info');
          }
        } catch (fullErr) {
          console.warn('[Background] Full fetch fallback failed:', fullErr?.message || fullErr);
          if (ctx?.tabId) {
            sendDebugLog(ctx.tabId, ctx.messageId, `Full fetch fallback failed: ${fullErr?.message || fullErr}`, 'error');
          }
        }
      }
    }

    const estimateCoverageSec = (sampleObj, totalSec) => {
      if (!sampleObj?.partial) return null;
      const bufBytes = sampleObj?.buffer?.byteLength || 0;
      const totalBytes = sampleObj?.totalBytes || null;
      const dur = Number.isFinite(totalSec) ? totalSec : (Number.isFinite(sampleObj?.durationSec) ? sampleObj.durationSec : null);
      if (bufBytes && totalBytes && dur) {
        const ratio = Math.min(1, bufBytes / totalBytes);
        const cov = dur * ratio;
        return Number.isFinite(cov) ? cov : null;
      }
      if (Number.isFinite(sampleObj?.durationSec)) {
        return sampleObj.durationSec * 0.35; // fallback guess when only head duration is known
      }
      return null;
    };

    let sampleCoverageSec = estimateCoverageSec(sample, detectedDuration || sample?.durationSec);

    const computePlanAndWindows = (durationSec) => planWindows(durationSec, normalizeSyncPlan({ ...normalizedPlan, durationSeconds: durationSec }));
    const durationForPlan = detectedDuration || sample?.durationSec || planInput?.durationSeconds || sampleCoverageSec;
    let { windows: windowSpecs, plan: effectivePlan } = computePlanAndWindows(durationForPlan);
    if (effectivePlan) {
      onProgress(18, `Sync plan: ${describePlanForLog(effectivePlan)}`);
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Window specs (${windowSpecs.length}): ${JSON.stringify(windowSpecs)}`, 'info');
        if (sampleCoverageSec) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Coverage estimate from sample ~${Math.round(sampleCoverageSec)}s of audio`, 'info');
        }
      }
    }

    const buildWindowBuffers = async (specs, headSample, totalDurationSec, headCoverageSec = null) => {
      const windows = [];
      const fallbackHead = (specs?.[0]?.durSec || effectivePlan?.windowSeconds || 60);
      const headDuration = headCoverageSec
        || headSample?.durationSec
        || probeContainerDuration(headSample?.buffer)
        || totalDurationSec
        || fallbackHead;
      const clampSeek = (desired, available) => {
        if (!Number.isFinite(available) || available <= 0) return Math.max(0, desired || 0);
        if (!Number.isFinite(desired) || desired < 0) return 0;
        if (desired > available - 0.5) {
          // Keep a tiny buffer inside the available window to avoid empty decodes
          return Math.max(0, available - Math.min(available * 0.1, 10));
        }
        return desired;
      };
      let tailSample = null;
      const ensureTail = async () => {
        if (tailSample) return tailSample;
        onProgress(86, 'Fetching tail slice for late windows...');
        tailSample = await fetchTailSample(streamUrl, 96 * 1024 * 1024, (p) => onProgress(86 + p * 0.08), baseHeaders);
        tailSample.durationSec = probeContainerDuration(tailSample.buffer) || headDuration || null;
        return tailSample;
      };

      for (let idx = 0; idx < specs.length; idx++) {
        const spec = specs[idx];
        const useTail = headSample?.partial && headDuration && spec.startSec > headDuration * 0.65;
        if (useTail) {
          const tail = await ensureTail();
          const tailDuration = tail.durationSec || fallbackHead || headDuration;
          let tailStartSec;
          if (totalDurationSec && Number.isFinite(tailDuration)) {
            tailStartSec = Math.max(0, totalDurationSec - tailDuration);
          } else {
            tailStartSec = Math.max(0, spec.startSec - (tailDuration || fallbackHead) * 0.8);
          }
          const seekToRaw = spec.startSec - tailStartSec;
          const seekTo = clampSeek(seekToRaw, tailDuration || fallbackHead);
          const actualStartSec = (Number.isFinite(tailStartSec) ? tailStartSec : 0) + seekTo;
          const w = {
            buffer: tail.buffer,
            startSec: actualStartSec,
            plannedStartSec: spec.startSec,
            durSec: spec.durSec,
            seekToSec: seekTo
          };
          windows.push(w);
          if (ctx?.tabId) {
            sendDebugLog(ctx.tabId, ctx.messageId, `Window#${idx + 1} (tail) planned=${spec.startSec}s -> actual=${actualStartSec}s dur=${spec.durSec}s seek=${seekTo}s bytes=${tail.buffer?.byteLength || 0}`, 'info');
          }
        } else {
          const seekTo = clampSeek(spec.startSec, headDuration || fallbackHead);
          const actualStartSec = headSample?.partial ? seekTo : spec.startSec;
          const w = {
            buffer: headSample.buffer,
            startSec: actualStartSec,
            plannedStartSec: spec.startSec,
            durSec: spec.durSec,
            seekToSec: seekTo
          };
          windows.push(w);
          if (ctx?.tabId) {
            sendDebugLog(ctx.tabId, ctx.messageId, `Window#${idx + 1} (head) planned=${spec.startSec}s -> actual=${actualStartSec}s dur=${spec.durSec}s seek=${seekTo}s bytes=${headSample.buffer?.byteLength || 0}`, 'info');
          }
        }
      }
      return windows;
    };

    const tryDecode = async (sampleData, progressStart, progressSpan, label) => {
      onProgress(progressStart, label || 'Decoding audio via FFmpeg...');
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Preparing window buffers (partial=${sampleData?.partial === true})`, 'info');
      }
      const windows = await buildWindowBuffers(windowSpecs, sampleData, durationForPlan, sampleCoverageSec);
      return await decodeWindowsWithFFmpeg(
        windows,
        normalizedMode,
        (p) => onProgress(progressStart + p * progressSpan),
        ctx,
        {
          strictWhenTooFew: true,
          allowPartialOnStrictFail: false,
          requireAll: true,
          audioStreamIndex: opts?.audioStreamIndex
        }
      );
    };

    if (sample?.partial) {
      onProgress(55, 'Partial fetch detected; drift correction may be limited');
      console.warn('[Background] Partial fetch; drift correction may be limited');
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, 'Partial fetch detected; attempting tail fetch for late windows', 'warn');
      }
    }

    let decodeError = null;
    try {
      audioWindows = await tryDecode(sample, 70, 0.2);
    } catch (err) {
      decodeError = err;
    }

    const fullFetchRetry = async (reasonLabel) => {
      const statusMsg = reasonLabel || 'Retrying audio decode with full stream...';
      try {
        const full = await fetchFullStreamBuffer(streamUrl, (p) => onProgress(70 + p * 0.15, statusMsg), baseHeaders);
        const fullBuf = full?.buffer || full;
        sample = {
          ...sample,
          ...full,
          buffer: fullBuf,
          partial: false,
          totalBytes: full?.totalBytes || sample?.totalBytes || null,
          durationSec: probeContainerDuration(fullBuf) || sample?.durationSec || detectedDuration || null
        };
        if (sample?.durationSec && !detectedDuration) {
          detectedDuration = sample.durationSec;
        }
        const durationForRetry = detectedDuration || sample?.durationSec || planInput?.durationSeconds || null;
        ({ windows: windowSpecs, plan: effectivePlan } = computePlanAndWindows(durationForRetry || durationForPlan));
        if (effectivePlan && ctx?.tabId) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Retry decode after full fetch; window specs (${windowSpecs.length}): ${JSON.stringify(windowSpecs)}`, 'info');
        }
        audioWindows = await tryDecode(sample, 85, 0.12, statusMsg);
        decodeError = null;
      } catch (fullErr) {
        decodeError = fullErr;
        if (ctx?.tabId) {
          sendDebugLog(ctx.tabId, ctx.messageId, `Full-fetch retry failed: ${fullErr?.message || fullErr}`, 'error');
        }
      }
    };

    const sampleFullyFetched = sample?.partial === false && (!sample?.totalBytes || !sample?.buffer?.byteLength || sample.buffer.byteLength >= sample.totalBytes * 0.98);
    if (decodeError && !sampleFullyFetched) {
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Decode failed (${decodeError?.message || decodeError}); retrying after full fetch...`, 'warn');
      }
      await fullFetchRetry('Decode failed; downloading full stream to retry...');
    }

    if (decodeError) {
      throw decodeError;
    }

    if (!audioWindows || !audioWindows.length) {
      throw new Error('Audio decode returned no windows');
    }

    onProgress(95);
    if (ctx?.tabId) {
      const totalBytes = audioWindows.reduce((sum, w) => sum + (w?.audioBlob?.size || 0), 0);
      sendDebugLog(ctx.tabId, ctx.messageId, `Audio extraction complete (${audioWindows.length} window(s), totalBytes=${totalBytes})`, 'info');
    }
    return audioWindows;

  } catch (error) {
    console.error('[Background] Audio extraction failed:', error);
    throw new Error(`Audio extraction failed: ${error.message}`);
  }
}

async function handleAutoSubRequest(message, tabId) {
  const { messageId, data = {} } = message || {};
  const streamUrl = data.streamUrl;
  const cfAccountId = data.cfAccountId || data.accountId;
  const cfToken = data.cfToken || data.token;
  const model = data.model || '@cf/openai/whisper';
  let sourceLanguage = (data.sourceLanguage || data.language || '').trim();
  const diarization = data.diarization === true;
  const pageHeaders = data.pageHeaders || null;
  const ctx = { tabId, messageId, pageHeaders };

  if (!streamUrl) {
    return { success: false, error: 'Missing stream URL' };
  }
  if (!cfAccountId || !cfToken) {
    return { success: false, error: 'Cloudflare credentials are required' };
  }

  try {
    const host = (() => { try { return new URL(streamUrl || '').hostname; } catch (_) { return streamUrl || ''; } })();
    sendDebugLog(tabId, messageId, `Auto-sub request received (model=${model}, diarization=${diarization}) host=${host || 'n/a'}`, 'info');
    const cfWindowCapSec = 90; // ~2.9 MB at 16k/16-bit mono, keeps well below Cloudflare's effective payload guard
    const planInput = {
      preset: 'complete',
      fullScan: true,
      strategy: 'full',
      coveragePct: 1,
      minWindows: null,
      maxWindows: null,
      requestedWindowSeconds: cfWindowCapSec,
      maxChunkSeconds: cfWindowCapSec
    };

    const buildBaseHeaders = (fromPageHeaders) => {
      const h = fromPageHeaders || {};
      const headers = {};
      if (h.referer) headers.Referer = h.referer;
      if (h.cookie) headers.Cookie = h.cookie;
      if (h.userAgent) headers['User-Agent'] = h.userAgent;
      return Object.keys(headers).length ? headers : null;
    };

    const baseHeaders = buildBaseHeaders(pageHeaders);

    const pickPreferredTrack = (tracks, langHint) => {
      if (!Array.isArray(tracks) || !tracks.length) return { preferred: null, ordered: [] };
      const normalize = (l) => (l || '').split('-')[0].toLowerCase();
      const hint = normalize(langHint || '');
      const ordered = [...tracks];
      const byHint = hint ? ordered.find(t => normalize(t.language) === hint) : null;
      const byEn = ordered.find(t => normalize(t.language) === 'en');
      const preferred = byHint || byEn || ordered[0];
      return { preferred, ordered };
    };

    const probeAudioTracks = async () => {
      try {
        const sample = await fetchByteRangeSample(
          streamUrl,
          () => { },
          { minBytes: 12 * 1024 * 1024, maxBytesCap: 64 * 1024 * 1024 },
          baseHeaders
        );
        const headerInfo = parseMkvHeaderInfo(sample.buffer, { maxScanBytes: Math.min(sample.buffer.byteLength, 12 * 1024 * 1024) });
        const audioTracks = (headerInfo?.tracks || [])
          .filter(t => t.type === 0x02 || t.type === 2)
          .map((t, idx) => ({
            index: idx,
            trackNumber: typeof t.number === 'number' ? t.number : idx + 1,
            language: (t.language || '').trim(),
            name: t.name || '',
            codec: t.codecId || ''
          }));
        return audioTracks;
      } catch (err) {
        console.warn('[Background] Audio track probe failed:', err?.message || err);
        if (tabId) {
          sendDebugLog(tabId, messageId, `Audio track probe failed: ${err?.message || err}`, 'warn');
        }
        return [];
      }
    };

    const isMixedLangError = (err) => {
      const msg = (err?.message || '').toLowerCase();
      return msg.includes('different language') || msg.includes('unsupported audio input') || msg.includes('language');
    };

    const audioTracks = await probeAudioTracks();
    if (audioTracks.length) {
      const trackSummaries = audioTracks.map(t => `#${t.trackNumber || t.index + 1}${t.language ? `(${t.language})` : ''}${t.name ? ` ${t.name}` : ''}`).join(' | ');
      sendDebugLog(tabId, messageId, `Detected audio tracks: ${trackSummaries}`, 'info');
    }
    const { preferred, ordered } = pickPreferredTrack(audioTracks, sourceLanguage || 'en');
    if (!sourceLanguage && preferred?.language) {
      sourceLanguage = preferred.language;
    }

    const attemptAutoSub = async (audioStreamIndex) => {
      sendAutoSubProgress(tabId, messageId, 5, `Preparing pipeline (audio track ${audioStreamIndex + 1})...`, 'init');
      sendAutoSubProgress(tabId, messageId, 8, 'Fetching stream...', 'fetch');
      const audioWindows = await extractAudioFromStream(
        streamUrl,
        planInput,
        (p, status) => {
          // Only log a label when provided; otherwise just advance progress to avoid spamming the same text.
          sendAutoSubProgress(tabId, messageId, Math.min(60, Math.round(p)), status || null, 'fetch');
        },
        ctx,
        { audioStreamIndex }
      );
      sendAutoSubProgress(tabId, messageId, 65, 'Audio ready. Sending to Cloudflare...', 'transcribe');
      sendDebugLog(tabId, messageId, `Audio ready; forwarding ${audioWindows.length} window(s) to Cloudflare (audio track ${audioStreamIndex + 1}, lang=${sourceLanguage || 'auto'})`, 'info');
      try {
        const transcript = await transcribeWindowsWithCloudflare(
          audioWindows,
          { accountId: cfAccountId, token: cfToken, model, sourceLanguage, diarization, filename: data.filename || 'audio' },
          (p, status) => sendAutoSubProgress(tabId, messageId, Math.min(92, Math.round(p)), status || 'Transcribing...', 'transcribe'),
          ctx
        );
        sendAutoSubProgress(tabId, messageId, 96, 'Transcript ready. Finalizing...', 'package');
        sendDebugLog(tabId, messageId, `Transcript ready (segments=${transcript.segmentCount || '?'}, lang=${transcript.languageCode || 'und'})`, 'info');
        const payload = { success: true, ...transcript };
        sendAutoSubResult(tabId, messageId, payload);
        return payload;
      } catch (cfErr) {
        sendDebugLog(tabId, messageId, `Cloudflare transcription failed: ${cfErr?.message || cfErr}`, 'error');
        throw cfErr;
      }
    };

    const streamAttempts = (() => {
      if (preferred) {
        const others = ordered.filter(t => t.index !== preferred.index).map(t => t.index);
        return [preferred.index, ...others];
      }
      return [0, 1];
    })();
    let lastErr = null;
    for (let i = 0; i < streamAttempts.length; i++) {
      try {
        return await attemptAutoSub(streamAttempts[i]);
      } catch (err) {
        lastErr = err;
        if (isMixedLangError(err) && i < streamAttempts.length - 1) {
          sendDebugLog(tabId, messageId, `Cloudflare rejected audio track ${streamAttempts[i] + 1} as mixed-language; retrying with track ${streamAttempts[i + 1] + 1}...`, 'warn');
          continue;
        }
        throw err;
      }
    }
    if (lastErr) throw lastErr;
  } catch (error) {
    console.error('[Background] Auto-sub request failed:', error);
    const msg = error?.message || 'Auto-subtitles failed';
    sendDebugLog(tabId, messageId, `Auto-sub failed: ${msg}${error?.stack ? ` | stack: ${error.stack.slice(0, 400)}` : ''}`, 'error');
    sendDebugLog(tabId, messageId, `Auto-sub failed: ${msg}`, 'error');
    sendAutoSubProgress(tabId, messageId, 100, `Failed: ${msg}`, 'error', 'error');
    const payload = { success: false, error: msg };
    sendAutoSubResult(tabId, messageId, payload);
    return payload;
  }
}

async function uploadToAssemblyFromBlob(apiKey, blob, logger) {
  if (!apiKey) throw new Error('AssemblyAI API key missing');
  if (!blob) throw new Error('No upload payload provided');
  const headers = { Authorization: apiKey };
  if (blob.type) headers['Content-Type'] = blob.type;
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 120000);
  let response = null;
  let raw = '';
  try {
    logger?.('Uploading media to AssemblyAI...', 'info');
    response = await fetch('https://api.assemblyai.com/v2/upload', {
      method: 'POST',
      headers,
      body: blob,
      signal: controller.signal
    });
    raw = await response.text();
  } catch (err) {
    clearTimeout(timeout);
    if (err.name === 'AbortError') throw new Error('AssemblyAI upload timed out');
    throw err;
  }
  clearTimeout(timeout);
  let data = null;
  try { data = raw ? JSON.parse(raw) : null; } catch (_) { data = null; }
  if (!response.ok || !data?.upload_url) {
    const msg = data?.error || data?.message || raw || `AssemblyAI upload failed (${response?.status || 'no status'})`;
    throw new Error(msg);
  }
  return data.upload_url;
}

async function createAssemblyTranscriptClient(apiKey, payload = {}, logger) {
  const body = {
    punctuate: true,
    format_text: true,
    speaker_labels: payload.speaker_labels === false ? false : true,
    disfluencies: true,
    audio_url: payload.audio_url
  };
  if (payload.language_code) {
    body.language_code = payload.language_code;
  } else {
    body.language_detection = true;
  }
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 30000);
  try {
    logger?.('Requesting AssemblyAI transcript...', 'info');
    const resp = await fetch('https://api.assemblyai.com/v2/transcript', {
      method: 'POST',
      headers: {
        Authorization: apiKey,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify(body),
      signal: controller.signal
    });
    const data = await resp.json().catch(() => null);
    if (!resp.ok || !data?.id) {
      const msg = data?.error || data?.message || `AssemblyAI transcript request failed (${resp.status})`;
      throw new Error(msg);
    }
    return data.id;
  } catch (err) {
    if (err.name === 'AbortError') throw new Error('AssemblyAI transcript request timed out');
    throw err;
  } finally {
    clearTimeout(timeout);
  }
}

async function pollAssemblyTranscriptClient(apiKey, transcriptId, logger) {
  const start = Date.now();
  while (Date.now() - start < ASSEMBLY_POLL_TIMEOUT_MS) {
    const resp = await fetch(`https://api.assemblyai.com/v2/transcript/${encodeURIComponent(transcriptId)}`, {
      headers: { Authorization: apiKey }
    });
    const data = await resp.json().catch(() => null);
    const status = (data?.status || '').toLowerCase();
    if (status === 'completed') return data;
    if (status === 'error') {
      const msg = data?.error || data?.message || 'AssemblyAI returned an error';
      throw new Error(msg);
    }
    logger?.(`AssemblyAI status: ${status || 'pending'}...`, 'info');
    await new Promise((r) => setTimeout(r, ASSEMBLY_POLL_INTERVAL_MS));
  }
  throw new Error('AssemblyAI transcription timed out');
}

async function fetchAssemblySrtClient(apiKey, transcriptId, logger) {
  const resp = await fetch(`https://api.assemblyai.com/v2/transcript/${encodeURIComponent(transcriptId)}/srt`, {
    headers: { Authorization: apiKey }
  });
  if (!resp.ok) {
    logger?.(`AssemblyAI SRT fetch failed (${resp.status})`, 'warn');
    return '';
  }
  return await resp.text();
}

async function handleAssemblyAutoSubRequest(message, tabId) {
  const { messageId, data = {} } = message || {};
  const streamUrl = data.streamUrl;
  const apiKey = (data.assemblyApiKey || '').trim();
  let sourceLanguage = (data.sourceLanguage || data.language || '').trim();
  const diarization = data.diarization === true;
  const sendFullVideo = data.sendFullVideo === true;
  const pageHeaders = data.pageHeaders || null;
  const ctx = { tabId, messageId, pageHeaders };

  if (!streamUrl) return { success: false, error: 'Missing stream URL' };
  if (!apiKey) return { success: false, error: 'AssemblyAI API key is required' };

  const logToPage = (text, level = 'info') => sendDebugLog(tabId, messageId, text, level);
  const progress = (pct, status, stage = 'info', level = 'info') => sendAutoSubProgress(tabId, messageId, pct, status, stage, level);

  try {
    const baseHeaders = (() => {
      const h = pageHeaders || {};
      const headers = {};
      if (h.referer) headers['Referer'] = h.referer;
      if (h.cookie) headers['Cookie'] = h.cookie;
      if (h.userAgent) headers['User-Agent'] = h.userAgent;
      return Object.keys(headers).length ? headers : null;
    })();

    progress(5, 'Preparing AssemblyAI pipeline...', 'fetch');
    const isHls = /\.m3u8(\?|$)/i.test(streamUrl);
    let uploadBlob = null;
    let contentType = '';
    let usedFullVideo = sendFullVideo === true;

    if (sendFullVideo) {
      if (isHls) {
        const full = await fetchFullHlsStream(streamUrl, (p) => progress(Math.min(60, 5 + Math.round(p * 0.55)), 'Fetching full stream...', 'fetch'), baseHeaders);
        uploadBlob = new Blob([full.buffer], { type: full.contentType || 'video/mp2t' });
        contentType = uploadBlob.type || full.contentType || 'video/mp2t';
      } else {
        const full = await fetchFullStreamBuffer(streamUrl, (p) => progress(Math.min(60, p), 'Fetching full stream...', 'fetch'), baseHeaders);
        uploadBlob = new Blob([full.buffer], { type: full.contentType || 'video/mp4' });
        contentType = uploadBlob.type || full.contentType || 'video/mp4';
      }
    } else {
      const planInput = {
        preset: 'complete',
        fullScan: true,
        coveragePct: 1,
        minWindows: 1,
        maxWindows: 1,
        requestedWindowSeconds: 6 * 3600,
        maxChunkSeconds: 6 * 3600
      };
      const audioWindows = await extractAudioFromStream(
        streamUrl,
        planInput,
        (p, status) => progress(Math.min(70, Math.round(p)), status || 'Extracting audio...', 'fetch'),
        ctx,
        {}
      );
      if (!audioWindows || !audioWindows.length) {
        throw new Error('Audio extraction returned no audio blob');
      }
      if (audioWindows.length > 1) {
        try {
          const stitched = await stitchWavWindows(audioWindows, ctx);
          uploadBlob = stitched?.blob || null;
          contentType = uploadBlob?.type || 'audio/wav';
          const stitchedDur = stitched?.durationMs ? `${Math.round(stitched.durationMs / 1000)}s` : '?s';
          const stitchedMb = stitched?.bytes
            ? `${Math.round(stitched.bytes / (1024 * 1024))}MB`
            : `${Math.round((uploadBlob?.size || 0) / (1024 * 1024))}MB`;
          logToPage(`Combined ${audioWindows.length} audio windows into single WAV (~${stitchedDur}, ${stitchedMb})`, 'info');
        } catch (combineErr) {
          logToPage(`Failed to combine audio windows; using first window only (${combineErr?.message || combineErr})`, 'warn');
        }
      }
      if (!uploadBlob) {
        const first = Array.isArray(audioWindows) ? audioWindows[0] : null;
        uploadBlob = first?.audioBlob || first?.audio || (first?.audioBuffer ? new Blob([first.audioBuffer], { type: 'audio/wav' }) : null);
        contentType = uploadBlob?.type || 'audio/wav';
      }
      if (!uploadBlob) {
        throw new Error('Audio extraction returned no audio blob');
      }
      usedFullVideo = false;
    }

    const uploadBytes = uploadBlob?.size || null;
    progress(72, 'Uploading to AssemblyAI...', 'transcribe');
    const uploadUrl = await uploadToAssemblyFromBlob(apiKey, uploadBlob, (msg, lvl) => logToPage(msg, lvl || 'info'));
    const transcriptId = await createAssemblyTranscriptClient(apiKey, {
      audio_url: uploadUrl,
      language_code: sourceLanguage,
      speaker_labels: diarization !== false
    }, (msg, lvl) => logToPage(msg, lvl || 'info'));
    logToPage(`AssemblyAI transcript id: ${transcriptId}`, 'info');
    progress(80, 'Polling AssemblyAI...', 'transcribe');
    const transcriptData = await pollAssemblyTranscriptClient(apiKey, transcriptId, (msg, lvl) => logToPage(msg, lvl || 'info'));
    if (!sourceLanguage && transcriptData?.language) {
      sourceLanguage = transcriptData.language;
    }
    progress(92, 'Fetching SRT...', 'package');
    const assemblySrt = await fetchAssemblySrtClient(apiKey, transcriptId, (msg, lvl) => logToPage(msg, lvl || 'info'));
    const srt = assemblySrt || '';
    if (!srt) throw new Error('AssemblyAI returned no SRT');
    progress(98, 'Transcript ready. Finalizing...', 'package');
    const transcriptPayload = {
      srt,
      languageCode: sourceLanguage || transcriptData?.language || 'und',
      model: 'assemblyai',
      assemblyId: transcriptId,
      audioBytes: uploadBytes,
      audioSource: sendFullVideo ? 'extension-full-video' : 'extension-audio',
      contentType,
      usedFullVideo
    };
    const payload = { success: true, transcript: transcriptPayload, ...transcriptPayload };
    sendAutoSubResult(tabId, messageId, payload);
    progress(100, 'AssemblyAI transcription complete', 'package', 'success');
    return payload;
  } catch (error) {
    progress(100, `AssemblyAI failed: ${error?.message || error}`, 'error', 'error');
    sendAutoSubResult(tabId, messageId, { success: false, error: error?.message || 'AssemblyAI transcription failed' });
    return { success: false, error: error?.message || 'AssemblyAI transcription failed' };
  }
}
/**
 * Synchronize subtitle using alass algorithm
 */
async function synchronizeSubtitle(audioBlob, subtitleContent, mode, onProgress, preferAlass = false, ctx = null, opts = {}) {
  const ctxLabel = ctx?.messageId ? `job ${ctx.messageId}` : 'unknown job';
  const preferFfsubsync = opts?.preferFfsubsync === true;
  const preferCtc = opts?.preferCtc === true;
  const presetStr = ctx?.plan?.preset;
  const modeGroup = ctx?.plan?.modeGroup
    || (typeof presetStr === 'string' && presetStr.startsWith('whisper-') ? 'whisper-alass' : null);
  const isWhisperAlassMode = modeGroup === 'whisper-alass';
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  const whisperBlocked = !WHISPER_EVAL_ALLOWED;
  const windowCount = Array.isArray(audioBlob) ? audioBlob.length : (audioBlob ? 1 : 0);
  console.log('[Background] Synchronizing subtitle...', { windowCount, mode, preferAlass, preferFfsubsync, ctx: ctxLabel });
  if (windowCount) {
    const first = Array.isArray(audioBlob) ? audioBlob[0] : audioBlob;
    const approxKb = Math.round(((first?.audioBlob?.size || 0) / 1024) || 0);
    logToPage(`Autosync starting (${windowCount} window${windowCount === 1 ? '' : 's'}; first window ~${approxKb}KB; preferAlass=${preferAlass}; preferFfsubsync=${preferFfsubsync})`, 'info');
  } else {
    logToPage('Autosync starting with no audio windows detected', 'warn');
  }

  // Branch: Vosk CTC/DTW (explicit choice)
  if (preferCtc) {
    onProgress?.(10, 'Running Vosk CTC/DTW aligner...');
    try {
      const ctcRes = await runVoskCtcAlign(audioBlob, subtitleContent, (p, s) => {
        onProgress?.(p, s || 'Aligning with Vosk (CTC/DTW)...');
      }, ctx);
      if (ctcRes?.result) {
        onProgress?.(100, 'Vosk CTC/DTW alignment complete');
        logToPage(`Vosk CTC/DTW alignment succeeded (${ctcRes.words || '?'} words)`, 'info');
        return ctcRes.result;
      }
    } catch (err) {
      const msg = err?.message || String(err);
      console.warn('[Background] Vosk CTC/DTW failed:', msg);
      logToPage(`Vosk CTC/DTW failed: ${msg}`, 'error');
      throw err;
    }
  }

  // Branch: ffsubsync-first (explicit user choice)
  if (preferFfsubsync) {
    onProgress?.(10, 'Trying ffsubsync-wasm aligner first...');
    try {
      const ffRes = await runFfsubsyncSync(audioBlob, subtitleContent, (p, s) => {
        onProgress?.(p, s || 'Aligning with ffsubsync-wasm...');
      }, ctx, opts.ffsubsyncOptions || {});
      if (ffRes?.result && ffRes.method === 'ffsubsync') {
        onProgress?.(100, 'ffsubsync alignment complete');
        console.log('[Background] Synchronization complete via ffsubsync (preferred)');
        logToPage(`ffsubsync alignment succeeded${ffRes.anchors ? ` using ${ffRes.anchors} anchor segment(s)` : ''}`, 'info');
        return ffRes.result;
      }
    } catch (err) {
      const msg = err?.message || String(err);
      console.warn('[Background] Preferred ffsubsync failed:', msg);
      logToPage(`Preferred ffsubsync failed: ${msg}`, 'error');
      throw err;
    }
  }

  // Branch: alass-first (explicit user choice)
  if (preferAlass) {
    onProgress?.(12, 'Trying alass-wasm aligner first...');
    try {
      const alassRes = await runAlassSync(audioBlob, subtitleContent, (p, s) => {
        onProgress?.(p, s || 'Aligning with alass-wasm...');
      }, ctx);
      if (alassRes?.result && alassRes.method === 'alass') {
        onProgress?.(100, 'alass alignment complete');
        console.log('[Background] Synchronization complete via alass (preferred)');
        logToPage(`alass alignment succeeded using ${alassRes.anchors || '?'} anchor segment(s)`, 'info');
        return alassRes.result;
      }
    } catch (err) {
      const msg = err?.message || String(err);
      console.warn('[Background] Preferred alass failed:', msg);
      logToPage(`Preferred alass failed: ${msg}`, 'error');
      throw err;
    }
  }

  if (whisperBlocked) {
    throw new Error(`Whisper unavailable (${WHISPER_EVAL_REASON || 'eval blocked by CSP'})`);
  }

  // Whisper-first (default path).
  onProgress?.(8, 'Preparing audio for Whisper autosync...');
  const transcript = await transcribeAudioWindows(audioBlob, mode, onProgress, ctx);
  if (!transcript || !transcript.length) {
    throw new Error('Whisper autosync returned no transcript');
  }

  onProgress?.(90, 'Aligning subtitles to transcript...');
  const whisperAligned = alignSubtitlesWithTranscript(subtitleContent, transcript);
  logToPage(`Whisper autosync succeeded with ${transcript.length} transcript segment(s)`, 'info');

  if (isWhisperAlassMode) {
    onProgress?.(94, 'Refining alignment with alass-wasm...');
    const alassRefine = await runAlassSync(audioBlob, whisperAligned, (p, s) => {
      onProgress?.(94 + (p * 0.06), s || 'Refining with alass-wasm...');
    }, ctx);
    if (alassRefine?.result && alassRefine.method === 'alass') {
      onProgress?.(100, 'Whisper + ALASS complete');
      console.log('[Background] Synchronization complete via Whisper + ALASS');
      logToPage(`ALASS refinement succeeded using ${alassRefine.anchors || '?'} anchor segment(s)`, 'info');
      return alassRefine.result;
    }
    throw new Error('ALASS refinement failed for Whisper mode');
  }

  onProgress?.(100, 'Autosync complete');
  console.log('[Background] Synchronization complete via Whisper');
  return whisperAligned;
}

/**
 * Extract embedded subtitle streams using FFmpeg (client-side).
 * Falls back to direct SRT/VTT fetch when possible.
 */
async function resolveStreamUrl(streamUrl, tabId, messageId) {
  const original = String(streamUrl || '');
  let resolvedUrl = original;
  let contentType = '';
  let isHls = /\.m3u8(\?|$)/i.test(original);
  let isDash = /\.mpd(\?|$)/i.test(original);
  const upgradeToHttpsHosts = ['download.real-debrid.com', 'real-debrid.com', 'torrentio.strem.fun', 'strem.fun'];

  try {
    sendExtractProgress(tabId, messageId, 5, 'Resolving stream (following redirects)...');
    const resp = await safeFetch(original, { redirect: 'follow' });
    contentType = resp.headers.get('content-type') || '';

    // Try JSON resolvers (e.g., torrentio resolve)
    if (contentType.includes('application/json')) {
      try {
        const json = await resp.json();
        const candidate = json.url || json.stream || json.file || json.link;
        if (candidate && isHttpUrl(candidate)) {
          resolvedUrl = candidate;
          sendExtractProgress(tabId, messageId, 8, 'Resolved via JSON response');
        }
      } catch (_) {
        // ignore JSON parse errors
      }
    } else {
      // Non-JSON: rely on final URL/content-type
      if (resp.url && isHttpUrl(resp.url)) {
        resolvedUrl = resp.url;
      }
      // HLS by content-type
      if (contentType.includes('application/vnd.apple.mpegurl') || contentType.includes('application/x-mpegURL')) {
        isHls = true;
      }
      if (contentType.includes('application/dash+xml') || contentType.includes('mpd')) {
        isDash = true;
      }
    }

    // If the resolved URL is http on a host that supports https, upgrade to https to avoid mixed-content blocks
    try {
      const parsed = new URL(resolvedUrl);
      if (parsed.protocol === 'http:' && upgradeToHttpsHosts.some(h => parsed.hostname.endsWith(h))) {
        parsed.protocol = 'https:';
        resolvedUrl = parsed.toString();
        console.log('[Background] Upgraded stream URL to https:', resolvedUrl.substring(0, 80));
      }
    } catch (_) {
      // ignore URL parse errors; let downstream handle
    }

    sendExtractProgress(tabId, messageId, 9, `Using stream: ${new URL(resolvedUrl).hostname}`);
  } catch (err) {
    console.warn('[Background] Resolve step failed, continuing with original URL:', err?.message);
  }

  return { streamUrl: resolvedUrl, contentType, isHls, isDash };
}

async function tryExtractDashTextTracks(mpdUrl, tabId, messageId) {
  try {
    sendExtractProgress(tabId, messageId, 12, 'Parsing DASH manifest for text tracks...');
    const text = await (await safeFetch(mpdUrl)).text();
    const tracks = [];

    const baseMatch = text.match(/<BaseURL>([^<]+)<\/BaseURL>/i);
    const baseUrl = baseMatch ? baseMatch[1].trim() : '';

    const adaptationRegex = /<AdaptationSet([^>]*)>([\s\S]*?)<\/AdaptationSet>/gi;
    let adaptation;
    while ((adaptation = adaptationRegex.exec(text)) !== null) {
      const attrs = adaptation[1] || '';
      const body = adaptation[2] || '';
      const mimeMatch = attrs.match(/mimeType="([^"]+)"/i);
      const mime = mimeMatch ? mimeMatch[1] : '';
      const adaptLang = normalizeTrackLanguageCode((attrs.match(/\blang="([^"]+)"/i) || [])[1]);
      const adaptLabel = (attrs.match(/\blabel="([^"]+)"/i) || [])[1];
      if (!/vtt|ttml|webvtt|text\/vtt/i.test(mime)) continue;

      const repRegex = /<Representation[^>]*>([\s\S]*?)<\/Representation>/gi;
      let rep;
      while ((rep = repRegex.exec(body)) !== null) {
        const repBody = rep[1] || '';
        const repLang = normalizeTrackLanguageCode((repBody.match(/\blang="([^"]+)"/i) || [])[1]) || adaptLang || 'und';
        const repLabel = (repBody.match(/\blabel="([^"]+)"/i) || [])[1] || adaptLabel || 'DASH subtitle';
        const repBaseMatch = repBody.match(/<BaseURL>([^<]+)<\/BaseURL>/i);
        const repBase = repBaseMatch ? repBaseMatch[1].trim() : '';
        const url = repBase || baseUrl;
        if (!url) continue;
        const abs = new URL(url, mpdUrl).toString();
        if (abs.endsWith('.vtt') || abs.includes('.vtt?')) {
          const vtt = await (await safeFetch(abs)).text();
          tracks.push({ id: String(tracks.length), label: repBase || repLabel || 'DASH VTT', language: repLang, codec: 'vtt', content: convertVttToSrt(vtt) });
        } else if (abs.endsWith('.srt') || abs.includes('.srt?')) {
          const srt = await (await safeFetch(abs)).text();
          tracks.push({ id: String(tracks.length), label: repBase || repLabel || 'DASH SRT', language: repLang, codec: 'srt', content: srt });
        }
      }
    }

    if (tracks.length) {
      sendExtractProgress(tabId, messageId, 20, `Found ${tracks.length} text track(s) in DASH`);
      return applyContentLanguageGuesses(tracks);
    }
  } catch (err) {
    console.warn('[Background] DASH text track parse failed:', err?.message);
  }
  return null;
}

async function extractEmbeddedSubtitles(streamUrl, mode, tabId, messageId, hints = {}) {
  const normalizedMode = normalizeExtractMode(mode);
  const isCompleteMode = normalizedMode === 'complete';
  const isSmartMode = normalizedMode === 'smart';
  const lowerUrl = String(streamUrl || '').toLowerCase();
  const hostLabel = (() => { try { return new URL(streamUrl).hostname; } catch (_) { return streamUrl; } })();
  const extractionMode = normalizedMode;
  const baseHeaders = mergeHeaders(null, hints?.pageHeaders || null);
  console.log('[Background] extractEmbeddedSubtitles for host:', hostLabel, 'mode:', extractionMode);
  const applyLangHints = (tracks, langHints) => {
    const withHints = (!langHints || !langHints.length)
      ? (tracks || [])
      : applyHeaderLanguagesToTracks(tracks, langHints);
    return applyContentLanguageGuesses(withHints);
  };

  // Simple path: direct subtitle file
  if (lowerUrl.endsWith('.srt') || lowerUrl.includes('.srt?')) {
    const text = await (await safeFetch(streamUrl, baseHeaders ? { headers: baseHeaders } : undefined)).text();
    const langGuess = detectLanguageFromContent(text) || 'und';
    return [{ id: '0', label: 'Subtitle file', language: langGuess, codec: 'srt', content: text }];
  }
  if (lowerUrl.endsWith('.vtt') || lowerUrl.includes('.vtt?')) {
    const text = await (await safeFetch(streamUrl, baseHeaders ? { headers: baseHeaders } : undefined)).text();
    const asSrt = convertVttToSrt(text);
    const langGuess = detectLanguageFromContent(asSrt) || 'und';
    return [{ id: '0', label: 'WebVTT file', language: langGuess, codec: 'vtt', content: asSrt }];
  }

  const isHls = hints.isHls === true || /\.m3u8(\?|$)/i.test(lowerUrl);
  const isDash = hints.isDash === true || /\.mpd(\?|$)/i.test(lowerUrl);

  if (isDash) {
    const dashTracks = await tryExtractDashTextTracks(streamUrl, tabId, messageId);
    if (dashTracks && dashTracks.length) {
      return dashTracks;
    }
    throw new Error('DASH manifest detected but no extractable text tracks were found.');
  }

  // Smart mode: single-pass, fast path. If completeness is uncertain, fail and ask user to use Complete mode.
  if (isSmartMode) {
    const modeLabel = 'Smart';
    const failSmart = (reason) => {
      const msg = `${modeLabel} could not produce complete subtitles${reason ? ` (${reason})` : ''}. Please switch to Complete Mode.`;
      sendDebugLog(tabId, messageId, msg, 'error');
      throw new Error(msg);
    };
    const evaluateTracks = (tracks, durationSec, partial, stage) => {
      if (!tracks?.length) {
        failSmart(stage ? `${stage} returned no tracks` : 'no tracks');
      }
      const summary = summarizeTracks(tracks);
      const timelines = analyzeCueTimelines(tracks);
      const qualityOk = isTrackQualityAcceptable(tracks, summary, timelines, durationSec);
      const partialOk = !partial || (durationSec && summary?.lastCueSec && summary.lastCueSec >= durationSec * 0.95);
      const looksComplete = qualityOk && partialOk;
      const stats = [
        `min ${Math.round((summary?.minTrackSize || 0) / 1024)}KB`,
        `last ${summary?.lastCueSec ? Math.round(summary.lastCueSec) + 's' : 'n/a'}`,
        `partial ${partial ? 'yes' : 'no'}`
      ];
      sendDebugLog(tabId, messageId, `Smart ${stage || 'validation'}: ${stats.join(', ')}`, looksComplete ? 'info' : 'warn');
      if (!looksComplete) {
        failSmart(`${stage || 'validation'} incomplete (quality=${qualityOk ? 'ok' : 'low'}, partial=${partial ? 'yes' : 'no'})`);
      }
      return { tracks, summary };
    };

    // HLS: stick to the video-element path only (fastest, preserves discontinuities).
    if (isHls) {
      sendExtractProgress(tabId, messageId, 4, `${modeLabel}: loading text tracks via video element...`);
      try {
        const videoTracks = applyLangHints(await extractSubtitlesViaVideoOffscreen(streamUrl, extractionMode, messageId, tabId));
        const { summary } = evaluateTracks(videoTracks, null, false, 'video extraction');
        const lastCueText = summary?.lastCueSec ? `; last cue at ${Math.round(summary.lastCueSec)}s` : '';
        sendExtractProgress(tabId, messageId, 100, `${modeLabel}: extracted ${videoTracks.length} track(s) via video${lastCueText}`);
        return videoTracks;
      } catch (vErr) {
        const reason = vErr?.message || vErr;
        sendDebugLog(tabId, messageId, `${modeLabel} video extraction failed (${reason})`, 'warn');
        failSmart('video element path unavailable');
      }
    }

    // Non-HLS: fetch a single generous head slice, demux once, validate completeness.
    sendExtractProgress(tabId, messageId, 5, `${modeLabel}: fetching fast sample...`);
    let sample;
    try {
      sample = await fetchByteRangeSample(
        streamUrl,
        (p) => sendExtractProgress(tabId, messageId, Math.min(60, 5 + Math.round(p * 0.55)), `${modeLabel}: fetching sample from ${hostLabel}...`),
        { minBytes: 96 * 1024 * 1024, maxBytesCap: 320 * 1024 * 1024 },
        baseHeaders
      );
    } catch (sErr) {
      failSmart(`sample fetch failed (${sErr?.message || sErr})`);
    }

    const buffer = sample?.buffer || sample;
    const sampleBytes = buffer?.byteLength || 0;
    const sampleMb = Math.round((sampleBytes / (1024 * 1024)) * 10) / 10;
    sendDebugLog(tabId, messageId, `${modeLabel}: sample ready (~${sampleMb} MB, partial=${sample?.partial ? 'yes' : 'no'})`, 'info');
    sendExtractProgress(tabId, messageId, 75, `${modeLabel}: demuxing sample...`);
    try {
    const tracks = applyLangHints(await demuxSubtitlesOffscreen(buffer, messageId, tabId), sample?.subtitleLangs);
      const durationSec = sample?.durationSec || probeContainerDuration(buffer) || null;
      const { summary } = evaluateTracks(tracks, durationSec, sample?.partial === true, 'demux');
      const lastCueText = summary?.lastCueSec ? `; last cue at ${Math.round(summary.lastCueSec)}s` : '';
      sendExtractProgress(tabId, messageId, 100, `${modeLabel}: demuxed ${tracks.length} track(s)${lastCueText}`);
      return tracks;
    } catch (dErr) {
      failSmart(`demux failed (${dErr?.message || dErr})`);
    }
  }

  if (isCompleteMode) {
    sendExtractProgress(tabId, messageId, 4, isHls ? 'Complete: downloading full HLS stream...' : 'Complete: downloading full stream...');
    const full = isHls
      ? await fetchFullHlsStream(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(92, 5 + Math.round(p * 0.87)), 'Complete: downloading full HLS stream...'), baseHeaders)
      : await fetchFullStreamBuffer(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(92, 5 + Math.round(p * 0.87)), 'Complete: downloading full stream...'), baseHeaders);
    const fullBuffer = full?.buffer || full;
    const fullBytes = fullBuffer?.byteLength || 0;
    const fullMb = Math.round((fullBytes / (1024 * 1024)) * 10) / 10;
    sendDebugLog(tabId, messageId, `Complete: fetched full stream (~${fullMb || '?'} MB). Demuxing...`, 'info');
    sendExtractProgress(tabId, messageId, 95, 'Complete: demuxing full stream...');
    const tracks = applyLangHints(await demuxSubtitlesOffscreen(fullBuffer, messageId, tabId), full?.subtitleLangs || hints?.subtitleLangs);
    if (!tracks || !tracks.length) {
      throw new Error('Complete demux returned no tracks');
    }
    const summary = summarizeTracks(tracks);
    const lastCueText = summary?.lastCueSec ? `; last cue at ${Math.round(summary.lastCueSec)}s` : '';
    sendExtractProgress(tabId, messageId, 100, `Complete: demuxed ${tracks.length} track(s)${lastCueText}`);
    return tracks;
  }

  // PRIMARY METHOD: Try video-based extraction first (gets complete subtitles without downloading full video)
  // This uses the HTML5 Video element's TextTrack API in the offscreen document
  console.log('[Background] Attempting video-based subtitle extraction (primary method)...');
  sendExtractProgress(tabId, messageId, 5, 'Loading video for subtitle extraction...');
  try {
    const videoTracks = applyLangHints(await extractSubtitlesViaVideoOffscreen(streamUrl, extractionMode, messageId, tabId));
    if (videoTracks && videoTracks.length > 0) {
      console.log(`[Background] Video-based extraction succeeded: ${videoTracks.length} track(s)`);
      sendExtractProgress(tabId, messageId, 100, `Extracted ${videoTracks.length} track(s) via video element`);
      return videoTracks;
    }
    sendExtractProgress(tabId, messageId, 12, 'Video element found no text tracks; switching to FFmpeg fallback...');
    console.log('[Background] Video-based extraction returned no tracks, falling back to FFmpeg method...');
  } catch (videoErr) {
    const reason = videoErr?.message || String(videoErr);
    console.warn('[Background] Video-based extraction failed, falling back to FFmpeg method:', reason);
    sendExtractProgress(tabId, messageId, 12, `Video extraction failed (${reason}); switching to FFmpeg fallback...`);
    sendDebugLog(tabId, messageId, `Video extraction failed (${reason}), trying FFmpeg fallback...`, 'warn');
  }

  // FALLBACK METHOD: FFmpeg-based extraction from sample
  console.log('[Background] Using FFmpeg fallback method (sample-based extraction)...');
  sendExtractProgress(tabId, messageId, 15, 'Video method unavailable, using FFmpeg fallback...');
  let sample;
  try {
    sample = isHls
      ? await fetchHlsSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(60, Math.round(p * 0.6)), `Downloading HLS sample from ${hostLabel}...`), {}, baseHeaders)
      : await fetchByteRangeSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(60, p), `Downloading sample from ${hostLabel}...`));
  } catch (err) {
    console.error('[Background] Sample fetch failed:', err?.message || err);
    throw new Error(`Failed to fetch media from ${hostLabel}: ${err?.message || err}`);
  }
  let buffer = sample?.buffer || sample;
  let sampleBytes = buffer?.byteLength || 0;
  const sampleMb = Math.round((sampleBytes / (1024 * 1024)) * 10) / 10;
  console.log('[Background] Sample ready for demux:', { sizeMb: sampleMb, bytes: sampleBytes, partial: sample?.partial });
  sendDebugLog(tabId, messageId, `Sample fetched (~${sampleMb} MB). Running FFmpeg demux...`, 'info');
  if (!buffer || sampleBytes === 0) {
    throw new Error(`Stream sample from ${hostLabel} returned 0 bytes; cannot demux.`);
  }
  if (sampleBytes > 20 * 1024 * 1024) {
    console.warn('[Background] Sample size is large; chunking to offscreen demux (no automatic mode reduction).');
  }

  sendExtractProgress(tabId, messageId, 70, 'Demuxing subtitle streams...');
  console.log('[Background] Delegating demux to offscreen document...');
  try {
    let tracks = await demuxSubtitlesOffscreen(buffer, messageId, tabId);
    tracks = applyLangHints(tracks, sample?.subtitleLangs);
    if (!tracks || !tracks.length) {
      throw new Error('FFmpeg demux returned no tracks');
    }
    // Guard against flattened/non-monotonic cues (common with HLS discontinuities when manifest is ignored)
    const { flatCueStarts, nonMonotonicCues } = analyzeCueTimelines(tracks);
    if (flatCueStarts || nonMonotonicCues) {
      sendDebugLog(tabId, messageId, `Detected ${flatCueStarts ? 'flat' : 'non-monotonic'} cue timestamps after demux; retrying via video element fallback...`, 'warn');
      try {
        const safeTracks = applyLangHints(await extractSubtitlesViaVideoOffscreen(streamUrl, 'smart', messageId, tabId));
        if (safeTracks?.length) {
          sendDebugLog(tabId, messageId, 'Video fallback succeeded; returning re-extracted tracks.', 'info');
          return safeTracks;
        }
      } catch (reextractErr) {
        sendDebugLog(tabId, messageId, `Video fallback failed (${reextractErr?.message || reextractErr}); keeping demux result.`, 'warn');
      }
    }

    // Check if tracks are too small (< 20KB) regardless of whether sample is partial
    // This ensures we always get complete subtitle files as a proper fallback
    let totalBytes = sample?.totalBytes || null;
    let durationSec = sample?.durationSec || null;
    let { minTrackSize, lastCueSec } = summarizeTracks(tracks);
    const fullFetchDone = sample?.partial === false && sampleBytes > 0 && (!totalBytes || sampleBytes >= totalBytes * 0.9);
    const MIN_SUB_BYTES = 20 * 1024;
    const logDemuxSummary = () => {
      const parts = [
        `min track ${Math.round(minTrackSize / 1024)}KB`,
        `last cue ${lastCueSec ? Math.round(lastCueSec) + 's' : 'n/a'}`,
        `duration ${durationSec ? Math.round(durationSec) + 's' : 'n/a'}`,
        `partial ${sample?.partial ? 'yes' : 'no'}`,
        `fullFetch ${fullFetchDone ? 'yes' : 'no'}`
      ];
      sendDebugLog(tabId, messageId, `Demux summary: ${parts.join(', ')}`, 'info');
      console.log('[Background] Demux summary ->', { minTrackSize, lastCueSec, durationSec, partial: sample?.partial, fullFetchDone });
    };
    logDemuxSummary();

    let triedTailAugment = false;
    const tryTailAugment = async () => {
      if (triedTailAugment) return false;
      triedTailAugment = true;
      try {
        const tailBytes = Math.max(96 * 1024 * 1024, sampleBytes);
        sendDebugLog(tabId, messageId, `Coverage looks short (last cue ${lastCueSec || 'n/a'}s vs duration ${durationSec || 'n/a'}s); fetching tail slice (~${Math.round(tailBytes / (1024 * 1024))} MB) to merge...`, 'warn');
        const tail = await fetchTailSample(streamUrl, tailBytes, (p) => sendExtractProgress(tabId, messageId, Math.min(88, 76 + Math.round(p * 0.06)), 'Fetching tail slice to complete subtitles...'), baseHeaders);
        const combined = concatBuffers(buffer, tail.buffer);
        let combinedTracks = await demuxSubtitlesOffscreen(combined, messageId, tabId);
        combinedTracks = applyLangHints(combinedTracks, sample?.subtitleLangs || tail?.subtitleLangs);
        const combinedSummary = summarizeTracks(combinedTracks);
        const improved = (combinedSummary.lastCueSec && (!lastCueSec || combinedSummary.lastCueSec > lastCueSec + 30)) ||
          (combinedSummary.minTrackSize > minTrackSize);
        if (improved) {
          buffer = combined;
          tracks = combinedTracks;
          sampleBytes = combined.byteLength || combined.buffer?.byteLength || sampleBytes;
          totalBytes = totalBytes || tail.totalBytes || null;
          durationSec = durationSec || probeContainerDuration(combined) || null;
          minTrackSize = combinedSummary.minTrackSize;
          lastCueSec = combinedSummary.lastCueSec;
          sendDebugLog(tabId, messageId, 'Tail slice merge improved coverage; using merged demux result.', 'info');
          logDemuxSummary();
          return true;
        }
        sendDebugLog(tabId, messageId, 'Tail slice merge did not improve coverage; keeping original demux.', 'warn');
      } catch (tailMergeErr) {
        console.warn('[Background] Tail merge attempt failed:', tailMergeErr?.message || tailMergeErr);
      }
      return false;
    };

    // Guard: keep fetching more video while subtitles stay under 20KB.
    // Stop if size exceeds threshold or two consecutive fetches produce the same size.
    let guardFetches = 0;
    let stableSizeFetches = 0;
    const MAX_GUARD_FETCHES = 4;
    let prevSize = minTrackSize;

    const runGuardFetch = async () => {
      guardFetches += 1;
      const growthFactor = guardFetches === 1 ? 1.6 : 2.25;
      const progressHint = Math.min(88, 72 + guardFetches * 4);

      if (isHls) {
        const baseTarget = 900;
        const minDurationSec = Math.min(1800, Math.round(baseTarget * (1 + guardFetches * 0.75)));
        sendDebugLog(tabId, messageId, `Subtitles under 20KB; grabbing ~${Math.round(minDurationSec / 60)}min of HLS for retry (${guardFetches})...`, 'warn');
        const expanded = await fetchHlsSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(90, progressHint + Math.round(p * 0.05)), `Fetching extra HLS video (${guardFetches})...`), { minDurationSec }, baseHeaders);
        sample = { ...(sample || {}), buffer: expanded.buffer, durationSec: expanded.durationSec || durationSec };
      } else {
        const targetBytes = Math.min(256 * 1024 * 1024, Math.max(MIN_SUB_BYTES * 4, Math.round(sampleBytes * growthFactor)));
        sendDebugLog(tabId, messageId, `Subtitles under 20KB; expanding sample to ~${Math.round(targetBytes / (1024 * 1024))} MB (attempt ${guardFetches})...`, 'warn');
        const expanded = await fetchByteRangeSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(90, progressHint + Math.round(p * 0.05)), `Fetching extra video (${guardFetches})...`), { minBytes: targetBytes });
        sample = expanded;
        sampleBytes = expanded?.buffer?.byteLength || expanded?.byteLength || sampleBytes;
        totalBytes = expanded?.totalBytes ?? totalBytes;
        durationSec = expanded?.durationSec ?? durationSec;
      }

      buffer = sample?.buffer || sample;
      sampleBytes = buffer?.byteLength || sampleBytes;
      let retryTracks = await demuxSubtitlesOffscreen(buffer, messageId, tabId);
      retryTracks = applyLangHints(retryTracks, sample?.subtitleLangs);
      const summary = summarizeTracks(retryTracks);
      const sizeUnchanged = summary.minTrackSize === prevSize;
      stableSizeFetches = sizeUnchanged ? stableSizeFetches + 1 : 0;
      prevSize = summary.minTrackSize;
      minTrackSize = summary.minTrackSize;
      lastCueSec = summary.lastCueSec;
      tracks = retryTracks;
    };

    const hasGoodCoverage = () => durationSec && lastCueSec && lastCueSec >= durationSec * 0.9;
    if (hasGoodCoverage()) {
      sendDebugLog(tabId, messageId, 'Coverage looks complete (last cue near duration); returning tracks without further fetches.', 'info');
      return tracks;
    }
    if (durationSec && lastCueSec && lastCueSec < durationSec * 0.9 && !fullFetchDone) {
      await tryTailAugment();
      if (hasGoodCoverage()) {
        sendDebugLog(tabId, messageId, 'Coverage became complete after tail merge; returning tracks.', 'info');
        return tracks;
      }
    }

    while (minTrackSize < MIN_SUB_BYTES && guardFetches < MAX_GUARD_FETCHES && stableSizeFetches < 2 && !hasGoodCoverage()) {
      await runGuardFetch();
      if (hasGoodCoverage()) {
        sendDebugLog(tabId, messageId, 'Coverage became complete after guard fetch; returning tracks.', 'info');
        break;
      }
      logDemuxSummary();
      if (minTrackSize >= MIN_SUB_BYTES) break;
    }

    const tooSmall = minTrackSize < MIN_SUB_BYTES; // smaller than 20 KB suggests incomplete extraction
    const durationSuggestsTruncation = durationSec && lastCueSec && lastCueSec < durationSec * 0.6;
    const partialEarlyEnd = sample?.partial && lastCueSec && lastCueSec < 900; // partial head sample that ends very early
    sendDebugLog(tabId, messageId, `Demux summary: min track ${Math.round(minTrackSize / 1024)}KB; last cue ${lastCueSec ? Math.round(lastCueSec) + 's' : 'n/a'}; duration ${durationSec ? Math.round(durationSec) + 's' : 'n/a'}; partial ${sample?.partial ? 'yes' : 'no'}`, 'info');
    const allowUnknownSizeFullFetch = !totalBytes && sampleBytes && sampleBytes <= 256 * 1024 * 1024;
    const canFullFetch = totalBytes && totalBytes <= 512 * 1024 * 1024;

    // Heuristic: if we still have tiny tracks OR no duration info (likely MKV) and tracks are under 60KB, force “tryable” strategies before a full fetch.
    const looksIncomplete = (tooSmall && !fullFetchDone) ||
      durationSuggestsTruncation ||
      (!durationSec && minTrackSize < 60 * 1024) ||
      partialEarlyEnd;

    if (looksIncomplete) {
      sendDebugLog(tabId, messageId, `Tracks look incomplete (min size: ${Math.round(minTrackSize / 1024)}KB, last cue: ${lastCueSec || 'n/a'}s). Trying targeted MKV strategies...`, 'warn');
      try {
        const targeted = await tryTargetedMkvStrategies({
          streamUrl,
          sampleBuffer: buffer,
          sampleBytes,
          messageId,
          tabId,
          hostLabel,
          durationSec,
          totalBytes,
          minTrackSize,
          lastCueSec,
          contentType: sample?.contentType
        });
        if (targeted) {
          return targeted;
        }
      } catch (mkErr) {
        console.warn('[Background] Targeted MKV strategies failed:', mkErr?.message || mkErr);
      }
    }

    // If tracks are too small or truncated, try to get more data
    // This applies regardless of whether the initial fetch was partial
    if (tooSmall || durationSuggestsTruncation || partialEarlyEnd) {
      console.warn('[Background] Tracks look incomplete (small size or early end time); attempting to fetch more data');
      sendDebugLog(tabId, messageId, `Tracks incomplete (min size: ${Math.round(minTrackSize / 1024)}KB); expanding sample...`, 'warn');

      // First try expanding if the initial sample was partial
      if (sample?.partial) {
        try {
          const expanded = await fetchByteRangeSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(85, p), `Downloading larger sample from ${hostLabel}...`));
          const expandedBytes = expanded?.buffer?.byteLength || 0;
          const expandedMb = Math.round((expandedBytes / (1024 * 1024)) * 10) / 10;
          sendDebugLog(tabId, messageId, `Retrying demux with expanded sample (~${expandedMb} MB)...`, 'info');
          let expandedTracks = await demuxSubtitlesOffscreen(expanded.buffer, messageId, tabId);
          expandedTracks = applyLangHints(expandedTracks, expanded?.subtitleLangs || sample?.subtitleLangs);
          const { minTrackSize: expandedMin } = summarizeTracks(expandedTracks);
          if (expandedMin >= 20 * 1024) {
            console.log(`[Background] Expanded sample succeeded (${Math.round(expandedMin / 1024)}KB per track)`);
            return expandedTracks;
          }
          console.warn('[Background] Expanded sample still too small; trying full fetch');
        } catch (expandErr) {
          console.warn('[Background] Expanded sample fetch failed:', expandErr?.message);
        }
      }

      // Try full fetch if reasonable size (use a capped guess when total size is unknown)
      if (canFullFetch || allowUnknownSizeFullFetch) {
        console.warn('[Background] Attempting full fetch for complete demux');
        sendDebugLog(tabId, messageId, canFullFetch
          ? 'Fetching full stream for complete subtitles...'
          : 'Total size unknown; fetching full stream up to capped buffer for complete subtitles...', 'warn');
        const fullRes = await safeFetch(streamUrl);
        if (!fullRes.ok) {
          throw new Error(`Full fetch failed (HTTP ${fullRes.status})`);
        }
        const fullBuf = await fullRes.arrayBuffer();
        const fullMb = Math.round((fullBuf.byteLength / (1024 * 1024)) * 10) / 10;
        sendDebugLog(tabId, messageId, `Retrying demux with full stream (~${fullMb} MB)...`, 'info');
        const fullTracks = applyLangHints(await demuxSubtitlesOffscreen(fullBuf, messageId, tabId), sample?.subtitleLangs);
        const { minTrackSize: fullMin, lastCueSec: fullLast } = summarizeTracks(fullTracks);
        const improved = (durationSuggestsTruncation && fullLast && (!lastCueSec || fullLast > lastCueSec)) || fullMin >= minTrackSize;
        if (improved) {
          console.log(`[Background] Full fetch succeeded (${Math.round(fullMin / 1024)}KB per track)`);
          return fullTracks;
        }
        console.warn('[Background] Full fetch did not improve tracks; using original');
      }
    }
    return tracks;
  } catch (err) {
    if (sample?.partial) {
      console.warn('[Background] Demux failed on partial sample; retrying with tail slice / larger sample:', err?.message || err);
      sendDebugLog(tabId, messageId, 'Partial sample demux failed. Fetching tail slice to retry...', 'warn');
      const attemptErrors = [err?.message || String(err)];
      let tail = null;
      try {
        // Increased tail limit to ensure better coverage for subtitle extraction
        const tailLimit = Math.max(32 * 1024 * 1024, sampleBytes);
        tail = await fetchTailSample(streamUrl, tailLimit, (p) => sendExtractProgress(tabId, messageId, Math.min(85, p), `Downloading tail slice from ${hostLabel}...`), baseHeaders);
        const tailMb = Math.round(((tail?.buffer?.byteLength || 0) / (1024 * 1024)) * 10) / 10;
        sendDebugLog(tabId, messageId, `Retrying demux with tail slice (~${tailMb} MB)...`, 'info');
        try {
          return await demuxSubtitlesOffscreen(tail.buffer, messageId, tabId);
        } catch (tailOnlyErr) {
          attemptErrors.push(tailOnlyErr?.message || String(tailOnlyErr));
          console.warn('[Background] Tail-only demux failed; expanding head sample:', tailOnlyErr?.message || tailOnlyErr);
        }

        // Try head+tail combined before fetching a larger head
        if (tail?.buffer) {
          sendDebugLog(tabId, messageId, 'Tail slice did not demux. Combining head + tail...', 'warn');
          const combined = new Uint8Array(sampleBytes + tail.buffer.byteLength);
          combined.set(new Uint8Array(buffer), 0);
          combined.set(new Uint8Array(tail.buffer), sampleBytes);
          const combinedMb = Math.round((combined.byteLength / (1024 * 1024)) * 10) / 10;
          try {
            return await demuxSubtitlesOffscreen(combined, messageId, tabId);
          } catch (comboErr) {
            attemptErrors.push(comboErr?.message || String(comboErr));
            console.warn('[Background] Head+tail demux failed; fetching larger head sample:', comboErr?.message || comboErr);
          }
        }

        sendDebugLog(tabId, messageId, 'Head/tail samples did not demux. Grabbing larger head sample...', 'warn');
        const expanded = await fetchByteRangeSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(92, p), `Downloading larger sample from ${hostLabel}...`));
        const expandedBytes = expanded?.buffer?.byteLength || 0;
        const expandedMb = Math.round((expandedBytes / (1024 * 1024)) * 10) / 10;
        sendDebugLog(tabId, messageId, `Retrying demux with expanded head sample (~${expandedMb} MB)...`, 'info');
        try {
          return await demuxSubtitlesOffscreen(expanded.buffer, messageId, tabId);
        } catch (expandedErr) {
          attemptErrors.push(expandedErr?.message || String(expandedErr));
          const total = expanded?.totalBytes || null;
          // Try expanded head + tail if we have one and haven't combined yet
          if (tail?.buffer && expanded?.buffer) {
            try {
              sendDebugLog(tabId, messageId, 'Expanded head failed; trying expanded head + tail...', 'warn');
              const combo = new Uint8Array(expanded.buffer.byteLength + tail.buffer.byteLength);
              combo.set(new Uint8Array(expanded.buffer), 0);
              combo.set(new Uint8Array(tail.buffer), expanded.buffer.byteLength);
              const comboMb = Math.round((combo.byteLength / (1024 * 1024)) * 10) / 10;
              sendDebugLog(tabId, messageId, `Retrying demux with expanded head + tail (~${comboMb} MB)...`, 'info');
              return await demuxSubtitlesOffscreen(combo, messageId, tabId);
            } catch (comboExpandedErr) {
              attemptErrors.push(comboExpandedErr?.message || String(comboExpandedErr));
              console.warn('[Background] Expanded head + tail demux failed:', comboExpandedErr?.message || comboExpandedErr);
            }
          }

          if (total && total <= 256 * 1024 * 1024) {
            console.warn('[Background] Expanded sample failed; attempting full fetch within 256MB cap');
            sendDebugLog(tabId, messageId, `Expanded sample failed. Fetching full stream (${Math.round(total / (1024 * 1024))} MB) for final attempt...`, 'warn');
            const fullRes = await safeFetch(streamUrl);
            if (!fullRes.ok) {
              throw new Error(`Full fetch failed (HTTP ${fullRes.status})`);
            }
            const fullBuf = await fullRes.arrayBuffer();
            sendDebugLog(tabId, messageId, `Retrying demux with full stream (~${Math.round((fullBuf.byteLength / (1024 * 1024)) * 10) / 10} MB)...`, 'info');
            return await demuxSubtitlesOffscreen(fullBuf, messageId, tabId);
          }
          throw expandedErr;
        }
      } catch (tailErr) {
        attemptErrors.push(tailErr?.message || String(tailErr));
        console.warn('[Background] Tail / expanded demux retry failed:', tailErr?.message || tailErr);
        throw new Error(attemptErrors.join(' | '));
      }
    }
    throw err;
  }
}

/**
 * Decode audio windows via offscreen document (Worker-capable context).
 */
async function decodeWindowsOffscreen(windows, mode, onProgress, ctx = null, opts = {}) {
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  const endOffscreen = startOffscreenSession();
  try {
    await ensureOffscreenDocument();
    const messageId = `adecode_${Date.now()}`;

    const prepared = [];
    const sharedBuffers = new WeakMap();
    const startTs = Date.now();
    let idbBuffers = 0;
    let chunkedBuffers = 0;
    let directBuffers = 0;
    let reusedBuffers = 0;
    logToPage(`Offscreen decode starting (${windows.length} window(s)); chunkBytes=${OFFSCREEN_CHUNK_BYTES}`, 'info');

    for (let i = 0; i < windows.length; i++) {
      const win = windows[i];
      let buffer = normalizeBufferForTransfer(win.buffer);
      if (!buffer) continue;
      if (buffer instanceof Blob) {
        buffer = await buffer.arrayBuffer();
      } else if (typeof buffer.arrayBuffer === 'function') {
        buffer = await buffer.arrayBuffer();
      }
      const u8 = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
      if (!u8?.byteLength) continue;

      const cacheKey = win.buffer && typeof win.buffer === 'object' ? win.buffer : u8.buffer;
      const cached = sharedBuffers.get(cacheKey);

      let transferId = cached?.transferId || null;
      let directBuffer = cached?.directBuffer || null;
      let transferMethod = cached?.transferMethod || null;

      if (!cached) {
        if (u8.byteLength > MAX_DIRECT_OFFSCREEN_BYTES) {
          const sizeMb = Math.round((u8.byteLength / (1024 * 1024)) * 10) / 10;
          try {
            const Transfer = await ensureTransferHelper();
            const id = `idb_${messageId || Date.now()}_${i}_${Math.random().toString(16).slice(2)}`;
            await Transfer.saveTransferBuffer(id, u8);
            transferId = id;
            transferMethod = 'idb';
            directBuffer = null;
            idbBuffers += 1;
            logToPage(`Stashed window buffer #${i + 1} (~${sizeMb} MB) in IDB -> ${id}`, 'info');
          } catch (stashErr) {
            const chunkRes = await sendBufferToOffscreenInChunks(u8, `${messageId}_${i}`, ctx?.tabId);
            transferId = chunkRes.transferId;
            transferMethod = 'chunks';
            directBuffer = null;
            logToPage(`Chunked window buffer #${i + 1} (~${sizeMb} MB) -> transferId ${transferId}`, 'warn');
            chunkedBuffers += 1;
          }
        } else {
          directBuffer = u8;
          transferMethod = null;
          logToPage(`Reusing direct buffer for window #${i + 1} (${u8.byteLength} bytes)`, 'debug');
          directBuffers += 1;
        }
        sharedBuffers.set(cacheKey, { transferId, directBuffer, transferMethod });
      } else {
        logToPage(`Reusing shared buffer for window #${i + 1} (${transferId ? transferMethod || 'chunked' : 'direct'})`, 'debug');
        reusedBuffers += 1;
      }

      prepared.push({
        buffer: directBuffer || undefined,
        transferId: transferId || undefined,
        transferMethod: transferMethod || undefined,
        startSec: win.startSec,
        durSec: win.durSec,
        seekToSec: win.seekToSec
      });
    }

    if (!prepared.length) {
      throw new Error('No audio windows to send to offscreen decoder');
    }
    logToPage(
      `Prepared ${prepared.length}/${windows.length} window(s) for offscreen decode (idb=${idbBuffers}, chunked=${chunkedBuffers}, direct=${directBuffers}, reused=${reusedBuffers})`,
      'info'
    );

    const { promise, cancel } = waitForOffscreenResult(messageId, 240000);
    const payload = {
      type: 'OFFSCREEN_FFMPEG_DECODE',
      messageId,
      windows: prepared,
      mode: mode || 'single',
      audioStreamIndex: Number.isInteger(opts.audioStreamIndex) ? opts.audioStreamIndex : 0
    };

    await new Promise((resolve, reject) => {
      try {
        chrome.runtime.sendMessage(payload, (resp) => {
          if (chrome.runtime.lastError) {
            return reject(new Error(chrome.runtime.lastError.message));
          }
          // Immediate response may be undefined; rely on pushed result.
          resolve(resp);
        });
      } catch (err) {
        reject(err);
      }
    });

    const result = await promise;
    cancel();
    if (!result?.success) {
      throw new Error(result?.error || 'Offscreen audio decode failed');
    }

    const audioWindows = Array.isArray(result.audioWindows) ? result.audioWindows : [];
    if (!audioWindows.length) {
      throw new Error('Offscreen audio decode returned no windows');
    }

    logToPage(`Offscreen decode finished (${audioWindows.length} window(s)) in ${Date.now() - startTs}ms`, 'info');

    const mapped = audioWindows.map((w, idx) => {
      const bytes = new Uint8Array(w.audioBytes || []);
      if (!bytes?.byteLength || bytes.byteLength < 44) {
        throw new Error(`Offscreen audio window ${idx + 1} is empty or invalid`);
      }
      return {
        audioBlob: new Blob([bytes], { type: 'audio/wav' }),
        startMs: w.startMs || 0
      };
    });

    return mapped;
  } finally {
    endOffscreen();
  }
}

/**
 * Run alass synchronization algorithm
 */
async function runFfsubsyncSync(audioData, subtitleContent, onProgress, ctx = null, options = {}) {
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  onProgress?.(18, 'Loading ffsubsync-wasm...');
  const ffsubsync = await getFfsubsync(ctx);
  if (!ffsubsync || typeof ffsubsync.align !== 'function') {
    throw new Error('ffsubsync-wasm unavailable');
  }

  // Pick the first audio window; future work: combine multiple windows if needed.
  const firstWindow = Array.isArray(audioData) ? audioData.find(w => w?.audioBlob) : null;
  const audioBlob = (firstWindow && firstWindow.audioBlob) || (audioData && audioData.audioBlob) || audioData;
  if (!audioBlob || typeof audioBlob.arrayBuffer !== 'function') {
    throw new Error('Invalid audio data for ffsubsync');
  }

  onProgress?.(32, 'Preparing audio for ffsubsync...');
  const wavBuffer = await audioBlob.arrayBuffer();

  const alignOptions = {
    frameMs: options.frameMs ?? 10,
    maxOffsetMs: options.maxOffsetMs ?? 60_000,
    vadAggressiveness: options.vadAggressiveness ?? 2,
    gss: options.gss ?? false,
    sampleRate: options.sampleRate ?? 16_000
  };

  onProgress?.(64, 'Aligning subtitles to audio (ffsubsync)...');
  let result;
  try {
    result = await ffsubsync.align({
      audio: wavBuffer,
      srtText: subtitleContent,
      options: alignOptions,
      onProgress: (p, s) => onProgress?.(Math.min(90, p), s || 'ffsubsync alignment running...')
    });
  } catch (err) {
    const msg = err?.message || String(err);
    logToPage(`ffsubsync alignment failed: ${msg}`, 'error');
    throw new Error(`ffsubsync alignment failed: ${msg}`);
  }

  if (!result || !result.srt) {
    throw new Error('ffsubsync returned empty result');
  }

  onProgress?.(95, 'ffsubsync alignment succeeded');
  logToPage(`ffsubsync alignment succeeded (offset ${result.offsetMs ?? 'n/a'}ms)`, 'info');
  return {
    result: result.srt.trim(),
    method: 'ffsubsync',
    offsetMs: result.offsetMs ?? result.offset_ms ?? 0,
    drift: result.drift ?? 1,
    confidence: result.confidence ?? 0,
    anchors: result.segments ?? result.segments_used ?? null
  };
}

async function runFingerprintPrepass(audioWindows, subtitleContent, plan, ctx, progressLogger) {
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  const windows = Array.isArray(audioWindows) ? audioWindows.filter(w => w?.audioBlob) : [];
  if (!windows.length) {
    logToPage('Skipping fingerprint pre-pass (no audio windows)', 'warn');
    return { subtitleContent, applied: false };
  }

  const sampleWindows = windows.slice(0, 3);
  try {
    const prepassStart = 54;
    const prepassSpan = 5;
    progressLogger?.(prepassStart, 'Fingerprint pre-pass: coarse ffsubsync offset...');
    logToPage(`Fingerprint pre-pass running on ${sampleWindows.length} window(s)...`, 'info');
    const coarse = await runFfsubsyncSync(sampleWindows, subtitleContent, (p, status) => {
      const clamped = Math.max(0, Math.min(100, p || 0));
      const pct = prepassStart + (clamped * (prepassSpan / 100));
      progressLogger?.(pct, status || 'Fingerprint pre-pass running...');
    }, ctx, { frameMs: 20, maxOffsetMs: 15 * 60 * 1000, vadAggressiveness: 3, gss: true });

    const offsetMs = Number.isFinite(coarse?.offsetMs) ? Math.round(coarse.offsetMs) : 0;
    if (offsetMs) {
      const adjusted = offsetSubtitles(subtitleContent, offsetMs);
      const label = plan?.modeGroup || plan?.preset || 'autosync';
      logToPage(`Fingerprint pre-pass applied coarse offset ${offsetMs}ms before ${label}`, 'info');
      progressLogger?.(prepassStart + prepassSpan, `Fingerprint pre-pass applied ${offsetMs}ms`);
      return { subtitleContent: adjusted, offsetMs, applied: true, method: 'ffsubsync' };
    }

    logToPage('Fingerprint pre-pass completed (no offset change)', 'info');
    return { subtitleContent, offsetMs: 0, applied: false, method: 'ffsubsync' };
  } catch (err) {
    logToPage(`Fingerprint pre-pass skipped: ${err?.message || err}`, 'warn');
    return { subtitleContent, applied: false, error: err };
  }
}

async function inspectWavBuffer(input) {
  const toUint8 = async () => {
    if (!input) return null;
    if (input instanceof Uint8Array) return input;
    if (input instanceof ArrayBuffer) return new Uint8Array(input);
    if (ArrayBuffer.isView(input)) {
      return new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
    }
    if (typeof input.arrayBuffer === 'function') {
      const buf = await input.arrayBuffer();
      return new Uint8Array(buf);
    }
    return null;
  };

  const u8 = await toUint8();
  if (!u8 || !u8.byteLength) {
    return { ok: false, reason: 'empty buffer', bytes: 0 };
  }

  const view = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
  const bytes = view.byteLength;
  if (bytes < 44) {
    return { ok: false, reason: 'buffer too small', bytes };
  }

  const readTag = (off) => String.fromCharCode(
    view.getUint8(off),
    view.getUint8(off + 1),
    view.getUint8(off + 2),
    view.getUint8(off + 3)
  );

  if (readTag(0) !== 'RIFF' || readTag(8) !== 'WAVE') {
    return { ok: false, reason: 'missing RIFF/WAVE header', bytes };
  }

  let offset = 12;
  let fmt = null;
  let dataChunk = null;
  while (offset + 8 <= bytes) {
    const id = readTag(offset);
    const size = view.getUint32(offset + 4, true);
    const next = offset + 8 + size;
    if (id === 'fmt ') {
      fmt = {
        audioFormat: view.getUint16(offset + 8, true),
        channels: view.getUint16(offset + 10, true),
        sampleRate: view.getUint32(offset + 12, true),
        byteRate: view.getUint32(offset + 16, true),
        blockAlign: view.getUint16(offset + 20, true),
        bitsPerSample: view.getUint16(offset + 22, true)
      };
    } else if (id === 'data') {
      dataChunk = { offset, size };
    }
    if (next <= offset) break;
    offset = next;
  }

  if (!fmt) {
    return { ok: false, reason: 'missing fmt chunk', bytes };
  }
  if (!dataChunk) {
    return { ok: false, reason: 'missing data chunk', bytes, fmt };
  }

  const dataStart = dataChunk.offset + 8;
  const dataBytes = Math.max(0, Math.min(dataChunk.size, bytes - dataStart));
  if (!dataBytes) {
    return { ok: false, reason: 'no audio samples found', bytes, fmt, dataBytes: 0 };
  }

  const frameBytes = Math.max(1, (fmt.channels || 1) * Math.max(1, fmt.bitsPerSample || 16) / 8);
  const samples = Math.floor(dataBytes / frameBytes);
  const durationMs = (fmt.sampleRate && samples)
    ? Math.round((samples / fmt.sampleRate) * 1000)
    : null;

  return {
    ok: true,
    bytes,
    fmt,
    dataBytes,
    dataOffset: dataStart,
    samples,
    durationMs,
    reason: null
  };
}

async function stitchWavWindows(windows, ctx = null) {
  const sorted = Array.isArray(windows) ? [...windows].sort((a, b) => {
    const aStart = Number.isFinite(a?.startMs) ? a.startMs : Number.isFinite(a?.startSec) ? a.startSec * 1000 : 0;
    const bStart = Number.isFinite(b?.startMs) ? b.startMs : Number.isFinite(b?.startSec) ? b.startSec * 1000 : 0;
    return aStart - bStart;
  }) : [];

  const chunks = [];
  let baseFmt = null;
  let totalDataBytes = 0;

  const toUint8 = async (input) => {
    if (!input) return null;
    if (input instanceof Uint8Array) return input;
    if (input instanceof ArrayBuffer) return new Uint8Array(input);
    if (ArrayBuffer.isView(input)) return new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
    if (typeof input.arrayBuffer === 'function') {
      const buf = await input.arrayBuffer();
      return new Uint8Array(buf);
    }
    return null;
  };

  for (let i = 0; i < sorted.length; i++) {
    const win = sorted[i];
    const src = win?.audioBlob || win?.audio || win;
    if (!src) continue;
    const meta = await inspectWavBuffer(src);
    if (!meta?.ok || !meta?.dataBytes || typeof meta.dataOffset !== 'number') {
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Skipping audio window ${i + 1}: invalid WAV metadata (${meta?.reason || 'unknown'})`, 'warn');
      }
      continue;
    }
    if (!baseFmt) {
      baseFmt = meta.fmt;
    } else if (
      meta.fmt?.sampleRate !== baseFmt.sampleRate ||
      meta.fmt?.channels !== baseFmt.channels ||
      meta.fmt?.bitsPerSample !== baseFmt.bitsPerSample
    ) {
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Skipping audio window ${i + 1}: format mismatch (${meta.fmt?.sampleRate || '?'}Hz ${meta.fmt?.channels || '?'}ch ${meta.fmt?.bitsPerSample || '?'}b)`, 'warn');
      }
      continue;
    }
    const u8 = await toUint8(src);
    if (!u8 || u8.byteLength < meta.dataOffset + meta.dataBytes) {
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, `Skipping audio window ${i + 1}: unexpected buffer size`, 'warn');
      }
      continue;
    }
    const slice = u8.subarray(meta.dataOffset, meta.dataOffset + meta.dataBytes);
    chunks.push(slice);
    totalDataBytes += slice.byteLength;
  }

  if (!chunks.length || !baseFmt) {
    throw new Error('No usable audio windows to combine');
  }

  const channels = baseFmt.channels || 1;
  const bitsPerSample = baseFmt.bitsPerSample || 16;
  const sampleRate = baseFmt.sampleRate || 16000;
  const headerSize = 44;
  const frameBytes = Math.max(1, channels * Math.max(1, bitsPerSample) / 8);
  const buffer = new ArrayBuffer(headerSize + totalDataBytes);
  const view = new DataView(buffer);
  const out = new Uint8Array(buffer);

  out.set([82, 73, 70, 70], 0); // 'RIFF'
  view.setUint32(4, headerSize - 8 + totalDataBytes, true);
  out.set([87, 65, 86, 69], 8); // 'WAVE'
  out.set([102, 109, 116, 32], 12); // 'fmt '
  view.setUint32(16, 16, true);
  view.setUint16(20, 1, true); // PCM
  view.setUint16(22, channels, true);
  view.setUint32(24, sampleRate, true);
  view.setUint32(28, sampleRate * channels * (bitsPerSample / 8), true);
  view.setUint16(32, channels * (bitsPerSample / 8), true);
  view.setUint16(34, bitsPerSample, true);
  out.set([100, 97, 116, 97], 36); // 'data'
  view.setUint32(40, totalDataBytes, true);

  let offset = headerSize;
  for (const chunk of chunks) {
    out.set(chunk, offset);
    offset += chunk.byteLength;
  }

  const durationMs = sampleRate ? Math.round((totalDataBytes / frameBytes) / sampleRate * 1000) : null;
  return { blob: new Blob([buffer], { type: 'audio/wav' }), bytes: buffer.byteLength, durationMs };
}

function summarizeWavDiagnostics(diagnostics) {
  return diagnostics.map((m, idx) => {
    if (!m?.ok) return `#${idx + 1}:invalid (${m?.reason || 'unknown'})`;
    const hz = m?.fmt?.sampleRate ? `${m.fmt.sampleRate}Hz` : 'n/a';
    const ch = m?.fmt?.channels ? `${m.fmt.channels}ch` : 'n/a';
    const bits = m?.fmt?.bitsPerSample ? `${m.fmt.bitsPerSample}b` : 'n/a';
    const dur = Number.isFinite(m?.durationMs) ? `${Math.round(m.durationMs / 1000)}s` : 'n/a';
    return `#${idx + 1}:ok ${hz} ${ch} ${bits} ${dur}`;
  }).join('; ');
}

async function inspectAndFilterWavWindows(windows, ctx = null, logLabel = 'audio inspect') {
  const diagnostics = [];
  const valid = [];
  for (let i = 0; i < windows.length; i++) {
    const w = windows[i];
    const src = w?.audioBlob || w?.audio || w;
    const meta = await inspectWavBuffer(src);
    diagnostics.push(meta);
    if (meta?.ok) {
      valid.push(w);
    }
  }

  if (ctx?.tabId && diagnostics.length) {
    const summary = summarizeWavDiagnostics(diagnostics);
    const level = diagnostics.some(d => !d?.ok) ? 'warn' : 'info';
    const prefix = logLabel ? `${logLabel}: ` : '';
    sendDebugLog(ctx.tabId, ctx.messageId, `${prefix}${summary}`, level);
    const invalids = diagnostics
      .map((d, idx) => ({ idx: idx + 1, reason: d?.reason, durationMs: d?.durationMs, sampleRate: d?.fmt?.sampleRate }))
      .filter(d => d.reason);
    if (invalids.length) {
      sendDebugLog(ctx.tabId, ctx.messageId, `${logLabel} invalid detail: ${JSON.stringify(invalids)}`, 'warn');
    }
  }

  return {
    validWindows: valid,
    diagnostics,
    summary: diagnostics.length ? summarizeWavDiagnostics(diagnostics) : '',
    invalidCount: diagnostics.filter(d => !d?.ok).length
  };
}

async function logAudioWindowDiagnostics(windows, ctx = null, plan = null, phaseLabel = 'audio diagnostics') {
  if (!ctx?.tabId || !Array.isArray(windows) || !windows.length) return null;
  const { diagnostics } = await inspectAndFilterWavWindows(windows, ctx, `${phaseLabel} inspect`);
  const rows = windows.map((w, idx) => {
    const meta = diagnostics[idx] || {};
    const plannedStart = Number.isFinite(w?.startSec) ? `${Math.round(w.startSec * 1000) / 1000}s` : (Number.isFinite(w?.startMs) ? `${Math.round(w.startMs) / 1000}s` : '?s');
    const plannedDur = Number.isFinite(w?.durSec) ? `${Math.round(w.durSec)}s` : (Number.isFinite(w?.durMs) ? `${Math.round(w.durMs / 1000)}s` : '?s');
    const decodedDur = Number.isFinite(meta.durationMs) ? `${Math.round(meta.durationMs / 1000)}s` : (meta.reason || 'n/a');
    const sr = meta?.fmt?.sampleRate || '?';
    const ch = meta?.fmt?.channels || '?';
    const okFlag = meta?.ok ? 'ok' : (meta?.reason || 'invalid');
    return `#${idx + 1}@${plannedStart} len=${plannedDur} -> ${decodedDur} ${sr}Hz ${ch}ch (${okFlag})`;
  });
  const plannedCount = Number.isFinite(plan?.windowCount) ? plan.windowCount : plan?.minWindows;
  const header = `Audio windows (${rows.length}${plannedCount ? ` planned ${plannedCount}` : ''}) [${phaseLabel}]`;
  sendDebugLog(ctx.tabId, ctx.messageId, `${header}: ${rows.join(' | ')}`, 'info');
  return diagnostics;
}

async function validateAlassWindows(windows, ctx) {
  return inspectAndFilterWavWindows(windows, ctx, 'alass audio inspect');
}

async function ensureVoskModel(ctx = null) {
  if (voskModelInstance && voskModelInstance.ready) return voskModelInstance;
  if (voskModelPromise) return voskModelPromise;
  voskModelPromise = (async () => {
    if (!self.Vosk) {
      await importScriptSafe(VOSK_JS_URL, 'vosk-browser.js');
    }
    if (!self.Vosk || typeof self.Vosk.createModel !== 'function') {
      throw new Error('Vosk library unavailable');
    }
    const model = await self.Vosk.createModel(VOSK_MODEL_ARCHIVE_URL);
    if (typeof model.setLogLevel === 'function') {
      model.setLogLevel(-2);
    }
    voskModelInstance = model;
    return model;
  })().catch((err) => {
    voskLoadError = err;
    voskModelPromise = null;
    throw err;
  });
  return voskModelPromise;
}

function voskWordsToSegments(words, chunkSize = 12) {
  if (!Array.isArray(words) || !words.length) return [];
  const sorted = [...words].sort((a, b) => (a.startMs || 0) - (b.startMs || 0));
  const segments = [];
  for (let i = 0; i < sorted.length; i += chunkSize) {
    const slice = sorted.slice(i, i + chunkSize);
    const startMs = Math.max(0, Math.round(slice[0].startMs || 0));
    const endMs = Math.max(startMs, Math.round(slice[slice.length - 1].endMs || startMs));
    const text = slice.map((w) => w.word || '').join(' ').trim();
    if (text) {
      segments.push({ startMs, endMs, text });
    }
  }
  return segments;
}

async function runVoskCtcAlign(audioWindows, subtitleContent, onProgress, ctx = null) {
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  const windows = Array.isArray(audioWindows)
    ? audioWindows.filter((w) => w?.audioBlob || w?.audio)
    : audioWindows
      ? [{ audioBlob: audioWindows }]
      : [];
  if (!windows.length) {
    throw new Error('No audio available for Vosk alignment');
  }
  onProgress?.(12, 'Loading Vosk model (CTC/DTW)...');
  logToPage('Loading Vosk model (CTC/DTW aligner)...', 'info');
  const model = await ensureVoskModel(ctx);
  const recognizer = new model.KaldiRecognizer(VOSK_SAMPLE_RATE);
  recognizer.setWords(true);

  const collectedWords = [];
  recognizer.on('result', (msg) => {
    const list = msg?.result?.result;
    if (Array.isArray(list)) {
      list.forEach((w) => {
        if (!w || typeof w.start !== 'number' || typeof w.end !== 'number') return;
        collectedWords.push({
          word: String(w.word || '').trim(),
          startMs: Math.round(w.start * 1000),
          endMs: Math.round(w.end * 1000),
          conf: w.conf
        });
      });
    }
  });

  let lastEndMs = 0;
  for (let i = 0; i < windows.length; i++) {
    const win = windows[i];
    const startMs = Number.isFinite(win?.startMs) ? win.startMs : lastEndMs;
    const gapMs = Math.max(0, startMs - lastEndMs);
    if (gapMs > 5) {
      const gapSamples = Math.round((gapMs / 1000) * VOSK_SAMPLE_RATE);
      recognizer.acceptWaveformFloat(new Float32Array(gapSamples), VOSK_SAMPLE_RATE);
    }
    const audioBuffer = win.audioBlob ? await win.audioBlob.arrayBuffer() : win.audio;
    const { pcm, sampleRate } = decodeWavToFloat32(audioBuffer);
    const readyPcm = resampleTo16kHz(pcm, sampleRate);
    const durationMs = Math.round((readyPcm.length / VOSK_SAMPLE_RATE) * 1000);
    onProgress?.(18 + Math.round((i / windows.length) * 50), `Vosk aligning window ${i + 1}/${windows.length}...`);
    recognizer.acceptWaveformFloat(readyPcm, VOSK_SAMPLE_RATE);
    lastEndMs = startMs + durationMs;
  }

  recognizer.retrieveFinalResult();
  await new Promise((resolve) => setTimeout(resolve, 600));
  recognizer.remove();

  if (!collectedWords.length) {
    throw new Error('Vosk returned no word timings');
  }

  const segments = voskWordsToSegments(collectedWords);
  if (!segments.length) {
    throw new Error('Vosk produced no usable segments');
  }

  logToPage(`Vosk produced ${segments.length} segments (${collectedWords.length} words)`, 'info');
  const aligned = alignSubtitlesWithTranscript(subtitleContent, segments);
  return { result: aligned, method: 'vosk-ctc', segments: segments.length, words: collectedWords.length };
}

function estimateSubtitleDurationSec(subtitleContent) {
  if (typeof subtitleContent !== 'string') return null;
  const re = /(\d{1,2}):(\d{2}):(\d{2})[,\.](\d{3})\s+-->\s+(\d{1,2}):(\d{2}):(\d{2})[,\.](\d{3})/g;
  let lastEnd = 0;
  let match;
  while ((match = re.exec(subtitleContent)) !== null) {
    const h = parseInt(match[5], 10);
    const m = parseInt(match[6], 10);
    const s = parseInt(match[7], 10);
    const ms = parseInt(match[8], 10);
    const end = (h * 3600 + m * 60 + s) * 1000 + ms;
    if (end > lastEnd) lastEnd = end;
  }
  return lastEnd ? lastEnd / 1000 : null;
}

function summarizeAudioWindowCoverage(windows, diagnostics = []) {
  if (!Array.isArray(windows) || !windows.length) {
    return { count: 0, spanMs: 0, minStartMs: 0, maxEndMs: 0, totalDurationMs: 0 };
  }

  let minStart = Number.POSITIVE_INFINITY;
  let maxEnd = 0;
  let totalDurationMs = 0;

  for (let i = 0; i < windows.length; i++) {
    const startMs = Math.max(0, Math.round(windows[i]?.startMs ?? (windows[i]?.startSec || 0) * 1000));
    const durMs = Number.isFinite(diagnostics[i]?.durationMs)
      ? Math.max(0, diagnostics[i].durationMs)
      : null;
    minStart = Math.min(minStart, startMs);
    if (Number.isFinite(durMs)) {
      maxEnd = Math.max(maxEnd, startMs + durMs);
      totalDurationMs += durMs;
    } else {
      maxEnd = Math.max(maxEnd, startMs);
    }
  }

  if (!Number.isFinite(minStart)) minStart = 0;
  const spanMs = Math.max(0, maxEnd - minStart);
  return { count: windows.length, spanMs, minStartMs: minStart, maxEndMs: maxEnd, totalDurationMs };
}

function ensureAlassCoverageSufficient(usableWindows, diagnostics, ctx, subtitleContent) {
  const plan = ctx?.plan || {};
  const expectedDurationSec = plan.durationSeconds || estimateSubtitleDurationSec(subtitleContent);
  if (!usableWindows?.length) return;

  const coverage = summarizeAudioWindowCoverage(usableWindows, diagnostics);
  const spanSec = coverage.spanMs / 1000;
  const estimatedDurationSec = expectedDurationSec || null;
  const plannedWindows = Number.isFinite(plan.windowCount) ? plan.windowCount : plan.minWindows;
  const coverageRatio = estimatedDurationSec ? (spanSec / estimatedDurationSec) : null;
  const plannedCoverageRatio = (() => {
    if (!estimatedDurationSec) return null;
    if (Number.isFinite(plan.coverageSeconds)) return plan.coverageSeconds / estimatedDurationSec;
    if (Number.isFinite(plan.coverageTargetPct)) return plan.coverageTargetPct;
    return null;
  })();

  if (ctx?.tabId) {
    const label = `alass coverage: span ~${Math.round(spanSec)}s, windows=${coverage.count}${plannedWindows ? `/${plannedWindows}` : ''}${estimatedDurationSec ? `, expected ~${Math.round(estimatedDurationSec)}s` : ''}${coverageRatio ? ` (~${Math.round(coverageRatio * 100)}% of expected)` : ''}${plannedCoverageRatio ? `, plan target ~${Math.round(plannedCoverageRatio * 100)}%` : ''}`;
    sendDebugLog(ctx.tabId, ctx.messageId, label, 'info');
  }
  console.log('[Background] alass coverage summary:', { spanSec, count: coverage.count, expectedDurationSec });

  if (!estimatedDurationSec) return; // Skip strict coverage checks for unknown durations

  const targetRatio = plannedCoverageRatio || 0.1;
  const coverageRatioStrict = spanSec / estimatedDurationSec;
  const minWindowsNeeded = Math.max(2, plannedWindows || plan.minWindows || 3);
  if (coverage.count < minWindowsNeeded) {
    throw new Error(`Insufficient audio windows for alass (${coverage.count}/${minWindowsNeeded})`);
  }
  const floorRatio = Math.max(0.05, Math.min(0.9, targetRatio * 0.7));
  if (coverageRatioStrict < floorRatio) {
    throw new Error(`Audio coverage too narrow for alass (${Math.round(coverageRatioStrict * 100)}% of ${Math.round(estimatedDurationSec)}s, target ~${Math.round(targetRatio * 100)}%)`);
  }
}

async function runAlassSync(audioData, subtitleContent, onProgress, ctx = null, options = {}) {
  console.log('[Background] Running alass alignment...');
  const logToPage = (text, level = 'info') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  logToPage('Starting alass alignment...', 'info');

  const windows = Array.isArray(audioData)
    ? audioData.filter(w => w?.audioBlob)
    : audioData
      ? [{ audioBlob: audioData instanceof Blob ? audioData : new Blob([audioData], { type: 'audio/wav' }) }]
      : [];

  if (!windows.length) {
    const errMsg = 'No audio window available for alignment';
    logToPage(errMsg, 'error');
    throw new Error(errMsg);
  }

  const { validWindows, diagnostics } = await validateAlassWindows(windows, ctx);
  const usable = validWindows.length ? validWindows : windows;
  if (!validWindows.length) {
    const reasons = diagnostics.map((d, idx) => `#${idx + 1}:${d?.reason || 'unknown'}`).join('; ');
    logToPage(`No valid WAV windows detected for alass (${reasons || 'unknown reason'})`, 'error');
    throw new Error('No valid audio samples available for alass');
  }
  try {
    ensureAlassCoverageSufficient(usable, diagnostics, ctx, subtitleContent);
  } catch (coverageErr) {
    logToPage(coverageErr.message, 'warn');
    throw coverageErr;
  }
  if (validWindows.length !== windows.length) {
    logToPage(`Filtered ${windows.length - validWindows.length} invalid audio window(s) before alass`, 'warn');
  }

  try {
    onProgress?.(45, 'Loading alass-wasm...');
    logToPage('Loading alass-wasm for direct audio alignment...', 'info');
    const alass = await getAlass(ctx);
    if (!alass || !alass.alignAudio) {
      throw new Error('alass-wasm unavailable');
    }

    onProgress?.(68, 'Aligning subtitles to audio with alass-wasm...');
    const alassRes = await alass.alignAudio(usable, subtitleContent, { allowDrift: true });
    const aligned = alassRes?.srt || alassRes;
    if (typeof aligned !== 'string' || !aligned.trim()) {
      throw new Error('alass-wasm returned empty result');
    }

    onProgress?.(95, 'alass-wasm alignment succeeded');
    logToPage(`alass-wasm alignment succeeded using ${alassRes?.anchors ?? '?'} audio anchor segment(s)`, 'info');
    return { result: aligned.trim(), method: 'alass', anchors: alassRes?.anchors };
  } catch (err) {
    console.warn('[Background] alass alignment failed:', err?.message);
    const errMsg = err?.message || String(err);
    logToPage(`alass attempt failed: ${errMsg}`, 'error');
    throw err;
  }
}

/**
 * Detect optimal offset and apply it
 * This is a placeholder for actual alass algorithm
 */
function detectAndApplyOffset(srtContent) {
  console.log('[Background] Detecting optimal offset...');

  // Parse SRT
  const subtitles = parseSRT(srtContent);

  if (subtitles.length === 0) {
    return srtContent;
  }

  // Simple heuristic: if first subtitle starts very early (< 1 second),
  // it might need a delay. If it starts late (> 30 seconds), might need to advance.
  const firstStartTime = subtitles[0].start;
  let detectedOffset = 0;

  if (firstStartTime < 1000) {
    // Starts too early, add 2 second delay
    detectedOffset = 2000;
    console.log('[Background] Detected early start, applying +2s offset');
  } else if (firstStartTime > 30000) {
    // Starts too late, advance by 1 second
    detectedOffset = -1000;
    console.log('[Background] Detected late start, applying -1s offset');
  } else {
    // Reasonable timing, apply small adjustment
    detectedOffset = 500;
    console.log('[Background] Applying standard +0.5s offset');
  }

  // Apply offset
  return offsetSubtitles(srtContent, detectedOffset);
}

const READABLE_SRT_MAX_LINE = 42;
const READABLE_SRT_MAX_LINES = 2;
const READABLE_SRT_MAX_CHARS = READABLE_SRT_MAX_LINE * READABLE_SRT_MAX_LINES;
const READABLE_SRT_MIN_MS = 800;
const READABLE_SRT_MAX_MS = 7500;
const READABLE_SRT_CPS_DEFAULT = 16;
const READABLE_SRT_CPS_SLOW = 12; // For denser languages like CJK
const READABLE_PAUSE_SPLIT_MS = 450;
const READABLE_GAP_ABSORB_MS = 400;
const READABLE_OVERLAP_TOLERANCE_MS = 120;

function cueCpsForLanguage(lang = '') {
  const lc = String(lang || '').toLowerCase();
  if (!lc) return READABLE_SRT_CPS_DEFAULT;
  if (['ja', 'jpn', 'zh', 'zho', 'ko', 'kor'].some((k) => lc.startsWith(k))) {
    return READABLE_SRT_CPS_SLOW;
  }
  return READABLE_SRT_CPS_DEFAULT;
}

function detectSpeakerId(seg) {
  return seg?.speaker || seg?.speakerId || seg?.speaker_id || seg?.spk || seg?.spkr || null;
}

function stripSpeakerPrefix(text = '') {
  if (!text) return text;
  const pattern = /^\s*(?:<v\s+[^>]+>\s*)?(?:speaker|spk|spkr|voice)\s*[._\-\s]*[0-9a-z]*\s*[:.)\]-]?\s*/i;
  return text.replace(pattern, '').replace(/<\/v>\s*$/i, '').trim();
}

function normalizeTranscriptSegment(seg) {
  if (!seg) return null;
  const startSec = Number(seg.start ?? seg.start_time ?? (seg.startMs ?? 0) / 1000) || 0;
  const endSecRaw = Number(seg.end ?? seg.end_time ?? (seg.endMs ?? 0) / 1000);
  const endSec = Number.isFinite(endSecRaw) ? endSecRaw : (startSec + 4);
  const startMs = Math.max(0, Number.isFinite(seg.startMs) ? Math.round(seg.startMs) : Math.round(startSec * 1000));
  let endMs = Number.isFinite(seg.endMs) ? Math.round(seg.endMs) : Math.round(endSec * 1000);
  if (!Number.isFinite(endMs) || endMs <= startMs) {
    endMs = startMs + READABLE_SRT_MIN_MS;
  }
  const text = stripSpeakerPrefix((seg.text || seg.transcript || '').toString().replace(/\s+/g, ' ').trim());
  if (!text) return null;
  return {
    startMs,
    endMs: Math.max(startMs + 300, endMs),
    text,
    speaker: detectSpeakerId(seg),
    language: seg.language || seg.lang || '',
    words: Array.isArray(seg.words) ? seg.words : null
  };
}

function splitTextIntoChunks(text, seg = null) {
  const cleaned = (text || '').replace(/\s+/g, ' ').trim();
  if (!cleaned) return [];
  const sentences = cleaned.split(/(?<=[\.?!])\s+(?=[A-Z0-9\[\("'])/);
  const pieces = [];
  const pushChunk = (chunk) => {
    const trimmed = (chunk || '').trim();
    if (trimmed) pieces.push(trimmed);
  };
  const splitLong = (input) => {
    const words = input.split(/\s+/);
    const chunks = [];
    let buf = [];
    let len = 0;
    for (const word of words) {
      const extra = (len ? 1 : 0) + word.length;
      if (len && len + extra > READABLE_SRT_MAX_CHARS && len >= READABLE_SRT_MAX_CHARS * 0.6) {
        chunks.push(buf.join(' '));
        buf = [word];
        len = word.length;
      } else {
        buf.push(word);
        len += extra;
      }
    }
    if (buf.length) chunks.push(buf.join(' '));
    return chunks;
  };

  for (const sentence of sentences) {
    const trimmed = (sentence || '').trim();
    if (!trimmed) continue;
    if (trimmed.length > READABLE_SRT_MAX_CHARS * 1.25) {
      splitLong(trimmed).forEach(pushChunk);
    } else {
      pushChunk(trimmed);
    }
  }

  const merged = [];
  for (const piece of pieces) {
    if (!merged.length) {
      merged.push(piece);
      continue;
    }
    const prev = merged[merged.length - 1];
    if (prev.length + 1 + piece.length <= READABLE_SRT_MAX_CHARS * 0.9) {
      merged[merged.length - 1] = `${prev} ${piece}`;
    } else {
      merged.push(piece);
    }
  }

  const hasWordTiming = Array.isArray(seg?.words) && seg.words.some((w) => Number.isFinite(w?.start) || Number.isFinite(w?.end) || Number.isFinite(w?.startMs) || Number.isFinite(w?.endMs));
  if (!hasWordTiming) return merged;

  const pauseBreaks = [];
  const words = seg.words
    .map((w) => {
      const wStart = Number.isFinite(w?.startMs) ? w.startMs : Number(w?.start || 0) * 1000;
      const wEnd = Number.isFinite(w?.endMs) ? w.endMs : Number(w?.end || 0) * 1000;
      const wText = w?.text || w?.word || '';
      return { ...w, startMs: wStart, endMs: wEnd, text: wText };
    })
    .filter((w) => Number.isFinite(w.startMs) && Number.isFinite(w.endMs) && w.endMs > w.startMs);
  for (let i = 1; i < words.length; i++) {
    const gap = words[i].startMs - words[i - 1].endMs;
    if (gap >= READABLE_PAUSE_SPLIT_MS) {
      pauseBreaks.push(words[i - 1].text || '');
    }
  }
  if (!pauseBreaks.length) return merged;

  const rebroken = [];
  for (const chunk of merged) {
    let buffer = '';
    const localWords = chunk.split(/\s+/);
    for (const w of localWords) {
      const candidate = buffer ? `${buffer} ${w}` : w;
      buffer = candidate;
      if (pauseBreaks.includes(w) || buffer.length >= READABLE_SRT_MAX_CHARS * 0.9) {
        rebroken.push(buffer);
        buffer = '';
      }
    }
    if (buffer) rebroken.push(buffer);
  }
  return rebroken;
}

function wrapCueLines(text, maxLine = READABLE_SRT_MAX_LINE, maxLines = READABLE_SRT_MAX_LINES) {
  const words = (text || '').split(/\s+/).filter(Boolean);
  if (!words.length) return '';
  const lines = [];
  let current = '';
  for (const word of words) {
    const candidate = current ? `${current} ${word}` : word;
    if (candidate.length > maxLine && current) {
      lines.push(current);
      current = word;
    } else {
      current = candidate;
    }
  }
  if (current) lines.push(current);

  if (lines.length <= maxLines) return lines.join('\n');

  const targetLen = Math.max(maxLine, Math.ceil(words.join(' ').length / maxLines));
  const reflow = [];
  current = '';
  for (const word of words) {
    const candidate = current ? `${current} ${word}` : word;
    if (candidate.length > targetLen && current) {
      reflow.push(current);
      current = word;
    } else {
      current = candidate;
    }
  }
  if (current) reflow.push(current);

  while (reflow.length > maxLines) {
    const tail = reflow.pop();
    reflow[reflow.length - 1] = `${reflow[reflow.length - 1]} ${tail}`;
  }
  return reflow.join('\n');
}

function distributeCueTimings(chunks, startMs, endMs, lang = '') {
  if (!Array.isArray(chunks) || !chunks.length) return [];
  const spanMs = Math.max(READABLE_SRT_MIN_MS, endMs - startMs);
  const cps = cueCpsForLanguage(lang);
  let durations = chunks.map((c) => {
    const idealMs = Math.max(READABLE_SRT_MIN_MS, (Math.max(c.length, 1) / cps) * 1000);
    return Math.min(READABLE_SRT_MAX_MS, idealMs);
  });

  let total = durations.reduce((a, b) => a + b, 0);
  if (total > spanMs) {
    const factor = spanMs / total;
    durations = durations.map((d) => Math.max(READABLE_SRT_MIN_MS * 0.6, d * factor));
    total = durations.reduce((a, b) => a + b, 0);
  }

  let remaining = Math.max(0, spanMs - total);
  if (remaining > 0) {
    const headroom = durations.reduce((sum, d) => sum + Math.max(0, READABLE_SRT_MAX_MS - d), 0);
    if (headroom > 0) {
      const ratio = Math.min(1, remaining / headroom);
      durations = durations.map((d) => d + Math.max(0, READABLE_SRT_MAX_MS - d) * ratio);
      remaining = Math.max(0, spanMs - durations.reduce((a, b) => a + b, 0));
    }
    if (remaining > 0) {
      durations[durations.length - 1] += remaining;
    }
  }

  const timed = [];
  let cursor = startMs;
  for (let i = 0; i < chunks.length; i++) {
    const dur = durations[i] || READABLE_SRT_MIN_MS;
    const cueEnd = i === chunks.length - 1 ? endMs : Math.min(endMs, cursor + dur);
    timed.push({ startMs: cursor, endMs: cueEnd, text: chunks[i] });
    cursor = cueEnd;
  }

  if (timed.length) {
    timed[timed.length - 1].endMs = Math.min(endMs, Math.max(timed[timed.length - 1].startMs + READABLE_SRT_MIN_MS, timed[timed.length - 1].endMs));
  }
  return timed;
}

function buildReadableCues(segments) {
  const cues = [];
  let lastEndMs = 0;

  const normalized = (segments || [])
    .map(normalizeTranscriptSegment)
    .filter(Boolean)
    .sort((a, b) => (a.startMs || 0) - (b.startMs || 0));

  normalized.forEach((seg, idx) => {
    const sameSpeakerAsPrev = idx > 0 && normalized[idx - 1].speaker && normalized[idx - 1].speaker === seg.speaker;
    const gapFromLast = seg.startMs - lastEndMs;

    // absorb micro gaps to keep flow tight, but keep clear separation on speaker switch
    let segStart = seg.startMs;
    if (gapFromLast <= READABLE_GAP_ABSORB_MS && gapFromLast >= 0) {
      segStart = sameSpeakerAsPrev ? Math.max(seg.startMs, lastEndMs) : lastEndMs;
    } else if (gapFromLast < 0) {
      segStart = lastEndMs;
    }

    let segEnd = Math.max(segStart + READABLE_SRT_MIN_MS, seg.endMs);

    const chunks = splitTextIntoChunks(seg.text, seg);
    if (!chunks.length) return;
    const timedChunks = distributeCueTimings(chunks, segStart, segEnd, seg.language);
    for (const chunk of timedChunks) {
      let cueStart = Math.max(chunk.startMs, lastEndMs);
      let cueEnd = Math.min(segEnd, Math.max(cueStart + 300, chunk.endMs));
      if (cueEnd <= cueStart) {
        cueEnd = cueStart + READABLE_SRT_MIN_MS;
      }
      cues.push({
        startMs: cueStart,
        endMs: cueEnd,
        text: wrapCueLines(chunk.text)
      });
      lastEndMs = cueEnd;
    }
  });

  // Final smoothing: ensure monotonic, trim tiny overlaps, and absorb sub-ms jitter
  for (let i = 1; i < cues.length; i++) {
    const prev = cues[i - 1];
    const curr = cues[i];
    if (curr.startMs < prev.endMs - READABLE_OVERLAP_TOLERANCE_MS) {
      curr.startMs = prev.endMs;
    }
    if (curr.endMs <= curr.startMs) {
      curr.endMs = curr.startMs + READABLE_SRT_MIN_MS;
    }
  }

  return cues;
}

function convertVttToSrt(vttText) {
  if (!vttText) return '';
  let srt = String(vttText).replace(/^WEBVTT[^\n]*\n+/i, '');
  srt = srt.replace(/\r/g, '');
  srt = srt.replace(/(\d{2}:\d{2}:\d{2})\.(\d{3})/g, '$1,$2');
  return srt.trim();
}

/**
 * Convert transcript segments (startMs/endMs/text) into SRT
 */
function segmentsToReadableSrt(segments) {
  const cues = buildReadableCues(Array.isArray(segments) ? segments : []);
  if (!cues.length) return '';
  return cues.map((cue, idx) => [
    String(idx + 1),
    `${formatTime(Math.max(0, Math.round(cue.startMs || 0)))} --> ${formatTime(Math.max(0, Math.round(cue.endMs || cue.startMs || 0)))}`,
    (cue.text || '').trim()
  ].join('\n')).join('\n\n');
}

/**
 * Parse SRT subtitle content
 */
function parseSRT(srtContent) {
  const lines = srtContent.trim().split('\n');
  const subtitles = [];
  let current = {};

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();

    if (!line) {
      if (current.index) {
        subtitles.push(current);
        current = {};
      }
      continue;
    }

    if (!current.index && /^\d+$/.test(line)) {
      current.index = parseInt(line);
    } else if (line.includes('-->')) {
      const times = line.split('-->').map(t => t.trim());
      current.start = parseTime(times[0]);
      current.end = parseTime(times[1]);
    } else if (current.start !== undefined) {
      current.text = (current.text || '') + line + '\n';
    }
  }

  if (current.index) subtitles.push(current);
  return subtitles;
}

/**
 * Parse SRT timestamp to milliseconds
 */
function parseTime(timeStr) {
  const match = timeStr.match(/(\d+):(\d+):(\d+)[,\.](\d+)/);
  if (!match) return 0;
  const hours = parseInt(match[1]);
  const minutes = parseInt(match[2]);
  const seconds = parseInt(match[3]);
  const ms = parseInt(match[4].padEnd(3, '0').substring(0, 3));
  return hours * 3600000 + minutes * 60000 + seconds * 1000 + ms;
}

/**
 * Format milliseconds to SRT timestamp
 */
function formatTime(ms) {
  if (ms < 0) ms = 0;
  const hours = Math.floor(ms / 3600000);
  const minutes = Math.floor((ms % 3600000) / 60000);
  const seconds = Math.floor((ms % 60000) / 1000);
  const milliseconds = ms % 1000;

  return `${String(hours).padStart(2, '0')}:${String(minutes).padStart(2, '0')}:${String(seconds).padStart(2, '0')},${String(milliseconds).padStart(3, '0')}`;
}

/**
 * Apply time offset to subtitle
 */
function offsetSubtitles(srtContent, offsetMs) {
  const subtitles = parseSRT(srtContent);
  let result = '';

  for (const sub of subtitles) {
    const newStart = Math.max(0, sub.start + offsetMs);
    const newEnd = Math.max(newStart, sub.end + offsetMs);

    result += `${sub.index}\n`;
    result += `${formatTime(newStart)} --> ${formatTime(newEnd)}\n`;
    result += sub.text;
    result += '\n';
  }

  return result.trim();
}

/**
 * Send progress update to content script
 */
const lastSyncProgress = new Map();

function sendProgress(tabId, messageId, progress, status) {
  if (!tabId) return;
  const pct = Math.round(progress);
  const prior = lastSyncProgress.get(messageId) || 0;
  const clamped = Math.max(prior, pct);
  lastSyncProgress.set(messageId, clamped);

  chrome.tabs.sendMessage(tabId, {
    type: 'SYNC_PROGRESS',
    messageId: messageId,
    progress: clamped,
    status: status
  }).catch(err => {
    console.error('[Background] Failed to send progress:', err);
  });
}

function sendExtractProgress(tabId, messageId, progress, status) {
  if (!tabId) return;

  chrome.tabs.sendMessage(tabId, {
    type: 'EXTRACT_PROGRESS',
    messageId,
    progress: Math.round(progress),
    status
  }).catch(err => {
    console.error('[Background] Failed to send extract progress:', err);
  });
}

function sendExtractResult(tabId, messageId, payload) {
  if (!tabId) return;
  chrome.tabs.sendMessage(tabId, {
    type: 'EXTRACT_RESPONSE',
    messageId,
    ...payload
  }).catch(err => {
    console.error('[Background] Failed to send extract result:', err);
  });
}

function sendAutoSubProgress(tabId, messageId, progress, status, stage = 'info', level = 'info') {
  if (!tabId) return;
  chrome.tabs.sendMessage(tabId, {
    type: 'AUTOSUB_PROGRESS',
    messageId,
    progress: Math.round(progress),
    status,
    stage,
    level
  }).catch(err => {
    console.error('[Background] Failed to send auto-sub progress:', err);
  });
}

function sendAutoSubResult(tabId, messageId, payload) {
  if (!tabId) return;
  chrome.tabs.sendMessage(tabId, {
    type: 'AUTOSUB_RESPONSE',
    messageId,
    ...payload
  }).catch(err => {
    console.error('[Background] Failed to send auto-sub result:', err);
  });
}

function sendDebugLog(tabId, messageId, text, level = 'info') {
  // Always emit logs tied to a specific job so tool pages can surface background activity,
  // even when verbose mode is toggled off.
  const allow = shouldBroadcastLevel(level, !!messageId);
  if (!tabId || !allow) return;
  chrome.tabs.sendMessage(tabId, {
    type: 'SUBMAKER_DEBUG_LOG',
    messageId,
    text,
    level,
    ts: Date.now()
  }).catch(err => {
    console.warn('[Background] Failed to send debug log:', err?.message || err);
  });
}

function pollDebug(tabId, messageId, text) {
  sendDebugLog(tabId, messageId, text, 'info');
}

// Relay logs coming from offscreen context
chrome.runtime.onMessage.addListener((msg, sender, sendResponse) => {
  if (msg?.type === 'OFFSCREEN_RESULT_CHUNK') {
    const res = stashResultChunk(msg.transferId, msg.chunkIndex, msg.totalChunks, msg.chunkArray, msg.expectedBytes);
    const shouldLog = msg.totalChunks <= 20 || msg.chunkIndex === 0 || msg.chunkIndex === msg.totalChunks - 1 || ((msg.chunkIndex + 1) % 25 === 0);
    if (shouldLog) {
      console.log('[Background][Offscreen] Result chunk received', {
        transferId: msg.transferId,
        idx: msg.chunkIndex + 1,
        total: msg.totalChunks,
        complete: res?.complete,
        label: msg.label
      });
    }
    try {
      sendResponse?.(res);
    } catch (_) { }
    return true;
  }

  if (msg?.type === 'OFFSCREEN_LOG') {
    const level = msg.level || 'info';
    if (!shouldBroadcastLevel(level, !!msg.messageId)) return;
    console.log('[Background][Offscreen]', level, msg.text || '', msg.messageId ? `(job ${msg.messageId})` : '');
    // Best effort broadcast: target active extract job tab if known
    const active = [...activeExtractJobs.values()].find(j => j?.messageId === msg?.messageId) || [...activeExtractJobs.values()][0];
    const tabId = active?.tabId;
    if (tabId) {
      sendDebugLog(tabId, active?.messageId, msg.text, level);
    }
  }

  if (msg?.type === 'OFFSCREEN_FFMPEG_RESULT') {
    if (debugEnabled()) {
      console.log('[Background][Offscreen] Result received', {
        messageId: msg.messageId,
        success: msg.success,
        trackCount: msg.tracks?.length,
        error: msg.error
      });
    }
    const active = [...activeExtractJobs.values()].find(j => j?.messageId === msg?.messageId) || [...activeExtractJobs.values()][0];
    if (active?.tabId) {
      const logText = msg.success
        ? `Offscreen demux result: ${msg.tracks?.length || 0} track(s)`
        : `Offscreen demux error: ${msg.error || 'unknown error'}`;
      sendDebugLog(active.tabId, active.messageId, logText, msg.success ? 'info' : 'error');
    }
  }
});

// ---------- Helpers: Fetching and HLS ----------
function parseContentRangeTotal(headerValue) {
  if (!headerValue) return null;
  const match = String(headerValue).match(/bytes\s+\d+-\d+\/(\d+)/i);
  if (match && match[1]) {
    const total = parseInt(match[1], 10);
    return Number.isFinite(total) && total > 0 ? total : null;
  }
  return null;
}

function probeMp4Duration(buffer) {
  try {
    const view = new DataView(buffer);
    const len = view.byteLength;
    let offset = 0;

    const readSize = (off) => {
      const size32 = view.getUint32(off);
      if (size32 === 1 && off + 16 <= len) {
        // 64-bit size
        const high = view.getUint32(off + 8);
        const low = view.getUint32(off + 12);
        return high * 2 ** 32 + low;
      }
      return size32;
    };

    while (offset + 12 <= len) {
      const size = readSize(offset);
      const type = String.fromCharCode(
        view.getUint8(offset + 4),
        view.getUint8(offset + 5),
        view.getUint8(offset + 6),
        view.getUint8(offset + 7)
      );

      if (!size || size < 8) break;
      const next = offset + size;

      if (type === 'moov') {
        let inner = offset + 8;
        const end = Math.min(len, next);
        while (inner + 12 <= end) {
          const innerSize = readSize(inner);
          const innerType = String.fromCharCode(
            view.getUint8(inner + 4),
            view.getUint8(inner + 5),
            view.getUint8(inner + 6),
            view.getUint8(inner + 7)
          );
          if (!innerSize || innerSize < 8) break;

          if (innerType === 'mvhd') {
            const version = view.getUint8(inner + 8);
            let timescale = 0;
            let duration = 0;
            if (version === 1 && inner + 36 <= end) {
              timescale = view.getUint32(inner + 20);
              const high = view.getUint32(inner + 24);
              const low = view.getUint32(inner + 28);
              duration = high * 2 ** 32 + low;
            } else if (version === 0 && inner + 20 <= end) {
              timescale = view.getUint32(inner + 12);
              duration = view.getUint32(inner + 16);
            }
            if (timescale > 0 && duration > 0) {
              return duration / timescale;
            }
          }

          const nextInner = inner + innerSize;
          if (nextInner <= inner) break;
          inner = nextInner;
        }
      }

      if (next <= offset) break;
      offset = next;
    }
  } catch (err) {
    console.warn('[Background] probeMp4Duration failed:', err?.message);
  }
  return null;
}

const SYNC_PLAN_DEFAULTS = {
  quick:   { coveragePct: 0.05, minWindows: 3, maxWindows: 5, windowSeconds: 45, legacyMode: 'quick' },
  smart:   { coveragePct: 0.1,  minWindows: 4, maxWindows: 7, windowSeconds: 60, legacyMode: 'fast' },
  long:    { coveragePct: 0.18, minWindows: 6, maxWindows: 10, windowSeconds: 75, legacyMode: 'complete' },
  thorough:{ coveragePct: 0.32, minWindows: 8, maxWindows: 14, windowSeconds: 90, legacyMode: 'complete' },
  complete:{ coveragePct: 1,    minWindows: null, maxWindows: null, windowSeconds: null, legacyMode: 'complete', fullScan: true }
};
const PLAN_MIN_WINDOW_SECONDS = 20;
const PLAN_MAX_WINDOW_SECONDS = 7200;
const PLAN_FULLSCAN_DEFAULT_CHUNK_CAP = 180;

function normalizeSyncPlan(plan, mode) {
  const presetKey = (plan?.preset || mode || 'smart').toString().toLowerCase();
  const preset = SYNC_PLAN_DEFAULTS[presetKey] || {};
  const inferModeGroup = () => {
    if (presetKey.startsWith('alass-')) return 'alass';
    if (presetKey.startsWith('ffss-') || presetKey.startsWith('ffsubsync-')) return 'ffsubsync';
    if (presetKey.startsWith('vosk-')) return 'vosk-ctc';
    if (presetKey.startsWith('whisper-')) return 'whisper-alass';
    return null;
  };

  const fullScan = plan?.fullScan === true || plan?.strategy === 'full' || preset.fullScan === true;
  const coverageTargetPct = Number.isFinite(plan?.coverageTargetPct)
    ? Math.max(0.01, Math.min(1, plan.coverageTargetPct))
    : Number.isFinite(plan?.coveragePct)
      ? Math.max(0.01, Math.min(1, plan.coveragePct))
      : Number.isFinite(preset.coveragePct)
        ? Math.max(0.01, Math.min(1, preset.coveragePct))
        : 0.1;

  const windowSeconds = Number.isFinite(plan?.windowSeconds)
    ? plan.windowSeconds
    : Number.isFinite(preset.windowSeconds) ? preset.windowSeconds : null;
  const requestedWindowSeconds = Number.isFinite(plan?.requestedWindowSeconds)
    ? plan.requestedWindowSeconds
    : windowSeconds;
  const windowCount = Number.isFinite(plan?.windowCount) ? plan.windowCount : null;
  const durationSeconds = Number.isFinite(plan?.durationSeconds) ? plan.durationSeconds : null;
  const minWindows = Number.isFinite(plan?.minWindows) ? plan.minWindows : (Number.isFinite(preset.minWindows) ? preset.minWindows : (fullScan ? null : 3));
  const maxWindows = Number.isFinite(plan?.maxWindows) ? plan.maxWindows : (Number.isFinite(preset.maxWindows) ? preset.maxWindows : null);
  const strategy = plan?.strategy || (preset.fullScan ? 'full' : (preset.strategy || 'spread'));
  const modeGroup = plan?.modeGroup
    || plan?.primaryMode
    || (typeof mode === 'string' && ['alass', 'ffsubsync', 'vosk-ctc', 'whisper-alass'].includes(mode) ? mode : null)
    || inferModeGroup();
  const useFingerprintPrepass = plan?.useFingerprintPrepass !== false;
  const maxChunkSeconds = (() => {
    const raw = Number.isFinite(plan?.maxChunkSeconds)
      ? plan.maxChunkSeconds
      : (Number.isFinite(plan?.maxWindowSeconds) ? plan.maxWindowSeconds : null);
    if (!Number.isFinite(raw)) return null;
    return Math.max(PLAN_MIN_WINDOW_SECONDS, Math.min(raw, PLAN_MAX_WINDOW_SECONDS));
  })();

  return {
    preset: plan?.preset || presetKey,
    legacyMode: plan?.legacyMode || preset.legacyMode || presetKey,
    coverageTargetPct,
    windowSeconds,
    windowCount,
    minWindows,
    maxWindows,
    durationSeconds,
    requestedWindowSeconds,
    overrideApplied: !!plan?.overrideApplied,
    durationAdjusted: !!plan?.durationAdjusted,
    strategy,
    fullScan,
    modeGroup,
    useFingerprintPrepass,
    maxChunkSeconds
  };
}

function adaptPlanToDuration(plan, durationSeconds) {
  const duration = Number.isFinite(durationSeconds) ? Math.max(0, durationSeconds) : plan.durationSeconds;
  const maxChunkSeconds = Number.isFinite(plan?.maxChunkSeconds)
    ? Math.max(PLAN_MIN_WINDOW_SECONDS, Math.min(plan.maxChunkSeconds, PLAN_MAX_WINDOW_SECONDS))
    : null;
  let windowSeconds = plan.windowSeconds;
  if (Number.isFinite(plan.requestedWindowSeconds)) {
    windowSeconds = plan.requestedWindowSeconds;
  }
  if (!Number.isFinite(windowSeconds) && duration) {
    const divisor = Math.max(1, plan.minWindows || 3);
    windowSeconds = Math.max(
      PLAN_MIN_WINDOW_SECONDS,
      Math.min(180, (duration * (plan.coverageTargetPct || 0.1)) / divisor)
    );
  }
  if (duration && Number.isFinite(windowSeconds) && windowSeconds > duration) {
    windowSeconds = duration;
  }
  if (Number.isFinite(windowSeconds) && Number.isFinite(maxChunkSeconds) && windowSeconds > maxChunkSeconds) {
    windowSeconds = maxChunkSeconds;
  }

  const windowCountLocked = Number.isFinite(plan.windowCount);
  let windowCount = plan.fullScan ? null : (windowCountLocked ? plan.windowCount : plan.minWindows || 3);
  if (!plan.fullScan && duration && Number.isFinite(windowSeconds) && !windowCountLocked) {
    const targetCoverage = duration * (plan.coverageTargetPct || 0.1);
    windowCount = Math.ceil(targetCoverage / windowSeconds);
    windowCount = Math.max(plan.minWindows || 1, windowCount);
    if (plan.maxWindows) {
      windowCount = Math.min(plan.maxWindows, windowCount);
    }
  }

  const coverageSeconds = plan.fullScan && duration
    ? duration
    : (windowCount && windowSeconds ? windowCount * windowSeconds : null);

  return {
    ...plan,
    durationSeconds: duration || null,
    windowSeconds: Number.isFinite(windowSeconds)
      ? Math.min(Math.max(windowSeconds, PLAN_MIN_WINDOW_SECONDS), Number.isFinite(maxChunkSeconds) ? maxChunkSeconds : PLAN_MAX_WINDOW_SECONDS)
      : null,
    windowCount: plan.fullScan ? null : windowCount,
    coverageSeconds,
    durationAdjusted: plan.durationAdjusted || (!!duration && plan.durationSeconds !== duration),
    maxChunkSeconds
  };
}

function planWindows(totalDurationSec, plan) {
  const effective = adaptPlanToDuration(plan, totalDurationSec);
  const inferred = totalDurationSec
    || effective.coverageSeconds
    || (Number.isFinite(effective.windowSeconds) && Number.isFinite(effective.windowCount)
      ? Math.max(effective.windowSeconds * effective.windowCount * 1.1, effective.windowSeconds * 3)
      : 0);
  const dur = Math.max(60, inferred || 0);
  const maxChunkSeconds = Number.isFinite(effective.maxChunkSeconds) ? effective.maxChunkSeconds : null;

  if (effective.fullScan) {
    const chunkCap = maxChunkSeconds || PLAN_FULLSCAN_DEFAULT_CHUNK_CAP;
    const chunk = Math.min(chunkCap, Math.max(60, dur / Math.max(1, Math.ceil(dur / 600))));
    const count = Math.max(1, Math.ceil(dur / chunk));
    const denom = Math.max(1, count - 1);
    const windows = Array.from({ length: count }).map((_, i) => {
      const pos = count === 1 ? 0 : i / denom;
      const start = Math.max(0, Math.min(Math.max(0, dur - chunk), (dur * pos) - (chunk / 2)));
      return { startSec: start, durSec: chunk };
    });
    return { windows, plan: { ...effective, windowCount: count, windowSeconds: chunk, coverageSeconds: count * chunk } };
  }

  let windowCount = Math.max(1, effective.windowCount || effective.minWindows || 3);
  let winDur = Math.max(PLAN_MIN_WINDOW_SECONDS, Math.min(PLAN_MAX_WINDOW_SECONDS, effective.windowSeconds || 60));
  if (Number.isFinite(maxChunkSeconds)) {
    winDur = Math.min(winDur, maxChunkSeconds);
  }
  const strategy = effective.strategy || 'spread';
  const denom = Math.max(1, windowCount - 1);
  const mapPosition = (idx) => {
    if (windowCount === 1) return 0;
    const t = idx / denom;
    if (strategy === 'dense-spread') {
      // Ease-in-out curve to bias anchors toward lead and tail while still covering the whole runtime
      return 0.5 - (Math.cos(Math.PI * t) / 2);
    }
    return t;
  };
  const windows = Array.from({ length: windowCount }).map((_, i) => {
    const pos = mapPosition(i);
    const start = Math.max(0, Math.min(Math.max(0, dur - winDur), (dur * pos) - (winDur / 2)));
    return { startSec: start, durSec: winDur };
  });

  return { windows, plan: { ...effective, windowCount, windowSeconds: winDur, coverageSeconds: windowCount * winDur } };
}

function describePlanForLog(plan) {
  if (!plan) return 'Plan: (none)';
  const parts = [`preset=${plan.preset || 'smart'}`];
  if (Number.isFinite(plan.windowCount)) parts.push(`windows=${plan.windowCount}`);
  if (Number.isFinite(plan.windowSeconds)) parts.push(`windowSeconds=${Math.round(plan.windowSeconds)}`);
  if (Number.isFinite(plan.maxChunkSeconds)) parts.push(`maxChunkSec=${Math.round(plan.maxChunkSeconds)}`);
  if (Number.isFinite(plan.coverageTargetPct)) parts.push(`target=${Math.round((plan.coverageTargetPct || 0) * 100)}%`);
  if (Number.isFinite(plan.coverageSeconds)) parts.push(`coverageSec=${Math.round(plan.coverageSeconds)}`);
  if (Number.isFinite(plan.durationSeconds)) parts.push(`duration=${formatSecondsShort(plan.durationSeconds)}`);
  if (plan.useFingerprintPrepass === false) parts.push('fingerprint=off');
  else if (plan.useFingerprintPrepass === true) parts.push('fingerprint=on');
  if (plan.language) parts.push(`lang=${plan.language}`);
  return `Plan: ${parts.join(', ')}`;
}

function formatSecondsShort(sec) {
  if (!Number.isFinite(sec)) return 'n/a';
  if (sec >= 3600) return `${(sec / 3600).toFixed(1).replace(/\.0$/, '')}h`;
  if (sec >= 60) return `${Math.round(sec / 60)}m`;
  return `${Math.round(sec)}s`;
}

function summarizeTracks(tracks) {
  let minTrackSize = Number.MAX_SAFE_INTEGER;
  let lastCueSec = null;
  const timeRegex = /(\d{1,2}):(\d{2}):(\d{2}),(\d{3})\s+-->\s+(\d{1,2}):(\d{2}):(\d{2}),(\d{3})/g;
  for (const t of tracks || []) {
    const byteLen = typeof t?.byteLength === 'number'
      ? t.byteLength
      : t?.contentBase64
        ? Math.floor((t.contentBase64.length * 3) / 4)
        : typeof t?.content === 'string'
          ? t.content.length
          : 0;
    if (byteLen) {
      minTrackSize = Math.min(minTrackSize, byteLen);
    }
    if (typeof t?.content === 'string') {
      let m;
      while ((m = timeRegex.exec(t.content)) !== null) {
        const h = parseInt(m[5], 10);
        const mi = parseInt(m[6], 10);
        const s = parseInt(m[7], 10);
        const ms = parseInt(m[8], 10);
        const endSec = h * 3600 + mi * 60 + s + ms / 1000;
        if (!lastCueSec || endSec > lastCueSec) {
          lastCueSec = endSec;
        }
      }
    }
  }
  if (minTrackSize === Number.MAX_SAFE_INTEGER) minTrackSize = 0;
  return { minTrackSize, lastCueSec };
}

function analyzeCueTimelines(tracks) {
  let flatCueStarts = false;
  let nonMonotonicCues = false;
  const timeRegex = /(\d{1,2}):(\d{2}):(\d{2}),(\d{3})\s+-->\s+(\d{1,2}):(\d{2}):(\d{2}),(\d{3})/g;

  for (const t of tracks || []) {
    if (typeof t?.content !== 'string') continue;
    const starts = [];
    let m;
    while ((m = timeRegex.exec(t.content)) !== null) {
      const h = parseInt(m[1], 10);
      const mi = parseInt(m[2], 10);
      const s = parseInt(m[3], 10);
      const ms = parseInt(m[4], 10);
      const startSec = h * 3600 + mi * 60 + s + ms / 1000;
      starts.push(startSec);
      if (starts.length > 1 && startSec + 1e-3 < starts[starts.length - 2]) {
        nonMonotonicCues = true;
      }
    }
    if (starts.length >= 6) {
      const uniqueStarts = new Set(starts.map(v => v.toFixed(3)));
      const uniqueRatio = uniqueStarts.size / starts.length;
      if (uniqueRatio <= 0.2) {
        flatCueStarts = true;
      }
    }
    if (flatCueStarts && nonMonotonicCues) break;
  }

  return { flatCueStarts, nonMonotonicCues };
}

function isTrackQualityAcceptable(tracks, summary, timelines, durationSec) {
  if (!tracks?.length) return false;
  const minTrackSize = summary?.minTrackSize || 0;
  const lastCueSec = summary?.lastCueSec || 0;
  const hasMonotonic = !(timelines?.nonMonotonicCues || false);
  const hasVariedStarts = !(timelines?.flatCueStarts || false);
  const sizeOK = minTrackSize >= 20 * 1024; // at least 20KB per track to treat as “complete”
  const coverageOK = durationSec ? lastCueSec >= durationSec * 0.8 : true; // allow unknown duration
  return sizeOK && hasMonotonic && hasVariedStarts && coverageOK;
}

function concatBuffers(head, tail) {
  const h = head instanceof ArrayBuffer ? new Uint8Array(head) : head;
  const t = tail instanceof ArrayBuffer ? new Uint8Array(tail) : tail;
  const combined = new Uint8Array((h?.byteLength || 0) + (t?.byteLength || 0));
  if (h) combined.set(new Uint8Array(h), 0);
  if (t) combined.set(new Uint8Array(t), h?.byteLength || 0);
  return combined;
}

function concatBuffersList(buffers) {
  const total = buffers.reduce((sum, b) => sum + (b?.byteLength || 0), 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const b of buffers) {
    if (!b) continue;
    const u = b instanceof Uint8Array ? b : new Uint8Array(b);
    out.set(u, offset);
    offset += u.byteLength;
  }
  return out;
}

function mergeRanges(ranges, maxTotalBytes) {
  if (!ranges?.length) return [];
  const sorted = ranges
    .map(r => ({ start: Math.max(0, r.start || 0), end: Math.max(r.end || 0, r.start || 0) }))
    .sort((a, b) => a.start - b.start);
  const merged = [];
  for (const r of sorted) {
    if (!merged.length) {
      merged.push({ ...r });
      continue;
    }
    const last = merged[merged.length - 1];
    if (r.start <= last.end + 1) {
      last.end = Math.max(last.end, r.end);
    } else {
      merged.push({ ...r });
    }
  }
  if (maxTotalBytes && maxTotalBytes > 0) {
    let total = 0;
    const capped = [];
    for (const r of merged) {
      const len = Math.max(0, r.end - r.start + 1);
      if (total + len > maxTotalBytes) {
        const remain = maxTotalBytes - total;
        if (remain > 0) {
          capped.push({ start: r.start, end: r.start + remain - 1 });
          total += remain;
        }
        break;
      }
      capped.push(r);
      total += len;
    }
    return capped;
  }
  return merged;
}

function isLikelyMkv(streamUrl, contentType, buffer) {
  const lowerUrl = String(streamUrl || '').toLowerCase();
  const lowerCt = String(contentType || '').toLowerCase();
  if (lowerUrl.endsWith('.mkv') || lowerUrl.includes('.mkv?')) return true;
  if (lowerCt.includes('matroska') || lowerCt.includes('x-matroska') || lowerCt.includes('webm')) return true;
  const u8 = buffer instanceof Uint8Array ? buffer : buffer instanceof ArrayBuffer ? new Uint8Array(buffer) : null;
  if (u8 && u8.byteLength >= 4) {
    // EBML magic number
    if (u8[0] === 0x1A && u8[1] === 0x45 && u8[2] === 0xDF && u8[3] === 0xA3) return true;
  }
  return false;
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

async function fetchRangesInParallel(rangeList, streamUrl, onProgressPerItem, options = {}) {
  const concurrency = Math.max(1, Math.min(options.concurrency || 3, 6));
  const results = new Array(rangeList.length);
  let idx = 0;

  async function worker() {
    while (idx < rangeList.length) {
      const current = idx++;
      const r = rangeList[current];
      results[current] = await fetchRangeSlice(streamUrl, r.start, r.end, (p) => onProgressPerItem?.(current, p));
    }
  }

  const workers = [];
  for (let i = 0; i < concurrency; i++) workers.push(worker());
  await Promise.all(workers);
  return results;
}

function uint8ToBase64(u8) {
  if (!u8?.length) return '';
  let binary = '';
  const chunk = 0x8000;
  for (let i = 0; i < u8.length; i += chunk) {
    binary += String.fromCharCode.apply(null, u8.subarray(i, i + chunk));
  }
  return btoa(binary);
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
  if (length > 8) return null;
  let value = first & (mask - 1);
  for (let i = 1; i < length; i++) {
    value = (value << 8) | u8[offset + i];
  }
  return { length, value };
}

function readEbmlElement(u8, offset, limit) {
  if (offset >= limit) return null;
  const idInfo = readVint(u8, offset);
  if (!idInfo) return null;
  // For element IDs, keep the raw bytes (marker bits included) to match EBML constants.
  let idRaw = 0;
  for (let i = 0; i < idInfo.length; i++) {
    idRaw = (idRaw << 8) | u8[offset + i];
  }
  const sizeInfo = readVint(u8, offset + idInfo.length);
  if (!sizeInfo) return null;
  const dataStart = offset + idInfo.length + sizeInfo.length;
  let size = sizeInfo.value;
  // Unknown-size EBML elements set all size bits; treat as consuming the remaining scan window
  if (size === (Math.pow(2, 7 * sizeInfo.length) - 1)) {
    size = Math.max(0, limit - dataStart);
  }
  let dataEnd = dataStart + size;
  if (dataEnd > limit) {
    // When scanning partial buffers (e.g., HTTP byte ranges), large/unknown sizes can exceed our window.
    // Cap to the available bytes so we can still walk nested header elements like Tracks.
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

  function parseUint(u8, start, end) {
    let v = 0;
    for (let i = start; i < end; i++) v = (v << 8) | u8[i];
    return v >>> 0;
  }

  function parseString(u8, start, end) {
    return decodeUtf8Safe(u8.subarray(start, end)).trim();
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
  // Find segment
  walk(0, limit, {
    [ID.SEGMENT]: (el) => {
      segmentStart = el.dataStart;
      info.segmentOffset = el.dataStart;
      const segEnd = Math.min(el.dataEnd, limit);
      // Parse only header-ish elements
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
          [ID.SEEK_ID]: (idEl) => {
            seekId = parseUint(u8, idEl.dataStart, idEl.dataEnd);
          },
          [ID.SEEK_POSITION]: (posEl) => {
            seekPos = parseUint(u8, posEl.dataStart, posEl.dataEnd);
          }
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
        // Prefer modern IETF tag when present
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

async function tryCueGuidedMkvExtraction(ctx) {
  const {
    streamUrl,
    sampleBuffer,
    sampleBytes,
    messageId,
    tabId,
    hostLabel
  } = ctx;

  const headerInfo = ctx.headerInfo || parseMkvHeaderInfo(sampleBuffer, { maxScanBytes: Math.min(sampleBytes || 0, 12 * 1024 * 1024) || 12 * 1024 * 1024 });
  const subtitleTracks = headerInfo.tracks.filter(t => t.type === 0x11 || t.type === 17 || t.codecId?.toLowerCase().includes('s_text'));
  let attachmentTracks = [];
  if (headerInfo.attachments.length) {
    attachmentTracks = headerInfo.attachments.map((att, idx) => {
      const lowerName = (att.name || '').toLowerCase();
      const lowerMime = (att.mime || '').toLowerCase();
      const isText = lowerMime.startsWith('text/') || lowerMime.includes('subtitle') || lowerName.endsWith('.srt') || lowerName.endsWith('.ass') || lowerName.endsWith('.ssa') || lowerName.endsWith('.vtt');
      const codec = lowerName.endsWith('.ass') ? 'ass' : lowerName.endsWith('.ssa') ? 'ssa' : lowerName.endsWith('.vtt') ? 'vtt' : lowerName.endsWith('.srt') ? 'srt' : (lowerMime.includes('ass') ? 'ass' : isText ? 'srt' : 'bin');
      let content = null;
      let contentBase64 = null;
      if (isText) {
        content = decodeUtf8Safe(att.data);
      } else {
        contentBase64 = uint8ToBase64(att.data);
      }
      return {
        id: `attach_${idx}`,
        label: att.name || `Attachment ${idx + 1}`,
        language: 'und',
        codec,
        content,
        contentBase64
      };
    }).filter(Boolean);
    if (attachmentTracks.length) {
      sendDebugLog(tabId, messageId, `Found ${attachmentTracks.length} attachment(s) in MKV header`, 'info');
    }
  }

  const cuesAlready = headerInfo.cues?.length ? headerInfo.cues : null;
  let cueList = cuesAlready;
  const cueSeek = headerInfo.seekHead.find(s => s.idHex === '1C53BB6B');
  if (!cueList && cueSeek && headerInfo.segmentOffset !== null) {
    const cueStart = headerInfo.segmentOffset + cueSeek.position;
    const cueWindow = 8 * 1024 * 1024;
    try {
      sendDebugLog(tabId, messageId, 'Fetching Cues via SeekHead...', 'info');
      const cueBuf = await fetchRangeSlice(streamUrl, cueStart, cueStart + cueWindow - 1, (p) => sendExtractProgress(tabId, messageId, Math.min(87, 70 + p * 0.05), `Fetching Cues from ${hostLabel}...`));
      const parsed = parseMkvHeaderInfo(cueBuf.buffer || cueBuf, { maxScanBytes: cueWindow });
      cueList = parsed.cues?.length ? parsed.cues : null;
    } catch (err) {
      console.warn('[Background] Cue fetch via SeekHead failed:', err?.message || err);
    }
  }

  if (!subtitleTracks.length || !cueList?.length) {
    if (attachmentTracks.length) {
      return attachmentTracks;
    }
    return null;
  }

  const subtitleTrackNumbers = new Set(subtitleTracks.map(t => t.number).filter(Boolean));
  const cuePositions = [];
  for (const cue of cueList) {
    for (const pos of cue.positions || []) {
      if (subtitleTrackNumbers.has(pos.track) && typeof pos.clusterPos === 'number') {
        cuePositions.push({ clusterPos: pos.clusterPos, relPos: pos.relPos || 0 });
      }
    }
  }

  if (!cuePositions.length) {
    if (attachmentTracks.length) {
      return attachmentTracks;
    }
    return null;
  }

  const preBytes = 128 * 1024;
  const windowBytes = 512 * 1024; // smaller nibble per cue; merged if dense
  const ranges = cuePositions.map(cp => {
    const clusterOffset = (headerInfo.segmentOffset || 0) + cp.clusterPos + (cp.relPos || 0);
    const start = Math.max(0, clusterOffset - preBytes);
    return { start, end: start + windowBytes - 1 };
  });
  const merged = mergeRanges(ranges, 160 * 1024 * 1024); // cap to ~160MB of targeted pulls

  let fetchedBuffers = [];
  try {
    const rangeCount = merged.length;
    const results = await fetchRangesInParallel(
      merged,
      streamUrl,
      (idx, p) => sendExtractProgress(tabId, messageId, Math.min(90, 75 + Math.round(p * 0.05)), `Cue window ${idx + 1}/${rangeCount}...`),
      { concurrency: 3 }
    );
    fetchedBuffers = results.map(r => r.buffer || r);
  } catch (err) {
    console.warn('[Background] Cue-guided range fetch failed:', err?.message || err);
    if (attachmentTracks.length) return attachmentTracks;
    return null;
  }

  // Stitch header+cue windows for demux
  const stitched = concatBuffersList([sampleBuffer, ...fetchedBuffers]);
  sendDebugLog(tabId, messageId, `Cue-guided demux with ${merged.length} window(s) (~${Math.round(stitched.byteLength / (1024 * 1024))} MB)`, 'info');
  try {
    const tracks = await demuxSubtitlesOffscreen(stitched, messageId, tabId);
    if (tracks?.length) {
      const combined = attachmentTracks.length ? [...tracks, ...attachmentTracks] : tracks;
      return combined;
    }
  } catch (err) {
    console.warn('[Background] Cue-guided demux failed:', err?.message || err);
  }

  if (attachmentTracks.length) {
    return attachmentTracks;
  }
  return null;
}

function readEbmlVint(bytes, offset, stripLengthMarker = false) {
  const first = bytes[offset];
  if (first === undefined) return null;
  let lengthMask = 0x80;
  let length = 1;
  while (length <= 8 && !(first & lengthMask)) {
    lengthMask >>= 1;
    length += 1;
  }
  if (length > 8 || offset + length > bytes.length) return null;
  let value = stripLengthMarker ? (first & (lengthMask - 1)) : first;
  for (let i = 1; i < length; i++) {
    value = (value << 8) + bytes[offset + i];
  }
  return { length, value };
}

function probeMkvDuration(buffer) {
  try {
    const bytes = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
    if (!bytes?.length) return null;
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const limit = Math.min(bytes.byteLength, 8 * 1024 * 1024); // parse first 8MB to catch Info block

    const readElement = (offset) => {
      const id = readEbmlVint(bytes, offset, false);
      if (!id) return null;
      const size = readEbmlVint(bytes, offset + id.length, true);
      if (!size) return null;
      return { id: id.value, size: size.value, header: id.length + size.length };
    };

    // Locate Segment element (0x18538067)
    let offset = 0;
    let segmentStart = null;
    let segmentEnd = null;
    while (offset < limit) {
      const el = readElement(offset);
      if (!el) break;
      const dataStart = offset + el.header;
      const dataEnd = dataStart + el.size;
      if (el.id === 0x18538067) {
        segmentStart = dataStart;
        segmentEnd = el.size ? Math.min(limit, dataEnd) : limit;
        break;
      }
      offset = dataEnd;
    }
    if (segmentStart == null) return null;

    // Locate Info element (0x1549A966) within Segment
    offset = segmentStart;
    let timecodeScale = 1000000; // default TimecodeScale (1ms -> 1e6 ns)
    let duration = null;
    while (offset < (segmentEnd || limit)) {
      const el = readElement(offset);
      if (!el) break;
      const dataStart = offset + el.header;
      const dataEnd = dataStart + el.size;
      if (dataEnd > limit) break;

      if (el.id === 0x1549A966) {
        let inner = dataStart;
        while (inner < dataEnd) {
          const infoEl = readElement(inner);
          if (!infoEl) break;
          const infoStart = inner + infoEl.header;
          const infoEnd = infoStart + infoEl.size;
          if (infoEnd > limit) break;

          if (infoEl.id === 0x2AD7B1) { // TimecodeScale
            let scale = 0;
            for (let i = 0; i < Math.min(infoEl.size, 8); i++) {
              scale = (scale << 8) + bytes[infoStart + i];
            }
            if (scale > 0) timecodeScale = scale;
          } else if (infoEl.id === 0x4489) { // Duration (float)
            if (infoEl.size === 4) {
              duration = view.getFloat32(infoStart, false);
            } else if (infoEl.size >= 8) {
              duration = view.getFloat64(infoStart, false);
            }
          }
          inner = infoEnd;
        }
        break; // Stop scanning after Info block
      }
      offset = dataEnd;
    }

    if (duration && timecodeScale) {
      return duration * (timecodeScale / 1e9); // convert to seconds
    }
  } catch (err) {
    console.warn('[Background] probeMkvDuration failed:', err?.message);
  }
  return null;
}

function probeContainerDuration(buffer) {
  return probeMp4Duration(buffer) || probeMkvDuration(buffer);
}

async function probeDurationHead(url, baseHeaders = null) {
  try {
    const headers = mergeHeaders(baseHeaders, { Range: 'bytes=0-2097151' });
    const res = await safeFetch(url, { headers });
    if (!res.ok && res.status !== 206) return null;
    const buf = await res.arrayBuffer();
    return probeContainerDuration(buf);
  } catch (err) {
    console.warn('[Background] probeDurationHead failed:', err?.message || err);
    return null;
  }
}

function parseIso8601Duration(str) {
  const m = /^PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+(?:\.\d+)?)S)?$/i.exec(str || '');
  if (!m) return null;
  const h = parseInt(m[1] || '0', 10);
  const mi = parseInt(m[2] || '0', 10);
  const s = parseFloat(m[3] || '0');
  return (h * 3600) + (mi * 60) + s;
}

async function probeDashDuration(mpdUrl) {
  try {
    const txt = await (await safeFetch(mpdUrl)).text();
    const durMatch = txt.match(/mediaPresentationDuration=\"([^\"]+)\"/i);
    if (durMatch && durMatch[1]) {
      const seconds = parseIso8601Duration(durMatch[1]);
      if (Number.isFinite(seconds) && seconds > 0) return seconds;
    }
  } catch (err) {
    console.warn('[Background] probeDashDuration failed:', err?.message || err);
  }
  return null;
}

async function scanClustersForSubtitles(ctx) {
  const {
    streamUrl,
    sampleBuffer,
    sampleBytes,
    messageId,
    tabId,
    hostLabel,
    totalBytes,
    contentType
  } = ctx;

  const looksMkv = isLikelyMkv(streamUrl, contentType, sampleBuffer);
  if (!looksMkv) return null;

  const u8 = sampleBuffer instanceof Uint8Array ? sampleBuffer : new Uint8Array(sampleBuffer || 0);
  const probeBytes = 32 * 1024 * 1024; // 32MB probe slices
  const maxScanBytes = Math.min(sampleBytes || u8.length || 0, 64 * 1024 * 1024); // limit local sample scan to 64MB
  const clusterId = 0x1F43B675; // Cluster
  const trackNumberHint = new Set();

  // Quick track read from header
  try {
    const header = parseMkvHeaderInfo(u8, { maxScanBytes: maxScanBytes });
    header.tracks.forEach(t => {
      if (t.type === 0x11 || t.type === 17 || (t.codecId || '').toLowerCase().includes('s_text')) {
        if (t.number) trackNumberHint.add(t.number);
      }
    });
  } catch (_) { /* ignore */ }

  function findClusters(buf) {
    const hits = [];
    for (let i = 0; i < buf.length - 4; i++) {
      if (buf[i] === 0x1F && buf[i + 1] === 0x43 && buf[i + 2] === 0xB6 && buf[i + 3] === 0x75) {
        hits.push(i);
      }
    }
    return hits;
  }

  // If sample already has clusters, reuse them to avoid extra calls.
  const localClusters = findClusters(u8);
  const clusterWindows = [];
  const halfWin = 1024 * 1024; // 2MB total window around each cluster

  if (localClusters.length) {
    for (const c of localClusters) {
      const start = Math.max(0, c - halfWin);
      clusterWindows.push({ start, end: start + halfWin * 2 });
    }
  } else {
    // Step through the remote file with larger probes (20-50MB) to find clusters
    const stepCount = 10;
    const span = totalBytes && totalBytes > probeBytes ? totalBytes : probeBytes * stepCount;
    for (let i = 0; i < stepCount; i++) {
      const pos = Math.min(span - probeBytes, Math.floor((span / stepCount) * i));
      const start = Math.max(0, pos);
      const end = start + probeBytes - 1;
      try {
        const slice = await fetchRangeSlice(streamUrl, start, end, (p) => sendExtractProgress(tabId, messageId, Math.min(86, 70 + p * 0.03), `Scanning clusters ${i + 1}/${stepCount}...`));
        const sliceU8 = slice.buffer instanceof Uint8Array ? slice.buffer : new Uint8Array(slice.buffer || slice);
        const hits = findClusters(sliceU8);
        for (const h of hits) {
          const globalStart = Math.max(0, start + h - halfWin);
          clusterWindows.push({ start: globalStart, end: globalStart + halfWin * 2 });
        }
      } catch (err) {
        console.warn('[Background] Cluster scan range failed:', err?.message || err);
      }
    }
  }

  if (!clusterWindows.length) return null;
  const merged = mergeRanges(clusterWindows, Math.min(5 * 1024 * 1024 * 1024, Math.max(160 * 1024 * 1024, (totalBytes && totalBytes / 2) || 512 * 1024 * 1024)));

  try {
    const rangeCount = merged.length;
    const results = await fetchRangesInParallel(
      merged,
      streamUrl,
      (idx, p) => sendExtractProgress(tabId, messageId, Math.min(90, 75 + Math.round(p * 0.05)), `Cluster window ${idx + 1}/${rangeCount}...`),
      { concurrency: 3 }
    );
    const stitched = concatBuffersList([sampleBuffer, ...results.map(r => r.buffer || r)]);
    const tracks = await demuxSubtitlesOffscreen(stitched, messageId, tabId);
    if (tracks?.length) return tracks;
  } catch (err) {
    console.warn('[Background] Cluster scan demux failed:', err?.message || err);
  }
  return null;
}

async function streamSubtitlesWithCoverage(ctx) {
  const {
    streamUrl,
    messageId,
    tabId,
    hostLabel,
    durationSec,
    totalBytes,
    contentType
  } = ctx;

  const looksMkv = isLikelyMkv(streamUrl, contentType);
  if (!looksMkv) return null;

  const chunkSize = 8 * 1024 * 1024;
  const maxBytes = Math.min(totalBytes || 256 * 1024 * 1024, 256 * 1024 * 1024);
  let offset = 0;
  let buffers = [];
  let bestTracks = null;
  let bestSummary = { minTrackSize: 0, lastCueSec: 0 };

  const targetDuration = durationSec || (ctx?.headerInfo?.chapters?.length
    ? Math.max(...ctx.headerInfo.chapters.map(c => (c.end || c.start || 0) / 1000))
    : null);

  while (offset < maxBytes) {
    const end = Math.min(offset + chunkSize - 1, (totalBytes || offset + chunkSize) - 1);
    const slice = await fetchRangeSlice(streamUrl, offset, end, (p) => sendExtractProgress(tabId, messageId, Math.min(88, 70 + p * 0.05), `Streaming demux @${Math.round(offset / (1024 * 1024))}MB...`));
    buffers.push(slice.buffer || slice);
    const stitched = concatBuffersList(buffers);
    try {
      const tracks = await demuxSubtitlesOffscreen(stitched, messageId, tabId);
      const summary = summarizeTracks(tracks);
      bestTracks = tracks;
      bestSummary = summary;
      const durationTarget = targetDuration ? targetDuration * 0.9 : null;
      const sizeOK = summary.minTrackSize >= 20 * 1024;
      const timeOK = durationTarget ? (summary.lastCueSec || 0) >= durationTarget : false;
      if (sizeOK && (timeOK || offset + chunkSize >= maxBytes)) {
        return tracks;
      }
    } catch (err) {
      console.warn('[Background] Streaming coverage demux failed at chunk:', err?.message || err);
    }
    offset += chunkSize;
  }
  return bestTracks;
}

async function tryTargetedMkvStrategies(ctx) {
  const {
    streamUrl,
    sampleBuffer,
    sampleBytes,
    messageId,
    tabId,
    hostLabel,
    durationSec,
    totalBytes,
    minTrackSize,
    lastCueSec,
    contentType
  } = ctx;

  const looksMkv = isLikelyMkv(streamUrl, contentType, sampleBuffer);
  if (!looksMkv) {
    return null; // skip targeted MKV tricks for non-MKV streams
  }

  const headerInfo = parseMkvHeaderInfo(sampleBuffer, { maxScanBytes: Math.min(sampleBytes || 0, 12 * 1024 * 1024) || 12 * 1024 * 1024 });
  ctx.headerInfo = headerInfo;

  let currentBest = { minTrackSize, lastCueSec, tracks: null };
  const minTail = 32 * 1024 * 1024; // 32MB tail by default
  const tailLimit = Math.max(minTail, Math.min(128 * 1024 * 1024, Math.round((sampleBytes || minTail) * 0.9)));

  try {
    const cueRes = await tryCueGuidedMkvExtraction(ctx);
    if (cueRes?.length) {
      return cueRes;
    }
  } catch (err) {
    console.warn('[Background] Cue-guided MKV extraction failed:', err?.message || err);
  }

  try {
    const clusterRes = await scanClustersForSubtitles(ctx);
    if (clusterRes?.length) {
      return clusterRes;
    }
  } catch (err) {
    console.warn('[Background] Cluster-scan MKV extraction failed:', err?.message || err);
  }

  try {
    const streamRes = await streamSubtitlesWithCoverage(ctx);
    if (streamRes?.length) {
      return streamRes;
    }
  } catch (err) {
    console.warn('[Background] Streaming coverage extraction failed:', err?.message || err);
  }

  // Dual head+tail probing: grab a generous tail slice and retry demux on combined buffer
  try {
    sendDebugLog(tabId, messageId, `Dual head+tail probing (~${Math.round(tailLimit / (1024 * 1024))} MB tail)...`, 'warn');
    const tail = await fetchTailSample(streamUrl, tailLimit, (p) => sendExtractProgress(tabId, messageId, Math.min(88, 70 + p * 0.1), `Downloading tail slice from ${hostLabel}...`), baseHeaders);
    const combined = concatBuffers(sampleBuffer, tail.buffer);
    const combinedTracks = await demuxSubtitlesOffscreen(combined, messageId, tabId);
    const summary = summarizeTracks(combinedTracks);
    if ((summary.minTrackSize || 0) > (currentBest.minTrackSize || 0) || (summary.lastCueSec || 0) > (currentBest.lastCueSec || 0)) {
      return combinedTracks;
    }
    currentBest = summary;
  } catch (err) {
    console.warn('[Background] Head+tail probing failed:', err?.message || err);
  }

  // If we know total size, try a mid-file probe near 75% to pick up late clusters without full download.
  if (totalBytes && totalBytes > 0) {
    const windowSize = Math.min(48 * 1024 * 1024, Math.max(16 * 1024 * 1024, Math.round(totalBytes * 0.05)));
    const midStart = Math.max(0, Math.round(totalBytes * 0.7));
    const midEnd = Math.min(totalBytes - 1, midStart + windowSize);
    try {
      sendDebugLog(tabId, messageId, 'Fetching mid-file probe for late subtitle clusters...', 'warn');
      const midSlice = await fetchRangeSlice(streamUrl, midStart, midEnd, (p) => sendExtractProgress(tabId, messageId, Math.min(90, 80 + p * 0.05), `Fetching mid-file probe (${hostLabel})...`));
      const stitched = concatBuffers(sampleBuffer, midSlice.buffer);
      const midTracks = await demuxSubtitlesOffscreen(stitched, messageId, tabId);
      const summary = summarizeTracks(midTracks);
      if ((summary.minTrackSize || 0) > (currentBest.minTrackSize || 0) || (summary.lastCueSec || 0) > (currentBest.lastCueSec || 0)) {
        return midTracks;
      }
      currentBest = summary;
    } catch (err) {
      console.warn('[Background] Mid-file probe failed:', err?.message || err);
    }
  }

  //   // As a last light attempt, rerun guard with a higher cap.
  {
    try {
      const expanded = await fetchByteRangeSample(streamUrl, (p) => sendExtractProgress(tabId, messageId, Math.min(93, 85 + p * 0.05), `Retrying with larger sample (${hostLabel})...`), { minBytes: 192 * 1024 * 1024 });
      const expandedTracks = await demuxSubtitlesOffscreen(expanded.buffer, messageId, tabId);
      const summary = summarizeTracks(expandedTracks);
      if ((summary.minTrackSize || 0) > (currentBest.minTrackSize || 0) || (summary.lastCueSec || 0) > (currentBest.lastCueSec || 0)) {
        return expandedTracks;
      }
    } catch (err) {
      console.warn('[Background] Expanded sample retry in targeted stage failed:', err?.message || err);
    }
  }

  return null;
}

async function fetchFullStreamBuffer(url, onProgress, baseHeaders = null) {
  const fetchOpts = baseHeaders ? { headers: baseHeaders } : undefined;
  const res = await safeFetch(url, fetchOpts);
  if (!res.ok) {
    throw new Error(`Full fetch failed (HTTP ${res.status})`);
  }
  const contentType = res.headers?.get?.('content-type') || '';
  const totalBytes = parseInt(res.headers.get('content-length') || '0', 10) || null;
  const reader = res.body && typeof res.body.getReader === 'function' ? res.body.getReader() : null;
  if (!reader) {
    const buf = await res.arrayBuffer();
    onProgress?.(100);
    return { buffer: buf, totalBytes: totalBytes || (buf?.byteLength || null), contentType };
  }

  let received = 0;
  const chunks = [];
  let allocated = null;

  if (totalBytes && totalBytes > 0) {
    allocated = new Uint8Array(totalBytes);
  }

  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    if (value && value.length) {
      if (allocated) {
        allocated.set(value, received);
      } else {
        chunks.push(value);
      }
      received += value.length;
      const pct = totalBytes ? Math.round((received / totalBytes) * 95) : Math.min(95, Math.round(received / (1024 * 1024)));
      onProgress?.(Math.min(95, pct));
    }
  }

  const buffer = allocated
    ? (totalBytes && received < totalBytes ? allocated.subarray(0, received) : allocated)
    : concatBuffersList(chunks);

  onProgress?.(100);
  return { buffer, totalBytes: totalBytes || received, contentType };
}

async function fetchFullHlsStream(m3u8Url, onProgress, baseHeaders = null) {
  const { segments, totalDurationSec, map } = await resolveHlsPlaylist(m3u8Url, baseHeaders);
  const buffers = [];
  let totalBytes = 0;
  const totalSegments = segments.length || 1;
  if (map?.uri) {
    try {
      const headers = map.byterange
        ? mergeHeaders(baseHeaders, { Range: `bytes=${map.byterange.offset || 0}-${(map.byterange.offset || 0) + map.byterange.length - 1}` })
        : baseHeaders;
      const res = await safeFetch(map.uri, headers ? { headers } : undefined);
      if (!res.ok) throw new Error(`Init segment fetch failed (${res.status})`);
      const initBuf = new Uint8Array(await res.arrayBuffer());
      buffers.push(initBuf);
      totalBytes += initBuf.byteLength || 0;
    } catch (err) {
      console.warn('[Background][HLS] Failed to fetch EXT-X-MAP init segment for full stream:', err?.message || err);
    }
  }

  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    const res = await safeFetch(seg.uri, baseHeaders ? { headers: baseHeaders } : undefined);
    if (!res.ok) throw new Error(`Segment fetch failed (HTTP ${res.status})`);
    const buf = new Uint8Array(await res.arrayBuffer());
    buffers.push(buf);
    totalBytes += buf.byteLength || 0;
    const pct = Math.min(95, Math.round(((i + 1) / totalSegments) * 95));
    onProgress?.(pct);
  }

  const stitched = concatBuffersList(buffers);
  onProgress?.(100);
  return { buffer: stitched, durationSec: totalDurationSec, totalBytes, contentType: 'application/vnd.apple.mpegurl' };
}

async function fetchByteRangeSample(url, onProgress, options = {}, baseHeaders = null) {
  // Single mode: start at 64MB, allow growth via options up to 768MB
  const baseLimit = Math.max(64 * 1024 * 1024, Math.max(0, options?.minBytes || 0));
  const cap = Math.min(options?.maxBytesCap || 512 * 1024 * 1024, 768 * 1024 * 1024);
  const limit = Math.min(cap, baseLimit);

  const headers = limit > 0 ? { Range: `bytes=0-${limit - 1}` } : undefined;

  let res;
  let usedRange = !!headers;
  let isPartial = false;
  try {
    const mergedHeaders = headers ? mergeHeaders(baseHeaders, headers) : baseHeaders;
    res = await fetchWithBackoff(url, mergedHeaders ? { headers: mergedHeaders } : undefined, 2, 1200);
  } catch (err) {
    // Some hosts (e.g. without CORS preflight for Range) reject the ranged request entirely.
    if (headers) {
      console.warn('[Background] Range fetch failed, retrying full fetch without Range header:', err?.message || err);
      usedRange = false;
      res = await fetchWithBackoff(url, baseHeaders ? { headers: baseHeaders } : undefined, 2, 1200);
    } else {
      throw new Error(`Stream fetch failed: ${err?.message || err}`);
    }
  }
  if (!(res.ok || res.status === 206)) {
    console.warn('[Background] Range request failed, retrying full fetch:', res.status);
    usedRange = false;
    res = await fetchWithBackoff(url, baseHeaders ? { headers: baseHeaders } : undefined, 2, 1200);
  }
  if (!res.ok && res.status !== 206) {
    throw new Error(`Failed to fetch stream (HTTP ${res.status})`);
  }

  const contentLength = parseInt(res.headers.get('content-length') || '0', 10) || null;
  const rangeTotal = parseContentRangeTotal(res.headers.get('content-range'));
  let buf;
  try {
    buf = await res.arrayBuffer();
  } catch (err) {
    // Some hosts will serve the stream but block ranged body reads; retry without Range.
    if (usedRange) {
      console.warn('[Background] Reading ranged response failed, retrying full fetch without Range:', err?.message || err);
      usedRange = false;
      isPartial = false;
      res = await safeFetch(url);
      if (!res.ok) throw new Error(`Failed to fetch stream (HTTP ${res.status})`);
      buf = await res.arrayBuffer();
    } else {
      throw err;
    }
  }
  if (!buf || buf.byteLength === 0) {
    if (usedRange) {
      console.warn('[Background] Ranged sample returned 0 bytes, retrying full fetch...');
      usedRange = false;
      isPartial = false;
      res = await safeFetch(url);
      if (!res.ok) throw new Error(`Failed to fetch stream (HTTP ${res.status})`);
      buf = await res.arrayBuffer();
    }
    if (!buf || buf.byteLength === 0) {
      throw new Error('Stream fetch returned an empty buffer; host may have blocked the request.');
    }
  }
  if (!usedRange && cap && contentLength && contentLength > cap * 1.05) {
    throw new Error(`Refusing full download: stream reports ${Math.round(contentLength / (1024 * 1024))} MB (cap ${Math.round(cap / (1024 * 1024))} MB)`);
  }
  if (!usedRange && cap && buf?.byteLength && buf.byteLength > cap * 1.05) {
    throw new Error(`Refusing full download: fetched ${Math.round(buf.byteLength / (1024 * 1024))} MB (cap ${Math.round(cap / (1024 * 1024))} MB)`);
  }
  onProgress?.(100);

  const sampleBytes = buf.byteLength || 0;
  const assumedPartial = usedRange && res.status !== 206 && !rangeTotal && (
    (contentLength && limit && contentLength >= limit * 0.9) ||
    (limit && sampleBytes >= limit * 0.9)
  );
  if (assumedPartial) {
    console.warn('[Background] Range request returned without Content-Range; treating sample as partial for fallback safety.');
  }
  const totalBytes = rangeTotal || (assumedPartial ? null : contentLength) || null;
  isPartial = usedRange && (res.status === 206 || assumedPartial || (totalBytes && contentLength && contentLength < totalBytes));

  const durationSec = probeContainerDuration(buf);

  return {
    buffer: buf,
    partial: isPartial,
    totalBytes,
    durationSec,
    contentType: res.headers.get('content-type') || ''
  };
}

async function fetchTailSample(url, maxBytes, onProgress, baseHeaders = null) {
  const suffix = Math.max(1024 * 1024, maxBytes || 8 * 1024 * 1024); // at least 1 MB
  const headers = mergeHeaders(baseHeaders, { Range: `bytes=-${suffix}` });
  const res = await fetchWithBackoff(url, { headers }, 2, 1200);
  if (!res.ok && res.status !== 206) {
    throw new Error(`Tail fetch failed (HTTP ${res.status})`);
  }
  const total = parseContentRangeTotal(res.headers.get('content-range')) || null;
  const buf = await res.arrayBuffer();
  if (!buf?.byteLength) {
    throw new Error('Tail fetch returned 0 bytes');
  }
  onProgress?.(100);
  return { buffer: buf, partial: true, totalBytes: total };
}

async function fetchRangeSlice(url, start, end, onProgress, baseHeaders = null) {
  const safeStart = Math.max(0, start || 0);
  const safeEnd = Math.max(safeStart, end || safeStart);
  const headers = mergeHeaders(baseHeaders, { Range: `bytes=${safeStart}-${safeEnd}` });
  const res = await fetchWithBackoff(url, { headers }, 2, 1200);
  if (!res.ok && res.status !== 206) {
    throw new Error(`Range slice fetch failed (HTTP ${res.status})`);
  }
  const buf = await res.arrayBuffer();
  if (!buf?.byteLength) {
    throw new Error('Range slice fetch returned 0 bytes');
  }
  onProgress?.(100);
  return { buffer: buf };
}

function hydrateOffscreenResult(msg) {
  if (!msg) return msg;
  const decoder = new TextDecoder();
  const clone = { ...msg };

  if (Array.isArray(msg.audioWindows)) {
    clone.audioWindows = msg.audioWindows.map((w, idx) => {
      if (w?.transferId) {
        const buf = consumeResultBuffer(w.transferId);
        if (!buf) {
          const entry = _offscreenResultChunks.get(w.transferId);
          const diag = entry ? { received: entry.received, total: entry.totalChunks, missing: (entry.parts || []).filter(p => !p).length } : null;
          console.warn('[Background][Offscreen] Missing audio buffer for window', idx + 1, { transferId: w.transferId, diag });
          throw new Error(`Missing audio buffer for window ${idx + 1}`);
        }
        return {
          ...w,
          audioBytes: buf
        };
      }
      return w;
    });
  }

  if (Array.isArray(msg.tracks)) {
    clone.tracks = msg.tracks.map((t, idx) => {
      if (t?.transferId) {
        const buf = consumeResultBuffer(t.transferId);
        if (!buf) {
          throw new Error(`Missing track buffer for track ${idx + 1}`);
        }
        return {
          ...t,
          content: decoder.decode(buf)
        };
      }
      return t;
    });
  }

  return clone;
}

function waitForOffscreenResult(messageId, timeoutMs = 200000) {
  const startedAt = Date.now();
  logOffscreenLifecycle('wait-for-result:start', { messageId, timeoutMs });
  let settled = false;
  let timer = null;
  let listener = null;

  const cancel = () => {
    if (settled) return;
    settled = true;
    logOffscreenLifecycle('wait-for-result:cancel', { messageId });
    if (timer) clearTimeout(timer);
    if (listener) chrome.runtime.onMessage.removeListener(listener);
  };

  const promise = new Promise((resolve, reject) => {
    listener = (msg) => {
      if ((msg?.type === 'OFFSCREEN_FFMPEG_RESULT' || msg?.type === 'OFFSCREEN_VIDEO_RESULT') && msg.messageId === messageId) {
        console.log('[Background][Offscreen] Received awaited result message', {
          type: msg.type,
          success: msg.success,
          messageId,
          durationMs: Date.now() - startedAt
        });
        try {
          const hydrated = hydrateOffscreenResult(msg);
          cancel();
          resolve({
            success: hydrated.success,
            tracks: hydrated.tracks,
            audioWindows: hydrated.audioWindows,
            error: hydrated.error
          });
        } catch (err) {
          cancel();
          resolve({ success: false, error: err?.message || err });
        }
      }
    };
    chrome.runtime.onMessage.addListener(listener);
    timer = setTimeout(() => {
      console.warn('[Background][Offscreen] Result wait timed out', { messageId, timeoutMs });
      cancel();
      reject(new Error('Offscreen result message timeout'));
    }, timeoutMs);
  });

  return { promise, cancel };
}

function startOffscreenSession() {
  logOffscreenLifecycle('session:start');
  _offscreenActive += 1;
  if (_offscreenCleanupTimer) {
    clearTimeout(_offscreenCleanupTimer);
    _offscreenCleanupTimer = null;
  }
  return () => {
    if (_offscreenActive > 0) _offscreenActive -= 1;
    logOffscreenLifecycle('session:end');
    scheduleOffscreenCleanup();
  };
}

function scheduleOffscreenCleanup(delayMs = OFFSCREEN_IDLE_CLOSE_MS) {
  if (!_offscreenCreated || _offscreenActive > 0) {
    logOffscreenLifecycle('cleanup:skip', { reason: !_offscreenCreated ? 'no-document' : 'active-sessions' });
    return;
  }
  if (_offscreenCleanupTimer) clearTimeout(_offscreenCleanupTimer);
  logOffscreenLifecycle('cleanup:schedule', { delayMs });
  _offscreenCleanupTimer = setTimeout(() => closeOffscreenDocumentSafe(), delayMs);
}

async function closeOffscreenDocumentSafe() {
  if (!_offscreenCreated || _offscreenActive > 0) return;
  logOffscreenLifecycle('close:start');
  _offscreenCleanupTimer = null;
  try {
    if (chrome.offscreen?.hasDocument) {
      const hasDoc = await chrome.offscreen.hasDocument();
      if (!hasDoc) {
        _offscreenCreated = false;
        _offscreenReady = false;
        return;
      }
    }
    if (typeof chrome.offscreen?.closeDocument === 'function') {
      await chrome.offscreen.closeDocument();
      console.log('[Background] Offscreen document closed (idle)');
    }
  } catch (err) {
    console.warn('[Background] Failed to close offscreen document:', err?.message || err);
  } finally {
    _offscreenCreated = false;
    _offscreenReady = false;
    logOffscreenLifecycle('close:finish');
  }
}

async function forceCloseOffscreenDocument(reason = 'force-close') {
  logOffscreenLifecycle('force-close:start', { reason });
  if (_offscreenCleanupTimer) {
    clearTimeout(_offscreenCleanupTimer);
    _offscreenCleanupTimer = null;
  }
  _offscreenReady = false;
  _offscreenActive = 0;
  try {
    if (chrome.offscreen?.hasDocument) {
      const hasDoc = await chrome.offscreen.hasDocument();
      if (!hasDoc) {
        _offscreenCreated = false;
        _offscreenReady = false;
        logOffscreenLifecycle('force-close:finish', { reason, existed: false });
        return;
      }
    }
    if (typeof chrome.offscreen?.closeDocument === 'function') {
      await chrome.offscreen.closeDocument();
      console.log('[Background] Offscreen document closed (forced)', { reason });
    }
  } catch (err) {
    console.warn('[Background] Failed to force-close offscreen document:', err?.message || err);
  } finally {
    _offscreenCreated = false;
    logOffscreenLifecycle('force-close:finish', { reason, existed: true });
  }
}

/**
 * Ensure offscreen document exists for FFmpeg work (Worker support).
 */
async function ensureOffscreenDocument(forceVerify = false) {
  // Validate the cached flag; Chrome can drop the offscreen document without warning.
  if (_offscreenCreated || forceVerify) {
    try {
      if (chrome.offscreen?.hasDocument) {
        const hasDoc = await chrome.offscreen.hasDocument();
        if (hasDoc) {
          _offscreenCreated = true;
          try {
            await waitForOffscreenReady(forceVerify);
            if (!forceVerify) return;
            console.log('[Background] Offscreen document already present (reusing)');
            logOffscreenLifecycle('ensure:reuse');
            return;
          } catch (pingErr) {
            console.warn('[Background] Offscreen document present but unresponsive; recreating', pingErr?.message || pingErr);
            _offscreenCreated = false;
            _offscreenReady = false;
          }
        }
        console.warn('[Background] Offscreen document flag set but hasDocument=false; recreating');
        logOffscreenLifecycle('ensure:stale');
        _offscreenCreated = false;
        _offscreenReady = false;
      } else if (_offscreenCreated && !forceVerify) {
        return;
      }
    } catch (checkErr) {
      console.warn('[Background] Failed to verify offscreen document state:', checkErr?.message || checkErr);
    }
  }
  logOffscreenLifecycle('ensure:start', { forceVerify });
  try {
    if (chrome.offscreen?.hasDocument) {
      const hasDoc = await chrome.offscreen.hasDocument();
      if (hasDoc) {
        _offscreenCreated = true;
        console.log('[Background] Offscreen document already present (reusing)');
        logOffscreenLifecycle('ensure:reuse');
        return;
      }
    }

    await chrome.offscreen.createDocument({
      url: 'pages/offscreen/offscreen.html',
      reasons: ['WORKERS'],
      justification: 'Run FFmpeg demux in a Worker-capable context'
    });
    _offscreenCreated = true;
    _offscreenReady = false;
    console.log('[Background] Offscreen document created for FFmpeg demux');
    logOffscreenLifecycle('ensure:created');
    await waitForOffscreenReady(true);
  } catch (err) {
    const msg = err?.message || '';
    if (msg.includes('already exists') || msg.includes('Only a single offscreen document')) {
      _offscreenCreated = true;
      _offscreenReady = false;
      console.log('[Background] Offscreen document already exists; will reuse existing document');
      logOffscreenLifecycle('ensure:exists');
      await waitForOffscreenReady(forceVerify);
      return;
    }
    console.warn('[Background] Failed to create offscreen document:', msg || err);
    logOffscreenLifecycle('ensure:error', { message: msg || err });
    throw err;
  }
}

function normalizeBufferForTransfer(buffer) {
  if (!buffer) return null;
  if (buffer instanceof ArrayBuffer) return buffer;
  if (ArrayBuffer.isView(buffer)) {
    const view = buffer;
    // Reuse the original view when it already spans the full backing buffer to avoid cloning huge payloads.
    if (view.byteOffset === 0 && view.byteLength === view.buffer.byteLength) {
      return view;
    }
    // Otherwise trim to the view range (clone) to keep the payload scoped correctly.
    return typeof view.slice === 'function'
      ? view.slice()
      : view.buffer.slice(view.byteOffset, view.byteOffset + view.byteLength);
  }
  if (buffer instanceof Blob) {
    return buffer;
  }
  if (typeof buffer.arrayBuffer === 'function') {
    return buffer;
  }
  return null;
}

const MAX_DIRECT_OFFSCREEN_BYTES = 4 * 1024 * 1024; // keep direct messages comfortably under runtime cap
const OFFSCREEN_CHUNK_BYTES = 512 * 1024; // larger chunks to cut transfer time without hitting message caps

function isMessageLengthError(err) {
  const msg = err?.message || '';
  return msg.includes('Message length exceeded') || msg.includes('maximum allowed length');
}

function isMissingOffscreenReceiver(err) {
  const msg = err?.message || '';
  return /receiving end does not exist|could not establish connection/i.test(msg);
}

async function sendBufferToOffscreenInChunks(uintPayload, messageId, tabId) {
  const totalBytes = uintPayload?.byteLength || 0;
  if (!totalBytes) {
    throw new Error('Cannot send empty buffer to offscreen demux.');
  }
  const transferId = `ffbuf_${messageId || Date.now()}_${Math.random().toString(16).slice(2)}`;
  const totalChunks = Math.ceil(totalBytes / OFFSCREEN_CHUNK_BYTES);
  console.log('[Background] Chunking buffer for offscreen demux', { bytes: totalBytes, totalChunks, transferId });
  sendDebugLog(tabId, messageId, `Buffer too large for direct messaging; chunking into ${totalChunks} part(s)...`, 'warn');

  for (let i = 0; i < totalChunks; i++) {
    const shouldLogChunk = totalChunks <= 20 || i === 0 || i === totalChunks - 1 || ((i + 1) % 25 === 0);
    const start = i * OFFSCREEN_CHUNK_BYTES;
    const end = Math.min(totalBytes, start + OFFSCREEN_CHUNK_BYTES);
    const view = uintPayload.subarray(start, end);
    const chunk = view?.byteLength
      ? view.buffer.slice(view.byteOffset, view.byteOffset + view.byteLength) // clone into a standalone ArrayBuffer
      : null;
    if (!chunk || chunk.byteLength === 0) {
      throw new Error(`Generated empty chunk ${i + 1}/${totalChunks} for offscreen demux`);
    }
    const chunkArray = Array.from(view); // send as plain array to avoid ArrayBuffer detachment issues
    await new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({
        type: 'OFFSCREEN_FFMPEG_BUFFER_CHUNK',
        transferId,
        chunkIndex: i,
        totalChunks,
        chunkArray,
        expectedBytes: view.byteLength
      }, (resp) => {
        if (chrome.runtime.lastError) {
          return reject(new Error(`Offscreen chunk send failed: ${chrome.runtime.lastError.message}`));
        }
        if (resp?.ok === false) {
          return reject(new Error(`Offscreen chunk ${i + 1}/${totalChunks} rejected: ${resp?.error || 'unknown error'}`));
        }
        if (shouldLogChunk) {
          console.log('[Background] Offscreen chunk sent', {
            chunk: i + 1,
            totalChunks,
            bytes: view.byteLength,
            transferId
          });
        }
        resolve();
      });
    });
  }
  console.log('[Background] Completed chunk send to offscreen', { transferId, totalChunks });
  return { transferId, totalChunks };
}

/**
 * Extract embedded subtitles via video element in offscreen document
 * This is the preferred method as it gets complete tracks without downloading the full video
 */
async function extractSubtitlesViaVideoOffscreen(streamUrl, mode, messageId, tabId) {
  const normalizedMode = 'single';
  const endOffscreen = startOffscreenSession();
  let cancel = null;
  const startedAt = Date.now();
  try {
    await ensureOffscreenDocument();
    sendDebugLog(tabId, messageId, `Video-based extraction: starting (${normalizedMode} mode)`, 'info');

    const requestId = messageId || `vextract_${Date.now()}`;
    console.log('[Background][Offscreen] Dispatching OFFSCREEN_VIDEO_EXTRACT', {
      requestId,
      streamUrl: streamUrl?.substring(0, 80),
      mode: normalizedMode
    });

    const waitRes = waitForOffscreenResult(requestId, 180000);
    cancel = waitRes.cancel;

    await chrome.runtime.sendMessage({
      type: 'OFFSCREEN_VIDEO_EXTRACT',
      messageId: requestId,
      streamUrl,
      mode: normalizedMode
    });

    const result = await waitRes.promise;

    if (!result.success) {
      throw new Error(result.error || 'Video extraction failed');
    }

    sendDebugLog(tabId, messageId, `Video extraction completed: ${result.tracks?.length || 0} track(s)`, 'info');
    console.log('[Background][Offscreen] Video extraction resolved', {
      requestId,
      success: result.success,
      trackCount: result.tracks?.length,
      durationMs: Date.now() - startedAt
    });
    return result.tracks || [];
  } catch (err) {
    console.warn('[Background][Offscreen] Video extraction error', {
      messageId,
      message: err?.message || err,
      durationMs: Date.now() - startedAt
    });
    if (typeof cancel === 'function') cancel();
    throw err;
  } finally {
    endOffscreen();
  }
}

const TRACK_LANG_NORMALIZE_MAP = {
  eng: 'en', enu: 'en', enus: 'en', enn: 'en', enuk: 'en', en_gb: 'en', en_gb: 'en', enus: 'en', engb: 'en', enau: 'en', enze: 'en',
  spa: 'es', esl: 'es', esu: 'es', esp: 'es', espanol: 'es', spn: 'es', es419: 'es', lat: 'es', latam: 'es', castellano: 'es',
  por: 'por', pt: 'por', porpt: 'por', pt_pt: 'por',
  pob: 'pob', pb: 'pob', ptb: 'pob', ptbr: 'pob', 'pt-br': 'pob', porbr: 'pob', brazpor: 'pob', brazilian: 'pob',
  fre: 'fr', fra: 'fr', frf: 'fr', frca: 'fr', frfr: 'fr',
  ger: 'de', deu: 'de', gerde: 'de',
  ita: 'it', itb: 'it',
  rus: 'ru', rusru: 'ru',
  chi: 'zh', zho: 'zh', cmn: 'zh', mlt: 'zh', mnd: 'zh', chs: 'zh', cht: 'zh', zhn: 'zh', zhcn: 'zh', zhtw: 'zh', zh_hans: 'zh', zh_hant: 'zh',
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
  if (/^extracte/.test(rawStr)) return null;
  if (/^extracted[_\s-]?sub/.test(rawStr)) return null;
  if (/^remux[_\s-]?sub/.test(rawStr)) return null;
  if (/^track\s*\d+/.test(rawStr)) return null;
  if (/^subtitle\s*\d+/.test(rawStr)) return null;
  const cleaned = rawStr.replace(/[^a-z-]/g, '');
  if (!cleaned) return null;
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
      best = lang;
    } else if (score > runnerUp) {
      runnerUp = score;
    }
  }

  const asciiLetters = (sample.match(/[A-Za-z]/g) || []).length;
  const nonAsciiLetters = (sample.match(/[^\x00-\x7F]/g) || []).length;
  const asciiRatio = asciiLetters / Math.max(1, asciiLetters + nonAsciiLetters);

  if (best && (bestScore >= 0.04 || (bestScore >= 0.025 && bestScore >= runnerUp * 1.35))) {
    return normalizeTrackLanguageCode(best) || best;
  }
  if (!best && asciiRatio > 0.9 && latinLetters > 20) return 'en';
  return null;
}

function applyContentLanguageGuesses(tracks) {
  if (!Array.isArray(tracks)) return tracks || [];
  return tracks.map((track) => {
    if (!track || (track.language && track.language !== 'und')) return track;
    const content = typeof track.content === 'string' ? track.content : null;
    const guess = detectLanguageFromContent(content);
    if (guess) {
      return { ...track, language: guess, languageRaw: track.languageRaw || guess };
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
        ? Math.min(end, p + 16 + Number(readU32(p + 8)) * 2 ** 32) // large size; coarse safeguard
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

function applyHeaderLanguagesToTracks(tracks, headerLangs) {
  if (!Array.isArray(tracks) || !tracks.length || !Array.isArray(headerLangs) || !headerLangs.length) return tracks || [];
  const usable = headerLangs.filter((l) => l && l.lang);
  if (!usable.length) return tracks;

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
    if (track?.language && track.language !== 'und') return track;
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
    if (langEntry?.lang) {
      const nextLabel = !track?.label || isGeneratedLabel(track.label)
        ? (langEntry.name || track?.label || `Track ${idx + 1}`)
        : track.label;
      return {
        ...track,
        language: langEntry.lang,
        label: nextLabel
      };
    }
    const labelSource = [track?.label, track?.name, track?.originalLabel].find((l) => l && !isGeneratedLabel(l));
    const labelGuess = labelSource ? detectLanguageFromLabel(labelSource) : null;
    if (labelGuess) return { ...track, language: labelGuess };
    return track;
  });
}

function filterTextTracksOnly(tracks) {
  if (!Array.isArray(tracks)) return [];
  return tracks.filter((t) => t && !(t.binary || t.codec === 'copy' || (typeof t.mime === 'string' && t.mime.toLowerCase().includes('matroska')) || t.source === 'copy'));
}

async function demuxSubtitlesOffscreen(buffer, messageId, tabId) {
  const endOffscreen = startOffscreenSession();
  const startedAt = Date.now();
  try {
    await ensureOffscreenDocument();
    sendDebugLog(tabId, messageId, 'Offscreen FFmpeg demux: starting', 'info');
    let payload = normalizeBufferForTransfer(buffer);
    if (payload instanceof Blob) {
      payload = await payload.arrayBuffer();
    }
    if (!payload) {
      throw new Error('Invalid media buffer for offscreen demux');
    }
    // Force a Uint8Array clone to avoid accidental zero-length transfers
    const uintPayload = payload instanceof Uint8Array
      ? payload
      : new Uint8Array(payload);
    const sendBytes = uintPayload.byteLength;
    if (!sendBytes) {
      throw new Error('Media buffer is empty; cannot send to offscreen demux');
    }
    console.log('[Background] Sending buffer to offscreen demux', {
      type: uintPayload?.constructor?.name,
      bytes: sendBytes,
      messageId
    });
    logOffscreenLifecycle('demux:start', { messageId, bytes: sendBytes });
    const timeoutMs = 180000; // allow time for first-time core download
    const { promise: pushedResponse, cancel: cancelPushWait } = waitForOffscreenResult(messageId, timeoutMs + 20000);
    let cancelDirect = null;
    const sendDemuxRequest = (payload) => new Promise((resolve, reject) => {
      let settled = false;
      const finish = (fn, val) => {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
        fn(val);
      };
      const timer = setTimeout(() => finish(reject, new Error('Offscreen demux timed out')), timeoutMs);
      cancelDirect = () => {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
      };
      try {
        console.log('[Background][Offscreen] Sending demux request payload', {
          messageId: payload?.messageId,
          hasBuffer: !!payload?.buffer,
          transferId: payload?.transferId,
          timeoutMs
        });
        chrome.runtime.sendMessage(payload, (resp) => {
          if (settled) return;
          if (chrome.runtime.lastError) {
            console.warn('[Background][Offscreen] Demux request error', {
              messageId: payload?.messageId,
              error: chrome.runtime.lastError.message
            });
            return finish(reject, new Error(`Offscreen message error: ${chrome.runtime.lastError.message}`));
          }
          console.log('[Background][Offscreen] Direct demux response received', {
            messageId: payload?.messageId,
            success: resp?.success,
            durationMs: Date.now() - startedAt
          });
          finish(resolve, resp);
        });
      } catch (err) {
        finish(reject, err);
      }
    });

    let response;
    let lastError = null;
    const mustChunk = sendBytes > MAX_DIRECT_OFFSCREEN_BYTES;
    try {
      for (let attempt = 0; attempt < 2; attempt++) {
        try {
          if (mustChunk) {
            const Transfer = await ensureTransferHelper();
            console.log('[Background] Buffer exceeds direct offscreen limit; using IDB transfer', { bytes: sendBytes });

            // Use IndexedDB transfer instead of chunked messaging
            const transferId = `idb_${messageId}_${Date.now()}${attempt ? `_retry${attempt}` : ''}`;
            await Transfer.saveTransferBuffer(transferId, uintPayload);

            response = await sendDemuxRequest({
              type: 'OFFSCREEN_FFMPEG_EXTRACT',
              messageId,
              transferId,
              transferMethod: 'idb'
            });
          } else {
            response = await sendDemuxRequest({
              type: 'OFFSCREEN_FFMPEG_EXTRACT',
              messageId,
              buffer: uintPayload
            });
          }
          break; // success, stop retry loop
        } catch (err) {
          lastError = err;

          // If a direct send unexpectedly trips the runtime size cap, retry with IDB
          if (!mustChunk && isMessageLengthError(err)) {
            console.warn('[Background] Direct offscreen message too large; retrying with IDB transfer', { bytes: sendBytes });

            const Transfer = await ensureTransferHelper();
            const transferId = `idb_${messageId}_${Date.now()}_retry`;
            await Transfer.saveTransferBuffer(transferId, uintPayload);

            response = await sendDemuxRequest({
              type: 'OFFSCREEN_FFMPEG_EXTRACT',
              messageId,
              transferId,
              transferMethod: 'idb'
            });
            break;
          }

          // If the offscreen page vanished, recreate it and retry once.
        if (isMissingOffscreenReceiver(err) && attempt === 0) {
          console.warn('[Background][Offscreen] Demux receiver missing; recreating offscreen document and retrying', {
            messageId,
            error: err?.message
          });
          _offscreenCreated = false;
          _offscreenReady = false;
          try { await forceCloseOffscreenDocument('missing-offscreen-retry'); } catch (_) { }
          await ensureOffscreenDocument(true);
          continue;
        }

          // Non-retryable error
          throw err;
        }
      }
      if (!response && lastError) {
        throw lastError;
      }

      // If the response is slim (no tracks or chunked), wait for the pushed result that carries the full payload.
      const needsPushResult = response?.success && (!response.tracks || !response.tracks.length || response.chunked);
      if (needsPushResult) {
        try {
          console.log('[Background][Offscreen] Waiting for pushed demux result (tracks missing from direct response)...', { messageId });
          const pushed = await pushedResponse;
          if (pushed) {
            response = pushed;
          }
        } catch (pushErr) {
          console.warn('[Background][Offscreen] Pushed demux result wait failed; falling back to direct response', {
            messageId,
            error: pushErr?.message || pushErr
          });
        }
      }

      if (!response) {
        console.warn('[Background][Offscreen] Demux response missing', { messageId, durationMs: Date.now() - startedAt });
        throw new Error('Offscreen demux returned no response');
      }
      if (response?.success) {
        sendDebugLog(tabId, messageId, 'Offscreen FFmpeg demux: completed', 'info');
        let tracks = response.tracks || [];
        const headerLangs = collectSubtitleLanguagesFromHeader(uintPayload);
        if (headerLangs.length) {
          const beforeCount = (tracks || []).filter(t => t && t.language && t.language !== 'und').length;
          tracks = applyHeaderLanguagesToTracks(tracks, headerLangs);
          const afterCount = (tracks || []).filter(t => t && t.language && t.language !== 'und').length;
          if (afterCount > beforeCount) {
            sendDebugLog(tabId, messageId, `Detected language tags for ${afterCount} track(s) from MKV header`, 'info');
          }
        }
        tracks = applyContentLanguageGuesses(tracks);
        const filtered = filterTextTracksOnly(tracks);
        if (filtered.length !== tracks.length) {
          sendDebugLog(tabId, messageId, `Omitted ${tracks.length - filtered.length} binary/copy track(s) from response`, 'info');
        }
        console.log('[Background][Offscreen] Demux response success', {
          messageId,
          trackCount: filtered?.length,
          durationMs: Date.now() - startedAt
        });
        return filtered;
      }
      const errMsg = response?.error || 'Offscreen demux failed';
      sendDebugLog(tabId, messageId, `Offscreen FFmpeg demux failed: ${errMsg}`, 'error');
      console.warn('[Background][Offscreen] Demux response error', { messageId, error: errMsg, durationMs: Date.now() - startedAt });
      throw new Error(errMsg);
    } finally {
      cancelDirect?.();
      cancelPushWait();
    }
  } finally {
    endOffscreen();
  }
}

async function resolveHlsPlaylist(m3u8Url, baseHeaders = null, depth = 0) {
  if (depth > 3) throw new Error('HLS playlist recursion exceeded');
  const text = await (await safeFetch(m3u8Url, baseHeaders ? { headers: baseHeaders } : undefined)).text();
  const parseAttrs = (line) => {
    const attrs = {};
    line.replace(/([A-Z0-9-]+)=("[^"]*"|[^,]*)/gi, (_, k, v) => {
      const key = k.toUpperCase();
      const val = v?.startsWith('"') && v.endsWith('"') ? v.slice(1, -1) : v;
      attrs[key] = val;
      return '';
    });
    return attrs;
  };
  const parseMap = (line) => {
    const attrs = parseAttrs(line);
    if (!attrs.URI) return null;
    const map = { uri: new URL(attrs.URI, m3u8Url).toString() };
    if (attrs.BYTERANGE) {
      const parts = String(attrs.BYTERANGE).split('@');
      const len = parseInt(parts[0], 10);
      const offset = parts[1] ? parseInt(parts[1], 10) : null;
      if (Number.isFinite(len) && len > 0) {
        map.byterange = { length: len, offset: Number.isFinite(offset) ? offset : null };
      }
    }
    return map;
  };

  // Master playlist
  if (/EXT-X-STREAM-INF/i.test(text)) {
    const lines = text.split(/\r?\n/);
    const variants = [];
    const audioGroups = new Map();
    const subtitleTracks = [];
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (line.startsWith('#EXT-X-STREAM-INF')) {
        const attrs = parseAttrs(line);
        const uri = lines[i + 1];
        if (uri && !uri.startsWith('#')) {
          variants.push({
            uri,
            bw: parseInt(attrs.BANDWIDTH || '0', 10) || 0,
            codecs: (attrs.CODECS || '').toLowerCase(),
            audioGroup: attrs.AUDIO || null
          });
        }
      } else if (line.startsWith('#EXT-X-MEDIA')) {
        const attrs = parseAttrs(line);
        const type = (attrs.TYPE || '').toUpperCase();
        if (type === 'AUDIO' && attrs.URI) {
          audioGroups.set(attrs['GROUP-ID'] || '', {
            uri: attrs.URI,
            isDefault: String(attrs.DEFAULT || '').toUpperCase() === 'YES',
            autoselect: String(attrs.AUTOSELECT || '').toUpperCase() === 'YES'
          });
        } else if (type === 'SUBTITLES') {
          subtitleTracks.push({
            groupId: attrs['GROUP-ID'] || '',
            lang: normalizeTrackLanguageCode(attrs.LANGUAGE || ''),
            name: attrs.NAME || '',
            uri: attrs.URI ? new URL(attrs.URI, m3u8Url).toString() : null,
            isDefault: String(attrs.DEFAULT || '').toUpperCase() === 'YES',
            autoselect: String(attrs.AUTOSELECT || '').toUpperCase() === 'YES'
          });
        }
      }
    }

    const pickAudioMedia = () => {
      for (const [_id, meta] of audioGroups) {
        if (meta.isDefault) return meta;
      }
      for (const [_id, meta] of audioGroups) {
        if (meta.autoselect) return meta;
      }
      const first = audioGroups.values().next();
      return first && !first.done ? first.value : null;
    };

    const preferredVariant = (() => {
      // Prefer variant with audio codecs if present
      const withAudioCodec = variants.filter(v => /mp4a|aac|audio/.test(v.codecs));
      if (withAudioCodec.length) {
        return withAudioCodec.sort((a, b) => b.bw - a.bw)[0];
      }
      // Otherwise highest bandwidth as before
      return variants.sort((a, b) => b.bw - a.bw)[0];
    })();

    const audioChoice = (() => {
      if (!variants.length || !audioGroups.size) return null;
      const groupId = preferredVariant?.audioGroup || (variants[0] && variants[0].audioGroup);
      if (groupId && audioGroups.has(groupId)) {
        return audioGroups.get(groupId);
      }
      return pickAudioMedia();
    })();

    if (audioChoice?.uri) {
      const audioUrl = new URL(audioChoice.uri, m3u8Url).toString();
      return { ...(await resolveHlsPlaylist(audioUrl, baseHeaders, depth + 1)), subtitleLangs: subtitleTracks };
    }

    if (!preferredVariant?.uri) throw new Error('No variant stream found');
    const variantUrl = new URL(preferredVariant.uri, m3u8Url).toString();
    return { ...(await resolveHlsPlaylist(variantUrl, baseHeaders, depth + 1)), subtitleLangs: subtitleTracks };
  }

  // Media playlist
  const segments = [];
  const lines = text.split(/\r?\n/);
  let totalDur = 0;
  let map = null;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('#EXT-X-MAP')) {
      map = parseMap(lines[i]) || map;
      continue;
    }
    if (lines[i].startsWith('#EXTINF:')) {
      const dur = parseFloat(lines[i].split(':')[1]);
      const uri = lines[i + 1];
      if (uri && !uri.startsWith('#')) {
        segments.push({ uri: new URL(uri, m3u8Url).toString(), dur });
        totalDur += dur;
      }
    }
  }
  if (segments.length === 0) throw new Error('No HLS segments');
  return { playlistUrl: m3u8Url, segments, totalDurationSec: totalDur, map, subtitleLangs: [] };
}

function sliceSegmentsForWindow(segments, startSec, durSec) {
  const chosen = [];
  let acc = 0;
  for (const seg of segments) {
    const segStart = acc;
    const segEnd = acc + seg.dur;
    if (segEnd >= startSec && segStart <= startSec + durSec) {
      chosen.push({ ...seg, startSec: segStart });
    }
    acc += seg.dur;
    if (acc > startSec + durSec + 30) break;
  }
  return chosen;
}

async function fetchHlsWindows(m3u8Url, onProgress, planInput = null, baseHeaders = null) {
  const { segments, totalDurationSec, map, subtitleLangs = [] } = await resolveHlsPlaylist(m3u8Url, baseHeaders);
  const { windows } = planWindows(totalDurationSec, normalizeSyncPlan(planInput));
  const totalSegmentsToFetch = windows
    .map(w => sliceSegmentsForWindow(segments, w.startSec, w.durSec).length)
    .reduce((a, b) => a + b, 0) || 1;

  let fetchedCount = 0;
  const result = [];
  let mapBytes = null;

  if (map?.uri) {
    try {
      const headers = map.byterange
        ? mergeHeaders(baseHeaders, { Range: `bytes=${map.byterange.offset || 0}-${(map.byterange.offset || 0) + map.byterange.length - 1}` })
        : baseHeaders;
      const res = await safeFetch(map.uri, headers ? { headers } : undefined);
      if (!res.ok) throw new Error(`Init segment fetch failed (${res.status})`);
      mapBytes = new Uint8Array(await res.arrayBuffer());
      const expected = map.byterange?.length;
      if (expected && mapBytes.byteLength !== expected) {
        console.warn('[Background][HLS] Init segment length mismatch', { expected, actual: mapBytes.byteLength });
      }
    } catch (err) {
      console.warn('[Background][HLS] Failed to fetch EXT-X-MAP init segment:', err?.message || err);
    }
  }

  for (const window of windows) {
    let segs = sliceSegmentsForWindow(segments, window.startSec, window.durSec);
    const effectiveStartSec = window.startSec;
    if (!segs.length) {
      throw new Error(`HLS window @${window.startSec}s has no segments`);
    }
    const buffers = [];
    for (const seg of segs) {
      const res = await safeFetch(seg.uri, baseHeaders ? { headers: baseHeaders } : undefined);
      if (!res.ok) throw new Error(`Segment fetch failed: ${res.status}`);
      buffers.push(new Uint8Array(await res.arrayBuffer()));
      fetchedCount += 1;
      onProgress(Math.min(100, Math.round((fetchedCount / totalSegmentsToFetch) * 80)));
    }
    const totalBytes = buffers.reduce((n, a) => n + a.byteLength, 0) + (mapBytes?.byteLength || 0);
    const out = new Uint8Array(totalBytes);
    let offset = 0;
    if (mapBytes) {
      out.set(mapBytes, offset);
      offset += mapBytes.byteLength;
    }
    for (const buf of buffers) { out.set(buf, offset); offset += buf.byteLength; }
    result.push({
      buffer: out.buffer,
      startSec: effectiveStartSec,
      durSec: window.durSec
    });
  }

  onProgress(100);
  return { windows: result, totalDurationSec, subtitleLangs };
}

async function fetchHlsSample(m3u8Url, onProgress, options = {}, baseHeaders = null) {
  const { segments, totalDurationSec, map, subtitleLangs = [] } = await resolveHlsPlaylist(m3u8Url, baseHeaders);
  const baseTarget = 900; // seconds to grab in single mode
  const targetDuration = Math.max(baseTarget, Math.round(options?.minDurationSec || 0));
  const buffers = [];
  let accumulated = 0;
  let fetched = 0;
  let mapBytes = null;

  if (map?.uri) {
    try {
      const headers = map.byterange
        ? mergeHeaders(baseHeaders, { Range: `bytes=${map.byterange.offset || 0}-${(map.byterange.offset || 0) + map.byterange.length - 1}` })
        : baseHeaders;
      const res = await safeFetch(map.uri, headers ? { headers } : undefined);
      if (!res.ok) throw new Error(`Init segment fetch failed (${res.status})`);
      mapBytes = new Uint8Array(await res.arrayBuffer());
    } catch (err) {
      console.warn('[Background][HLS] Failed to fetch EXT-X-MAP init segment for sample:', err?.message || err);
    }
  }

  for (const seg of segments) {
    const res = await safeFetch(seg.uri, baseHeaders ? { headers: baseHeaders } : undefined);
    if (!res.ok) throw new Error(`Segment fetch failed: ${res.status}`);
    buffers.push(new Uint8Array(await res.arrayBuffer()));
    accumulated += seg.dur;
    fetched += 1;
    const pct = Math.min(100, Math.round((accumulated / Math.max(targetDuration, accumulated)) * 100));
    onProgress?.(pct);
    if (accumulated >= targetDuration) break;
  }

  const totalBytes = buffers.reduce((n, a) => n + a.byteLength, 0) + (mapBytes?.byteLength || 0);
  const out = new Uint8Array(totalBytes);
  let offset = 0;
  if (mapBytes) {
    out.set(mapBytes, offset);
    offset += mapBytes.byteLength;
  }
  for (const buf of buffers) { out.set(buf, offset); offset += buf.byteLength; }
  onProgress?.(100);
  return { buffer: out.buffer, durationSec: totalDurationSec, subtitleLangs };
}

// ---------- Helpers: FFmpeg loader ----------
async function loadBareFfmpegCore() {
  try {
    if (typeof self.createFFmpegCore !== 'function') {
      const coreUrl = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/ffmpeg-core.js') : 'assets/lib/ffmpeg-core.js';
      importScripts(coreUrl);
    }
    if (typeof self.createFFmpegCore !== 'function') {
      throw new Error('createFFmpegCore not found after loading ffmpeg-core.js');
    }

    const module = await self.createFFmpegCore({
      locateFile: (path) => chrome.runtime?.getURL ? chrome.runtime.getURL(`assets/lib/${path}`) : path,
      print: (msg) => console.log('[Background][FFmpeg]', msg),
      printErr: (msg) => console.warn('[Background][FFmpeg]', msg)
    });

    const ffmpeg = {
      FS: (cmd, ...args) => {
        const target = module.FS || module;
        const fn = target?.[cmd];
        if (typeof fn === 'function') return fn.apply(target, args);
        if (typeof target.FS === 'function') return target.FS(cmd, ...args);
        throw new Error(`FFmpeg FS command unavailable: ${cmd}`);
      },
      run: async (...args) => {
        const argv = Array.isArray(args[0]) ? args[0] : args;
        const ret = typeof module.exec === 'function'
          ? module.exec(...argv)
          : module.callMain
            ? module.callMain(argv)
            : 0;
        if (typeof ret === 'number' && ret !== 0) {
          throw new Error(`FFmpeg exited with code ${ret}`);
        }
      }
    };

    _ffmpegMode = 'bare-core';
    _ffmpegInstance = ffmpeg;
    return ffmpeg;
  } catch (err) {
    console.warn('[Background] Bare FFmpeg core load failed:', err?.message || err);
    throw err;
  }
}

async function getFFmpeg(onProgress) {
  // Service worker environment cannot spin up Workers after installation; bail to offscreen path.
  if (typeof Worker === 'undefined') {
    console.warn('[Background] Worker API unavailable; will defer FFmpeg work to offscreen page');
    return null;
  }
  if (_ffmpegInstance) return _ffmpegInstance;
  try {
    const createFFmpeg = await ensureFfmpegFactory();
    const preferMt = typeof SharedArrayBuffer !== 'undefined' && typeof Worker === 'function';
    const corePath = preferMt
      ? chrome.runtime.getURL('assets/lib/ffmpeg-core-mt.js')
      : chrome.runtime.getURL('assets/lib/ffmpeg-core.js');
    const mainName = preferMt ? 'ffmpeg-core-mt' : 'ffmpeg-core';
    const ffmpeg = createFFmpeg({ log: false, corePath, mainName });
    onProgress?.(78);
    await ffmpeg.load();
    _ffmpegInstance = ffmpeg;
    _ffmpegMode = preferMt ? 'multi-thread' : 'single-thread';
    return _ffmpegInstance;
  } catch (e) {
    console.warn('[Background] FFmpeg load failed:', e?.message || e);
    try {
      onProgress?.(82);
      const ffmpeg = await loadBareFfmpegCore();
      onProgress?.(90);
      return ffmpeg;
    } catch (_) {
      // already logged in loadBareFfmpegCore
    }
    return null;
  }
}

async function decodeWindowsWithFFmpeg(windows, mode, onProgress, ctx = null, opts = {}) {
  // Primary path: offscreen document (Worker-capable) mirrors embedded-subtitles flow
  let decoded = null;
  const expectedCount = Array.isArray(windows) ? windows.length : 0;
  const strictWhenTooFew = opts?.strictWhenTooFew === true;
  const allowPartialOnStrictFail = opts?.allowPartialOnStrictFail !== false;
  const requireAll = opts?.requireAll === true;
  if (ctx?.tabId) {
    const desc = (windows || []).map((w, idx) => `#${idx + 1}@${Math.round((w.startSec || 0) * 1000) / 1000}s len=${w.durSec || '?'}s seek=${w.seekToSec || 0}s bytes=${w.buffer?.byteLength || 0}`).join(' | ');
    sendDebugLog(ctx.tabId, ctx.messageId, `FFmpeg decode request (${expectedCount} win): ${desc}`, 'info');
  }
  try {
    onProgress?.(70, 'Decoding audio via offscreen FFmpeg...');
    sendDebugLog(ctx?.tabId, ctx?.messageId, `Dispatching offscreen decode (${expectedCount} window(s))`, 'info');
    decoded = await decodeWindowsOffscreen(windows, mode, onProgress, ctx, { audioStreamIndex: opts?.audioStreamIndex });
  } catch (offErr) {
    console.warn('[Background] Offscreen FFmpeg decode failed:', offErr?.message || offErr);
    // Secondary best-effort local decode (may fail in service worker)
    try {
      onProgress?.(75, 'Retrying audio decode locally...');
      sendDebugLog(ctx?.tabId, ctx?.messageId, `Offscreen decode failed (${offErr?.message || offErr}); retrying locally`, 'warn');
      decoded = await decodeWindowsLocal(windows, mode, onProgress, { audioStreamIndex: opts?.audioStreamIndex });
    } catch (localErr) {
      console.warn('[Background] Local FFmpeg decode also failed:', localErr?.message || localErr);
      sendDebugLog(ctx?.tabId, ctx?.messageId, `Local FFmpeg decode failed: ${localErr?.message || localErr}`, 'error');
      throw offErr || localErr;
    }
  }

  // Validate decoded WAV windows to weed out empty/header-only outputs before autosync.
  const { validWindows, diagnostics, summary, invalidCount } = await inspectAndFilterWavWindows(decoded || [], ctx, 'audio decode inspect');
  if (!validWindows.length) {
    throw new Error('FFmpeg decode returned no usable audio windows');
  }
  if (invalidCount > 0) {
    console.warn('[Background] Dropped invalid decoded audio window(s):', summary || `${invalidCount} invalid`);
    if (ctx?.tabId) {
      sendDebugLog(ctx.tabId, ctx.messageId, `Dropped ${invalidCount} decoded window(s): ${summary}`, 'warn');
    }
    const tooFew = requireAll
      ? validWindows.length < expectedCount
      : validWindows.length < Math.max(1, Math.ceil(expectedCount / 2));
    if (tooFew && strictWhenTooFew) {
      const msg = `Decoded only ${validWindows.length}/${expectedCount} valid audio window(s)${summary ? ` (${summary})` : ''}`;
      if (ctx?.tabId) {
        sendDebugLog(ctx.tabId, ctx.messageId, msg, 'warn');
      }
      console.warn('[Background]', msg);
      if (!allowPartialOnStrictFail) {
        throw new Error(msg);
      }
    }
  }
  return validWindows;
}

async function decodeWindowsLocal(windows, mode, onProgress, opts = {}) {
  const ffmpeg = await getFFmpeg(onProgress);
  if (!ffmpeg) throw new Error('FFmpeg not available');

  const results = [];
  const sharedBuffer = windows.length > 1 && windows.every(w => w.buffer === windows[0].buffer);
  let sharedInputName = null;
  if (sharedBuffer) {
    sharedInputName = 'shared_input.bin';
    ffmpeg.FS('writeFile', sharedInputName, new Uint8Array(windows[0].buffer));
  }

  for (let i = 0; i < windows.length; i++) {
    const inputName = sharedInputName || `win_${i}.bin`;
    const outputName = `win_${i}.wav`;
    try {
      if (!sharedInputName) {
        ffmpeg.FS('writeFile', inputName, new Uint8Array(windows[i].buffer));
      }
      const buildArgs = () => {
        const base = ['-i', inputName, '-vn'];
        if (Number.isInteger(opts?.audioStreamIndex) && opts.audioStreamIndex >= 0) {
          base.push('-map', `0:a:${opts.audioStreamIndex}`);
        }
        base.push('-acodec', 'pcm_s16le', '-ar', '16000');
        // Avoid mixing bilingual dual-mono tracks; explicitly keep the left channel only.
        base.push('-af', 'pan=mono|c0=c0', '-ac', '1');
        const args = [...base];
        if (typeof windows[i].durSec === 'number' && windows[i].durSec > 0) {
          args.push('-t', String(windows[i].durSec));
        }
        args.push(outputName);
        if (typeof windows[i].seekToSec === 'number' && windows[i].seekToSec > 0) {
          args.unshift('-ss', String(windows[i].seekToSec));
        }
        return args;
      };

      await ffmpeg.run(...buildArgs());
      const data = ffmpeg.FS('readFile', outputName);
      if (!data?.byteLength) {
        throw new Error(`Empty decode result for window ${i + 1}`);
      }
      results.push({
        audioBlob: new Blob([data.buffer], { type: 'audio/wav' }),
        startMs: Math.round(((windows[i].startSec ?? windows[i].seekToSec ?? 0) || 0) * 1000)
      });
      if (!sharedInputName) {
        ffmpeg.FS('unlink', inputName);
      }
      ffmpeg.FS('unlink', outputName);
    } catch (err) {
      console.warn('[Background] FFmpeg decode failed for window', i, err?.message);
    }
    onProgress?.(Math.min(100, Math.round(((i + 1) / windows.length) * 100)));
  }
  if (sharedInputName) {
    try { ffmpeg.FS('unlink', sharedInputName); } catch (_) { /* ignore */ }
  }
  if (!results.length) {
    throw new Error('FFmpeg could not decode any window');
  }
  return results;
}

function mockSilentWav(seconds) {
  // Minimal PCM S16LE WAV header + silence
  const sampleRate = 16000, channels = 1, bps = 16;
  const frameCount = seconds * sampleRate;
  const dataSize = frameCount * channels * (bps / 8);
  const buffer = new ArrayBuffer(44 + dataSize);
  const v = new DataView(buffer);
  const u8 = new Uint8Array(buffer);
  // RIFF header
  u8.set([82, 73, 70, 70]); // 'RIFF'
  v.setUint32(4, 36 + dataSize, true);
  u8.set([87, 65, 86, 69], 8); // 'WAVE'
  u8.set([102, 109, 116, 32], 12); // 'fmt '
  v.setUint32(16, 16, true); // PCM fmt chunk size
  v.setUint16(20, 1, true); // PCM
  v.setUint16(22, channels, true);
  v.setUint32(24, sampleRate, true);
  v.setUint32(28, sampleRate * channels * (bps / 8), true);
  v.setUint16(32, channels * (bps / 8), true);
  v.setUint16(34, bps, true);
  u8.set([100, 97, 116, 97], 36); // 'data'
  v.setUint32(40, dataSize, true);
  // data already zeroed (silence)
  return new Blob([buffer], { type: 'audio/wav' });
}

// ---------- Helpers: alass-wasm loader ----------
async function getFfsubsync(ctx = null) {
  const logToPage = (text, level = 'error') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  if (_ffsubsyncReady && _ffsubsyncApi) return _ffsubsyncApi;
  try {
    if (!self.SubMakerFfsubsync) {
      const loaderUrl = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/ffsubsync-wasm.js') : 'assets/lib/ffsubsync-wasm.js';
      if (typeof importScripts !== 'function') {
        console.warn('[Background] importScripts unavailable for ffsubsync loader');
        logToPage('ffsubsync loader unavailable in this environment', 'error');
        return null;
      }
      try {
        await importScriptSafe(loaderUrl, 'ffsubsync-wasm.js');
      } catch (loadErr) {
        console.warn('[Background] Failed to load ffsubsync-wasm wrapper:', loadErr?.message);
        logToPage(`ffsubsync wrapper load failed: ${loadErr?.message || loadErr}`, 'error');
        return null;
      }
    }
    if (!self.SubMakerFfsubsync || typeof self.SubMakerFfsubsync.init !== 'function') {
      console.warn('[Background] ffsubsync-wasm wrapper not found');
      logToPage('ffsubsync-wasm wrapper not found after load', 'error');
      return null;
    }
    const wasmPath = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/ffsubsync_wasm_bg.wasm') : 'assets/lib/ffsubsync_wasm_bg.wasm';
    _ffsubsyncApi = await self.SubMakerFfsubsync.init({ wasmPath });
    _ffsubsyncReady = !!_ffsubsyncApi;
    console.log('[Background] ffsubsync-wasm initialized', { ready: !!_ffsubsyncApi });
    return _ffsubsyncApi;
  } catch (e) {
    console.warn('[Background] Failed to load ffsubsync-wasm:', e?.message, e?.stack);
    logToPage(`ffsubsync-wasm init failed: ${e?.message || e}`, 'error');
    return null;
  }
}

async function getAlass(ctx = null) {
  const logToPage = (text, level = 'error') => {
    if (ctx?.tabId) sendDebugLog(ctx.tabId, ctx.messageId, text, level);
  };
  if (_alassReady && _alassApi) return _alassApi;
  try {
    // Load wrapper (defines self.SubMakerAlass)
    if (!self.SubMakerAlass) {
      if (_alassPreloadError) {
        logToPage(`alass preload failed: ${_alassPreloadError?.message || _alassPreloadError}`, 'error');
        return null;
      }
      const alassUrl = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/alass-wasm.js') : 'assets/lib/alass-wasm.js';
      if (typeof importScripts !== 'function') {
        console.warn('[Background] importScripts unavailable for alass loader');
        logToPage('alass loader unavailable in this environment', 'error');
        return null;
      }
      try {
        await importScriptSafe(alassUrl, 'alass-wasm.js');
      } catch (loadErr) {
        console.warn('[Background] Failed to load alass-wasm wrapper:', loadErr?.message);
        logToPage(`alass wrapper load failed: ${loadErr?.message || loadErr}`, 'error');
        return null;
      }
    }
    if (!self.SubMakerAlass || !self.SubMakerAlass.init) {
      console.warn('[Background] alass-wasm wrapper not found');
      logToPage('alass-wasm wrapper not found after load', 'error');
      return null;
    }
    const wasmPath = chrome?.runtime?.getURL ? chrome.runtime.getURL('assets/lib/alass.wasm') : 'assets/lib/alass.wasm';
    _alassApi = await self.SubMakerAlass.init({ wasmPath });
    _alassReady = true;
    console.log('[Background] alass-wasm initialized', { ready: !!_alassApi, hasAlignAudio: !!_alassApi?.alignAudio });
    return _alassApi;
  } catch (e) {
    console.warn('[Background] Failed to load alass-wasm:', e?.message, e?.stack);
    logToPage(`alass-wasm init failed: ${e?.message || e}`, 'error');
    return null;
  }
}

// ---------- Helpers: popup statistics ----------
async function incStat(key, delta) {
  const cur = await chrome.storage.local.get([key]);
  const val = Math.max(0, (cur[key] || 0) + delta);
  await chrome.storage.local.set({ [key]: val });
}

console.log('[SubMaker xSync Background] Ready for sync requests');

// Expose lightweight status/handler to bootstrap
self.__xsyncStatus = () => ({
  active: (typeof activeSyncJobs !== 'undefined' && activeSyncJobs?.size) ? activeSyncJobs.size : 0,
  extracting: (typeof activeExtractJobs !== 'undefined' && activeExtractJobs?.size) ? activeExtractJobs.size : 0
});
self.__xsyncHandleMessage = __xsyncHandleMessage;
