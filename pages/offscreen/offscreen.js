// Offscreen document runner for FFmpeg demux (embedded subtitles)
// Runs in a DOM context so FFmpeg can spawn Workers (not allowed in MV3 service worker)

function sendOffscreenLog(text, level = 'info', messageId) {
  if (!shouldEmitOffscreenLog(level)) return;
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
let _ffmpegFactory = null;
let _ffmpegMode = 'unknown';
let _bareFfmpegModule = null;
let _workerLooksStub = null;
let _debugEnabled = true; // default to verbose so extraction failures surface without manual toggles
const _chunkedBuffers = new Map();
const CHUNK_BUFFER_TTL_MS = 5 * 60 * 1000;
const OUTGOING_CHUNK_BYTES = 512 * 1024;
const OUTGOING_CHUNK_THRESHOLD = 2.5 * 1024 * 1024; // approx 2.5MB before chunking

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
  if (size === (Math.pow(2, 7 * sizeInfo.length) - 1)) {
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
    let v = 0;
    for (let i = start; i < end; i++) v = (v << 8) | u8Arr[i];
    return v >>> 0;
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

const formatExtractedName = (index, ext = 'srt', variant = '') => {
  const num = String(index).padStart(2, '0');
  const prefix = variant ? `${EXTRACTED_PREFIX}_${variant}_` : `${EXTRACTED_PREFIX}_`;
  return `${prefix}${num}.${ext}`;
};

function normalizeExtractedTracks(tracks) {
  if (!Array.isArray(tracks)) return [];
  return tracks.map((t, idx) => {
    const ext = (t && (t.binary || t.codec === 'copy' || (t.mime && String(t.mime).toLowerCase().includes('matroska'))))
      ? 'mkv'
      : 'srt';
    const label = formatExtractedName(idx + 1, ext);
    return {
      ...t,
      id: String(idx + 1),
      label,
      originalLabel: t?.label
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

async function workerScriptLooksStub(url) {
  if (_workerLooksStub !== null) return _workerLooksStub;
  if (!url) return false;
  try {
    const res = await fetch(url, { cache: 'no-store' });
    if (!res.ok) return false;
    const text = await res.text();
    _workerLooksStub = text.length < 1024 && /placeholder/i.test(text);
    if (_workerLooksStub) {
      sendOffscreenLog('Detected placeholder FFmpeg worker; will prefer bare core fallback', 'warn');
    }
    return _workerLooksStub;
  } catch (_) {
    _workerLooksStub = false;
    return false;
  }
}

async function ensureFfmpegFactory() {
  if (_ffmpegFactory) return _ffmpegFactory;

  const wireUpWasmShim = () => {
    if (!self.createFFmpeg && self.FFmpegWASM?.FFmpeg) {
      self.FFmpeg = self.FFmpegWASM;
      self.createFFmpeg = (opts = {}) => new self.FFmpegWASM.FFmpeg(opts);
    }
    return self.createFFmpeg || (self.FFmpeg && self.FFmpeg.createFFmpeg);
  };

  let factory = wireUpWasmShim();
  const tryLoad = async (url, label) => {
    if (!url) return;
    try {
      sendOffscreenLog(`Loading FFmpeg loader: ${label}`, 'info');
      await loadScriptTag(url, label);
      factory = wireUpWasmShim();
      if (factory) {
        console.log(`[Offscreen] FFmpeg loader ready via ${label}`);
        sendOffscreenLog(`FFmpeg loader ready via ${label}`, 'info');
      }
    } catch (err) {
      console.warn(`[Offscreen] Failed to load FFmpeg loader from ${label}:`, err?.message || err);
      sendOffscreenLog(`FFmpeg loader failed via ${label}: ${err?.message || err}`, 'warn');
    }
  };

  const runtimeUrl = chrome.runtime.getURL('assets/lib/ffmpeg.js');
  await tryLoad(runtimeUrl, 'bundled ffmpeg.js');
  if (!factory) {
    await tryLoad('assets/lib/ffmpeg.js', 'fallback ffmpeg.js');
  }
  if (!factory) {
    throw new Error('FFmpeg loader unavailable in offscreen context.');
  }
  _ffmpegFactory = factory;
  return factory;
}

async function loadBareFfmpegCore(messageId) {
  if (_bareFfmpegModule && _ffmpegInstance) return _ffmpegInstance;
  const coreUrl = chrome.runtime.getURL('assets/lib/ffmpeg-core.js');
  sendOffscreenLog('Falling back to direct FFmpeg core (no worker)...', 'warn', messageId);
  await loadScriptTag(coreUrl, 'ffmpeg-core.js', messageId);
  if (typeof self.createFFmpegCore !== 'function') {
    throw new Error('createFFmpegCore not found after loading core script');
  }
  const module = await withTimeout(self.createFFmpegCore({
    locateFile: (path) => {
      if (path.endsWith('.wasm')) return chrome.runtime.getURL('assets/lib/ffmpeg-core.wasm');
      if (path.endsWith('.worker.js')) return chrome.runtime.getURL('assets/lib/ffmpeg-core.worker.js');
      return chrome.runtime.getURL(`assets/lib/${path}`);
    },
    print: (msg) => sendOffscreenLog(msg, 'info', messageId),
    printErr: (msg) => sendOffscreenLog(msg, 'warn', messageId)
  }), 45000, 'Bare FFmpeg core load timed out');

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

  const sabAvailable = typeof SharedArrayBuffer !== 'undefined';
  const coi = self.crossOriginIsolated;
  sendOffscreenLog(`FFmpeg loading... (SAB:${sabAvailable ? 'yes' : 'no'}, COI:${coi === false ? 'no' : 'yes'})`, 'info', messageId);
  const createFFmpeg = await ensureFfmpegFactory();

  // Force bare core to skip worker-based variants that hang in COI/SAB edge cases (faster and more reliable here).
  const forceBareCore = true;
  const buildPaths = (mt) => ({
    corePath: chrome.runtime.getURL(mt ? 'assets/lib/ffmpeg-core-mt.js' : 'assets/lib/ffmpeg-core.js'),
    wasmPath: chrome.runtime.getURL(mt ? 'assets/lib/ffmpeg-core-mt.wasm' : 'assets/lib/ffmpeg-core.wasm'),
    workerPath: mt ? chrome.runtime.getURL('assets/lib/ffmpeg-core-mt.worker.js') : null,
    mainName: mt ? 'ffmpeg-core-mt' : 'ffmpeg-core'
  });

  const preferBare = forceBareCore || await workerScriptLooksStub(buildPaths(false).workerPath);

  if (preferBare) {
    try {
      const bareReason = forceBareCore
        ? 'Forcing bare FFmpeg core (single-thread, no worker)'
        : 'Using bare FFmpeg core because worker script is a placeholder';
      sendOffscreenLog(bareReason, 'warn', messageId);
      _ffmpegInstance = await loadBareFfmpegCore(messageId);
      return _ffmpegInstance;
    } catch (err) {
      sendOffscreenLog(`Bare core quick path failed; retrying standard loader (${err?.message || err})`, 'warn', messageId);
    }
  }

  const loadWithMode = async (mt) => {
    const paths = buildPaths(mt);
    sendOffscreenLog(`Loading FFmpeg core (${mt ? 'multi-thread' : 'single-thread'})...`, 'info', messageId);

    const toBlobUrl = async (url, type) => {
      const res = await fetch(url, { cache: 'no-store' });
      if (!res.ok) throw new Error(`Fetch failed for ${url} (${res.status})`);
      const buf = await res.arrayBuffer();
      return URL.createObjectURL(new Blob([buf], { type }));
    };

    let corePath = paths.corePath;
    let wasmPath = paths.wasmPath;
    let workerPath = paths.workerPath;

    // For mt, load via Blob URLs so the worker inherits the offscreen document's COI/SAB context.
    if (mt) {
      corePath = await toBlobUrl(paths.corePath, 'application/javascript');
      wasmPath = await toBlobUrl(paths.wasmPath, 'application/wasm');
      workerPath = paths.workerPath ? await toBlobUrl(paths.workerPath, 'application/javascript') : null;
    }

    const ffmpeg = createFFmpeg({
      log: true,
      logger: ({ type, message }) => {
        const level = type === 'fferr' ? 'warn' : 'info';
        sendOffscreenLog(message, level, messageId);
      },
      corePath,
      wasmPath,
      ...(workerPath ? { workerPath } : {}),
      mainName: paths.mainName
    });
    const loadTimeout = mt ? 120000 : 45000;
    await withTimeout(ffmpeg.load(), loadTimeout, `FFmpeg ${mt ? 'multi-thread' : 'single-thread'} load timed out`);
    _ffmpegMode = mt ? 'multi-thread' : 'single-thread';
    sendOffscreenLog(`FFmpeg load finished (${_ffmpegMode})`, 'info', messageId);
    return ffmpeg;
  };

  const preferMt = sabAvailable;
  let lastErr = null;
  const modes = preferMt ? [true, false] : [false];
  if (preferMt && coi === false) {
    sendOffscreenLog('Cross-origin isolation disabled; will attempt multi-thread FFmpeg and fall back if blocked', 'warn', messageId);
  }
  for (const mt of modes) {
    try {
      _ffmpegInstance = await loadWithMode(mt);
      return _ffmpegInstance;
    } catch (err) {
      lastErr = err;
      const level = mt && modes.length > 1 ? 'warn' : 'error';
      sendOffscreenLog(`FFmpeg ${mt ? 'multi-thread' : 'single-thread'} load failed: ${err?.message || err}`, level, messageId);
      console.warn('[Offscreen] FFmpeg load failed:', err);
    }
  }

  try {
    sendOffscreenLog('Attempting bare FFmpeg core fallback after worker load failure...', 'warn', messageId);
    return await loadBareFfmpegCore(messageId);
  } catch (fallbackErr) {
    console.warn('[Offscreen] Bare FFmpeg fallback failed:', fallbackErr);
    sendOffscreenLog(`Bare FFmpeg core fallback failed: ${fallbackErr?.message || fallbackErr}`, 'error', messageId);
    throw lastErr || fallbackErr || new Error('FFmpeg load failed in offscreen page.');
  }
}

async function decodeAudioWindows(windows, mode, messageId, opts = {}) {
  const ffmpeg = await getFFmpeg(messageId);
  const results = [];
  const sharedBuffer = windows.length > 1 && windows.every(w => w.buffer === windows[0].buffer);
  let sharedInputName = null;
  const audioStreamIndex = Number.isInteger(opts.audioStreamIndex) ? opts.audioStreamIndex : 0;

  if (sharedBuffer) {
    sharedInputName = 'shared_input.bin';
    ffmpeg.FS('writeFile', sharedInputName, windows[0].buffer instanceof Uint8Array ? windows[0].buffer : new Uint8Array(windows[0].buffer));
  }

  for (let i = 0; i < windows.length; i++) {
    const win = windows[i];
    const inputName = sharedInputName || `win_${i}.bin`;
    const outputName = `win_${i}.wav`;
    const buffer = win.buffer instanceof Uint8Array ? win.buffer : new Uint8Array(win.buffer);
    ffmpeg.FS('writeFile', inputName, buffer);
    const buildArgs = () => {
      const base = ['-i', inputName, '-vn'];
      if (Number.isInteger(audioStreamIndex) && audioStreamIndex >= 0) {
        base.push('-map', `0:a:${audioStreamIndex}`);
      }
      base.push('-acodec', 'pcm_s16le', '-ar', '16000');
      // Avoid mixing bilingual dual-mono tracks; explicitly keep the left channel only.
      base.push('-af', 'pan=mono|c0=c0', '-ac', '1');
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
      await ffmpeg.run(...buildArgs());
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
    } finally {
      try { ffmpeg.FS('unlink', outputName); } catch (_) { /* ignore */ }
      if (!sharedInputName) {
        try { ffmpeg.FS('unlink', inputName); } catch (_) { /* ignore */ }
      }
    }
  }

  if (sharedInputName) {
    try { ffmpeg.FS('unlink', sharedInputName); } catch (_) { /* ignore */ }
  }

  if (!results.length) {
    throw new Error('FFmpeg could not decode any audio window');
  }

  return results;
}

async function demuxSubtitles(buffer, messageId) {
  const byteLength = typeof buffer?.byteLength === 'number'
    ? buffer.byteLength
    : (typeof buffer?.size === 'number' ? buffer.size : 0);
  const sizeMb = Math.round(((byteLength || 0) / (1024 * 1024)) * 10) / 10;
  sendOffscreenLog(`Starting demux (buffer ~${sizeMb} MB)`, 'info', messageId);
  if (!buffer || !byteLength) {
    sendOffscreenLog('Received empty buffer for demux; aborting.', 'error', messageId);
    throw new Error('Empty buffer received for demux.');
  }
  const view = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
  const ffmpeg = await getFFmpeg(messageId);
  if (ffmpeg?.setLogger) {
    ffmpeg.setLogger(({ type, message }) => {
      const level = type === 'fferr' ? 'warn' : 'info';
      sendOffscreenLog(message, level, messageId);
    });
  }
  if (ffmpeg?.setLogLevel) {
    ffmpeg.setLogLevel('debug');
  }
  const inputName = 'embedded_input.bin';
  sendOffscreenLog('Writing input buffer to FFmpeg FS...', 'info', messageId);
  ffmpeg.FS('writeFile', inputName, view);
  try {
    sendOffscreenLog('Running FFmpeg to extract subtitle streams...', 'info', messageId);
    const srtSeqPattern = `${EXTRACTED_PREFIX}_%02d.srt`;
    // Try generous probe and srt conversion first
    const baseArgs = [
      '-y',
      '-analyzeduration', '60M',
      '-probesize', '60M',
      '-i', inputName,
      '-map', '0:s?',
      '-c:s', 'srt',
      '-start_number', '1',
      srtSeqPattern
    ];
    try {
      await ffmpeg.run(...baseArgs);
    } catch (primaryErr) {
      sendOffscreenLog(`Primary demux attempt failed (${primaryErr?.message || primaryErr}); retrying with stream copy`, 'warn', messageId);
      // Fallback: stream copy to keep bitmap/ass subs intact
      await ffmpeg.run(
        '-y',
        '-analyzeduration', '60M',
        '-probesize', '60M',
        '-i', inputName,
        '-map', '0:s?',
        '-c:s', 'copy',
        '-f', 'matroska',
        'embedded_subs.mkv'
      );
    }
  } catch (err) {
    console.error('[Offscreen] FFmpeg demux failed:', err);
    sendOffscreenLog(`FFmpeg demux failed: ${err?.message || err}`, 'error', messageId);
    throw new Error('FFmpeg could not extract subtitle tracks (no subtitle streams or FFmpeg unavailable).');
  }

  // Gather initial SRT outputs
  let files = ffmpeg.FS('readdir', '/')
    .filter(f => EXTRACTED_SRT_PATTERN.test(f))
    .sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));

  const mkvExists = ffmpeg.FS('readdir', '/').includes('embedded_subs.mkv');
  const copiedTracks = [];
  const convertedSrts = [];

  // Always attempt to split every subtitle stream into its own MKV copy to preserve bitmap/ass tracks.
  if (mkvExists) {
    sendOffscreenLog('Inspecting MKV copy to preserve all subtitle streams...', 'info', messageId);
    try {
      const maxTracks = 32;
      for (let i = 0; i < maxTracks; i++) {
        const trackNumber = i + 1;
        const outName = formatExtractedName(trackNumber, 'mkv');
        try {
          await ffmpeg.run(
            '-y',
            '-analyzeduration', '60M',
            '-probesize', '60M',
            '-i', 'embedded_subs.mkv',
            '-map', `0:s:${i}`,
            '-c:s', 'copy',
            outName
          );
          const data = ffmpeg.FS('readFile', outName);
          if (data?.byteLength > 0) {
            copiedTracks.push(outName);
          } else {
            try { ffmpeg.FS('unlink', outName); } catch (_) { }
            break; // no more subtitle streams
          }
        } catch (innerErr) {
          try { ffmpeg.FS('unlink', outName); } catch (_) { }
          break; // stop at first missing stream
        }
      }
      sendOffscreenLog(`Remuxed ${copiedTracks.length} subtitle stream(s) to MKV copy (kept internal)`, 'info', messageId);
    } catch (probeErr) {
      sendOffscreenLog(`Failed to remux MKV copy: ${probeErr?.message || probeErr}`, 'error', messageId);
    }
  }

  // Try to convert each copied track to SRT if we don't already have an SRT for that index
  if (copiedTracks.length) {
    const existingIds = new Set(files.map(f => parseInt((f.match(/extracted_sub_(\d+)\.srt$/i) || [])[1] || '-1', 10)));
    for (const copyName of copiedTracks) {
      const idxMatch = copyName.match(/extracted_sub_(\d+)\.mkv$/i);
      const trackIdx = idxMatch ? parseInt(idxMatch[1], 10) : null;
      if (trackIdx !== null && existingIds.has(trackIdx)) {
        continue; // already have text output for this track
      }
      const srtName = copyName.replace(/\.mkv$/i, '.srt');
      try {
        await ffmpeg.run(
          '-y',
          '-analyzeduration', '60M',
          '-probesize', '60M',
          '-i', copyName,
          '-map', '0:s:0',
          '-c:s', 'srt',
          srtName
        );
        const data = ffmpeg.FS('readFile', srtName);
        if (data?.byteLength) {
          convertedSrts.push(srtName);
        } else {
          try { ffmpeg.FS('unlink', srtName); } catch (_) { }
        }
      } catch (convErr) {
        try { ffmpeg.FS('unlink', srtName); } catch (_) { }
        sendOffscreenLog(`Failed to convert ${copyName} to SRT: ${convErr?.message || convErr}`, 'warn', messageId);
      }
    }
    if (convertedSrts.length) {
      files = [...files, ...convertedSrts].sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
    }
  }
  const skippedCopies = copiedTracks.length;

  if (!files.length) {
    if (copiedTracks.length) {
      let ocrTracks = [];
      try {
        ocrTracks = await runPaddleOcrOnCopiedTracks(ffmpeg, copiedTracks, messageId);
        if (ocrTracks.length) {
          sendOffscreenLog(`OCR (PaddleOCR) extracted ${ocrTracks.length} subtitle track(s) from image-based streams`, 'info', messageId);
          return normalizeExtractedTracks(ocrTracks);
        }
      } catch (ocrErr) {
        sendOffscreenLog(`OCR failed: ${ocrErr?.message || ocrErr}`, 'error', messageId);
      }
      // Fallback to Tesseract if Paddle fails or produces no text
      try {
        ocrTracks = await runTesseractOcrOnCopiedTracks(ffmpeg, copiedTracks, messageId);
        if (ocrTracks.length) {
          sendOffscreenLog(`OCR (Tesseract) extracted ${ocrTracks.length} subtitle track(s) from image-based streams`, 'info', messageId);
          return normalizeExtractedTracks(ocrTracks);
        }
      } catch (tessErr) {
        sendOffscreenLog(`Tesseract OCR failed: ${tessErr?.message || tessErr}`, 'error', messageId);
      }
      sendOffscreenLog('Detected subtitle streams (likely image/bitmap, e.g., PGS/VobSub) that cannot be converted to SRT. OCR was attempted but no text was produced.', 'error', messageId);
      throw new Error('Image-based subtitle streams require OCR; no text could be produced.');
    }
    sendOffscreenLog('FFmpeg completed but no subtitle streams were found.', 'warn', messageId);
    throw new Error('No subtitle streams found in media.');
  }
  sendOffscreenLog(`FFmpeg demux produced ${files.length} track file(s)`, 'info', messageId);

  const decoder = new TextDecoder();
  let tracks = files.map((file) => {
    const data = ffmpeg.FS('readFile', file);
    const matchSrt = file.match(/extracted_sub_(\d+)\.srt$/i);
    const matchFix = file.match(/extracted_sub_fix_(\d+)\.srt$/i);
    const matchCopy = file.match(/extracted_sub_(\d+)\.mkv$/i);
    const trackId = matchSrt
      ? String(parseInt(matchSrt[1], 10))
      : matchFix
        ? String(parseInt(matchFix[1], 10))
        : matchCopy
          ? String(parseInt(matchCopy[1], 10))
          : file.replace(/\..*$/, '');
    const isBinary = /\.mkv$/i.test(file);
    const source = matchCopy ? 'copy' : 'srt';
    const base = {
      id: trackId,
      label: file,
      language: 'und',
      codec: isBinary ? 'copy' : 'srt',
      source
    };

    if (isBinary) {
      return {
        ...base,
        binary: true,
        mime: 'video/x-matroska',
        byteLength: data.byteLength,
        contentBase64: uint8ToBase64(data)
      };
    }

    return {
      ...base,
      binary: false,
      byteLength: data.byteLength,
      content: decoder.decode(data)
    };
  });

  // If timelines look broken (e.g., all cues share the same timestamp), retry with a PTS-normalized conversion.
  const timelineStatus = analyzeCueTimelines(tracks);
  if (timelineStatus.flatCueStarts || timelineStatus.nonMonotonicCues) {
    sendOffscreenLog(
      `Detected ${timelineStatus.flatCueStarts ? 'flat' : 'non-monotonic'} cue timestamps; retrying with PTS normalization...`,
      'warn',
      messageId
    );
    try {
      // Remove prior SRT outputs to avoid mixing old/new
      for (const f of ffmpeg.FS('readdir', '/')) {
        if (/^extracted_sub_(fix_)?\d+\.srt$/i.test(f)) {
          try { ffmpeg.FS('unlink', f); } catch (_) { }
        }
      }
      const fixPattern = `${EXTRACTED_PREFIX}_fix_%02d.srt`;
      await ffmpeg.run(
        '-y',
        '-fflags', '+genpts',
        '-copyts',
        '-start_at_zero',
        '-analyzeduration', '60M',
        '-probesize', '60M',
        '-i', inputName,
        '-map', '0:s?',
        '-c:s', 'srt',
        '-fix_sub_duration',
        '-avoid_negative_ts', 'make_zero',
        '-max_interleave_delta', '0',
        '-muxpreload', '0',
        '-muxdelay', '0',
        '-start_number', '1',
        fixPattern
      );
      const fixedFiles = ffmpeg.FS('readdir', '/')
        .filter(f => EXTRACTED_FIX_PATTERN.test(f))
        .sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
      if (fixedFiles.length) {
        const fixedTracks = fixedFiles.map((file) => {
          const data = ffmpeg.FS('readFile', file);
          const trackId = String(parseInt((file.match(/extracted_sub_fix_(\d+)\.srt$/i) || [])[1] || '0', 10));
          return {
            id: trackId,
            label: file,
            language: 'und',
            codec: 'srt',
            binary: false,
            byteLength: data.byteLength,
            content: decoder.decode(data)
          };
        });
        const fixedStatus = analyzeCueTimelines(fixedTracks);
        if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
          sendOffscreenLog('PTS-normalized retry improved timelines; using fixed tracks.', 'info', messageId);
          tracks = fixedTracks;
        } else {
          sendOffscreenLog('PTS-normalized retry still looks broken; keeping original tracks.', 'warn', messageId);
        }
      } else {
        sendOffscreenLog('PTS-normalized retry produced no SRT outputs.', 'warn', messageId);
      }
    } catch (normErr) {
      sendOffscreenLog(`PTS-normalized retry failed: ${normErr?.message || normErr}`, 'error', messageId);
    }
  }

  // If still broken, try per-stream remux + setpts-style reset before SRT conversion.
  const postNormStatus = analyzeCueTimelines(tracks);
  if (postNormStatus.flatCueStarts || postNormStatus.nonMonotonicCues) {
    sendOffscreenLog('Timelines still broken after PTS normalization; trying per-stream remux...', 'warn', messageId);
    try {
      const remuxed = [];
      const maxStreams = 32;
      for (let i = 0; i < maxStreams; i++) {
        const outName = `remux_sub_${String(i).padStart(2, '0')}.mkv`;
        try {
          await ffmpeg.run(
            '-y',
            '-analyzeduration', '60M',
            '-probesize', '60M',
            '-copyts',
            '-avoid_negative_ts', 'make_zero',
            '-i', inputName,
            '-map', `0:s:${i}`,
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
        const srtName = remuxName.replace(/\.mkv$/i, '.srt').replace(/^remux_sub_/, 'extracted_sub_fix_');
        try {
          await ffmpeg.run(
            '-y',
            '-fflags', '+genpts',
            '-copyts',
            '-start_at_zero',
            '-avoid_negative_ts', 'make_zero',
            '-analyzeduration', '60M',
            '-probesize', '60M',
            '-i', remuxName,
            '-map', '0:s:0',
            '-c:s', 'srt',
            '-fix_sub_duration',
            srtName
          );
          const data = ffmpeg.FS('readFile', srtName);
          if (data?.byteLength) {
            fixedTracks.push({
              id: String(parseInt((srtName.match(/extracted_sub_fix_(\d+)\.srt$/i) || [])[1] || fixedTracks.length, 10)),
              label: srtName,
              language: 'und',
              codec: 'srt',
              binary: false,
              byteLength: data.byteLength,
              content: decoder.decode(data)
            });
          }
        } catch (convErr) {
          sendOffscreenLog(`Remux conversion failed for ${remuxName}: ${convErr?.message || convErr}`, 'warn', messageId);
        }
      }

      if (fixedTracks.length) {
        const fixedStatus = analyzeCueTimelines(fixedTracks);
        if (!(fixedStatus.flatCueStarts || fixedStatus.nonMonotonicCues)) {
          sendOffscreenLog('Per-stream remux fixed timelines; using remuxed tracks.', 'info', messageId);
          tracks = fixedTracks;
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
  const headerLangs = collectSubtitleLanguagesFromHeader(buffer);
  if (headerLangs.length) {
    tracks = applyHeaderLanguagesToTracks(tracks, headerLangs);
  }
  tracks = applyContentLanguageGuesses(tracks);

  // Apply consistent naming/numbering for all outputs
  tracks = normalizeExtractedTracks(tracks);

  // Best-effort cleanup to avoid FS bloat across runs
  try {
    for (const file of files) ffmpeg.FS('unlink', file);
    ffmpeg.FS('unlink', inputName);
    for (const copyName of copiedTracks) {
      try { ffmpeg.FS('unlink', copyName); } catch (_) { /* ignore */ }
    }
    if (mkvExists) {
      try { ffmpeg.FS('unlink', 'embedded_subs.mkv'); } catch (_) { }
    }
  } catch (_) { /* ignore */ }
  const copyNote = skippedCopies ? `; omitted ${skippedCopies} MKV copy track(s) from output` : '';
  sendOffscreenLog(`Demux finished and cleaned up (${tracks.length} track(s)${copyNote})`, 'info', messageId);

  return tracks;
}

function withTimeout(promise, ms, label) {
  let timer;
  const timeout = new Promise((_, reject) => {
    timer = setTimeout(() => reject(new Error(label || `Operation timed out after ${ms}ms`)), ms);
  });
  return Promise.race([promise.finally(() => clearTimeout(timer)), timeout]);
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

    const timeout = setTimeout(() => {
      if (!cleanupDone) {
        cleanup();
        const msg = tracks.length > 0
          ? `Extraction timed out but found ${tracks.length} track(s)`
          : 'Extraction timed out - no tracks found';
        sendOffscreenLog(msg, tracks.length > 0 ? 'warn' : 'error', messageId);
        if (tracks.length > 0) {
          resolve(tracks);
        } else {
          reject(new Error('Video subtitle extraction timed out'));
        }
      }
    }, 120000);

    function cleanup() {
      if (cleanupDone) return;
      cleanupDone = true;
      clearTimeout(timeout);
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
        const trackObj = video.textTracks[trackIndex];
        if (!trackObj) {
          sendOffscreenLog(`Track ${trackIndex} not accessible`, 'warn', messageId);
          resolveTrack(null);
          return;
        }

        const handleCueChange = () => {
          try {
            const cues = Array.from(trackObj.cues || []);
            if (cues.length === 0) {
              sendOffscreenLog(`Track ${trackIndex} loaded but has no cues`, 'warn', messageId);
              resolveTrack(null);
              return;
            }

            const content = convertVttCuesToSrt(cues);
            const sizeKb = Math.round((content.length / 1024) * 10) / 10;
            sendOffscreenLog(`Track ${trackIndex}: extracted ${cues.length} cues (${sizeKb} KB)`, 'info', messageId);

            const langFromTrack = normalizeTrackLanguageCode(track.srclang || trackObj.language);
            const langGuess = detectLanguageFromLabel(track.label || trackObj.label || '');
            const langFromContent = detectLanguageFromContent(content);
            const language = langFromTrack || langFromContent || langGuess || 'und';

            resolveTrack({
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
            resolveTrack(null);
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
          setTimeout(handleCueChange, 100);
        } else {
          // Set a fallback timeout for this specific track
          setTimeout(() => {
            if (trackObj.cues && trackObj.cues.length > 0) {
              handleCueChange();
            } else {
              sendOffscreenLog(`Track ${trackIndex} timed out without loading cues`, 'warn', messageId);
              trackObj.removeEventListener('cuechange', handleCueChange);
              resolveTrack(null);
            }
          }, 30000);
        }
      });
    }

    video.addEventListener('loadedmetadata', async () => {
      if (metadataLoaded) return;
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
        cleanup();
        reject(new Error('No embedded subtitle tracks found in video'));
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
          const validTracks = results.filter(t => t !== null);

          if (validTracks.length === 0) {
            cleanup();
            reject(new Error('Failed to extract any subtitle content from tracks'));
            return;
          }

          sendOffscreenLog(`Successfully extracted ${validTracks.length}/${tracksExpected} track(s)`, 'info', messageId);
          const namedTracks = normalizeExtractedTracks(validTracks);
          cleanup();
          resolve(namedTracks);
        } catch (err) {
          cleanup();
          reject(err);
        }
      });

    video.addEventListener('error', (e) => {
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
      cleanup();
      reject(new Error(msg));
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

  if (message?.type === 'OFFSCREEN_FFMPEG_EXTRACT') {
    const requestId = message?.messageId;
    console.log('[Offscreen] Handling OFFSCREEN_FFMPEG_EXTRACT', {
      requestId,
      hasBuffer: !!message?.buffer,
      transferId: message?.transferId
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
        const transferId = message?.transferId || (incomingBuffer && incomingBuffer.transferId);

        if (message?.transferMethod === 'idb' && transferId) {
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
        const sizeMb = Math.round(((incomingBuffer?.byteLength || incomingBuffer?.size || 0) / (1024 * 1024)) * 10) / 10;
        sendOffscreenLog(`Received demux request (job ${requestId || 'n/a'}), size: ${sizeMb} MB`, 'info', requestId);
        sendOffscreenLog(`Offscreen env: SAB=${typeof SharedArrayBuffer !== 'undefined' ? 'yes' : 'no'}, COI=${self.crossOriginIsolated === false ? 'no' : 'yes'}`, 'info', requestId);
        const tracks = await withTimeout(
          demuxSubtitles(incomingBuffer, requestId),
          90000,
          `FFmpeg demux timed out in offscreen page${requestId ? ` (job ${requestId})` : ''}`
        );
        const prepared = await prepareTracksForSend(tracks, requestId);
        respond({ success: true, tracks: prepared.tracks, chunked: prepared.chunked });
      } catch (err) {
        console.error('[Offscreen] Extraction failed:', err);
        sendOffscreenLog(`Demux failed: ${err?.message || err}`, 'error', requestId);
        respond({ success: false, error: err?.message || String(err) });
      }
    })();
    return true; // async
  }

  if (message?.type === 'OFFSCREEN_FFMPEG_DECODE') {
    const requestId = message?.messageId;
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

        // Some decode requests reuse the same transferId across multiple windows to avoid
        // duplicating large buffers. Cache each loaded buffer so we only consume IDB/chunks once.
        const bufferCache = new Map();

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

          if (transferId) {
            buf = await loadFromTransfer(transferId, transferMethod);
          } else if (buf && buf.transferId) {
            buf = await loadFromTransfer(buf.transferId, buf.transferMethod || transferMethod);
          }
          if (!buf) {
            throw new Error(`Missing buffer for window ${idx + 1}`);
          }
          windows.push({
            buffer: buf instanceof Uint8Array ? buf : new Uint8Array(buf),
            startSec: w?.startSec,
            durSec: w?.durSec,
            seekToSec: w?.seekToSec
          });
        }

        const decoded = await withTimeout(
          decodeAudioWindows(windows, 'single', requestId, { audioStreamIndex: message?.audioStreamIndex }),
          180000,
          `FFmpeg audio decode timed out${requestId ? ` (job ${requestId})` : ''}`
        );
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

        respond({ success: true, audioWindows: prepared, chunked: true });
      } catch (err) {
        console.error('[Offscreen] Audio decode failed:', err);
        sendOffscreenLog(`Audio decode failed: ${err?.message || err}`, 'error', requestId);
        respond({ success: false, error: err?.message || String(err) });
      }
    })();
    return true;
  }

  if (message?.type === 'OFFSCREEN_VIDEO_EXTRACT') {
    const requestId = message?.messageId;
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

        sendOffscreenLog(`Starting video-based extraction for ${streamUrl.substring(0, 60)}...`, 'info', requestId);

        const tracks = await withTimeout(
          extractSubtitlesViaVideo(streamUrl, mode, requestId),
          180000,
          `Video extraction timed out${requestId ? ` (job ${requestId})` : ''}`
        );

        const prepared = await prepareTracksForSend(tracks, requestId);
        respond({ success: true, tracks: prepared.tracks, chunked: prepared.chunked });
      } catch (err) {
        console.error('[Offscreen] Video extraction failed:', err);
        sendOffscreenLog(`Video extraction failed: ${err?.message || err}`, 'error', requestId);
        respond({ success: false, error: err?.message || String(err) });
      }
    })();
    return true;
  }
});

console.log('[Offscreen] Ready for FFmpeg demux and video extraction requests');
