/**
 * ffsubsync-wasm loader wrapper for SubMaker xSync.
 * Expects artifacts produced by `scripts/build-ffsubsync-wasm.sh`:
 *   - ffsubsync_wasm.js (wasm-bindgen glue, no-modules)
 *   - ffsubsync_wasm_bg.wasm
 *
 * This wrapper is CSP/MV3-safe: it relies on importScripts/fetch, never eval.
 */
(function (global) {
  const state = {
    loading: null,
    api: null,
    bindgen: null,
  };

  async function loadGlueAndWasm({ wasmPath }) {
    if (state.api) return state.api;
    if (state.loading) return state.loading;

    state.loading = (async () => {
      const wasmUrl = wasmPath ||
        (global.chrome?.runtime?.getURL
          ? chrome.runtime.getURL('assets/lib/ffsubsync_wasm_bg.wasm')
          : 'ffsubsync_wasm_bg.wasm');

      let bindgen = state.bindgen || global.__SubMakerFfsubsyncBindgen || null;
      if (typeof bindgen !== 'function') {
        const glueUrl = global.chrome?.runtime?.getURL
          ? chrome.runtime.getURL('assets/lib/ffsubsync_wasm.js')
          : 'ffsubsync_wasm.js';
        if (typeof importScripts !== 'function') {
          throw new Error('importScripts unavailable; cannot load ffsubsync-wasm glue in this context');
        }
        const previous = global.wasm_bindgen;
        try {
          importScripts(glueUrl);
        } catch (e) {
          throw new Error(`Failed to import ffsubsync glue: ${e?.message || e}`);
        }
        bindgen = global.wasm_bindgen;
        if (typeof bindgen !== 'function') {
          throw new Error('wasm_bindgen not found after loading ffsubsync_wasm.js (build artifacts missing?)');
        }
        state.bindgen = bindgen;
        global.wasm_bindgen = previous;
      }

      const response = await fetch(wasmUrl);
      if (!response.ok) {
        throw new Error(`Failed to fetch ffsubsync wasm (${wasmUrl}): ${response.status}`);
      }
      const wasmBytes = await response.arrayBuffer();

      await bindgen(wasmBytes);
      if (typeof bindgen.align_wav !== 'function') {
        throw new Error('ffsubsync wasm failed to initialize (align_wav missing)');
      }
      state.api = bindgen;
      return state.api;
    })().catch((e) => {
      state.loading = null;
      throw e;
    });

    return state.loading;
  }

  async function align({ audio, srtText, options = {}, onProgress }) {
    if (!audio) throw new Error('audio is required for ffsubsync');
    if (!srtText) throw new Error('srtText is required for ffsubsync');
    onProgress?.(5, 'Loading ffsubsync-wasm...');
    const api = await loadGlueAndWasm({ wasmPath: options.wasmPath });
    onProgress?.(20, 'Normalizing audio...');

    // Callers are expected to provide 16 kHz mono PCM i16 data or a WAV blob/ArrayBuffer.
    let wavBytes;
    if (audio instanceof ArrayBuffer) {
      wavBytes = new Uint8Array(audio);
    } else if (ArrayBuffer.isView(audio)) {
      wavBytes = new Uint8Array(audio.buffer, audio.byteOffset, audio.byteLength);
    } else if (typeof Blob !== 'undefined' && audio instanceof Blob) {
      wavBytes = new Uint8Array(await audio.arrayBuffer());
    } else {
      throw new Error('Unsupported audio input for ffsubsync; provide Blob, ArrayBuffer, or TypedArray');
    }

    const opts = {
      frame_ms: options.frameMs ?? 10,
      max_offset_ms: options.maxOffsetMs ?? 15 * 60_000,
      gss: !!options.gss,
      sample_rate: options.sampleRate ?? 16_000,
      vad_aggressiveness: options.vadAggressiveness ?? 2,
    };

    onProgress?.(65, 'Aligning subtitles to audio...');
    let result;
    try {
      result = api.align_wav(wavBytes, opts, srtText);
    } catch (e) {
      throw new Error(`ffsubsync alignment failed: ${e?.message || e}`);
    }

    if (!result || !result.srt) {
      throw new Error('ffsubsync returned empty result');
    }
    onProgress?.(100, 'ffsubsync alignment complete');
    return {
      method: 'ffsubsync',
      offsetMs: result.offset_ms,
      drift: result.drift,
      confidence: result.confidence,
      segments: result.segments_used,
      srt: result.srt,
    };
  }

  global.SubMakerFfsubsync = {
    init: async (opts = {}) => {
      await loadGlueAndWasm({ wasmPath: opts.wasmPath });
      return { align };
    },
  };
})(typeof self !== 'undefined' ? self : globalThis);
