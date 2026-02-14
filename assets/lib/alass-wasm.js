/**
 * alass-wasm loader wrapper for SubMaker xSync
 *
 * New API: alignAudio(audioBytes|[{ audio, startMs?, sampleRateHint? }], targetSrt, { splitPenalty?, speedOptimization?, allowDrift?, sampleRateHint? })
 * Legacy API: alignSubtitles(referenceSrt, targetSrt, options?) for two-SRT alignment (kept for compatibility).
 */

(function () {
  const state = {
    bindgen: null,
  };

  const Fallback = {
    __available: false,
    alignAudio: async () => { throw new Error('alass-wasm not available'); },
    alignSubtitles: async () => { throw new Error('alass-wasm not available'); }
  };

  async function loadScript(glueUrl) {
    if (!glueUrl) {
      throw new Error('Missing glue URL for alass-wasm');
    }
    if (typeof self.__SubMakerAlassBindgen === 'function') {
      state.bindgen = self.__SubMakerAlassBindgen;
      return state.bindgen;
    }
    if (typeof state.bindgen === 'function') return state.bindgen;
    if (typeof importScripts !== 'function') {
      throw new Error('importScripts unavailable for alass loader');
    }
    const previous = self.wasm_bindgen;
    importScripts(glueUrl);
    if (typeof self.wasm_bindgen !== 'function') {
      throw new Error('wasm_bindgen not found after loading alass.js');
    }
    state.bindgen = self.wasm_bindgen;
    self.wasm_bindgen = previous;
    return state.bindgen;
  }

  async function toUint8Array(input) {
    if (!input) throw new Error('No audio input provided');
    if (input instanceof Uint8Array) return input;
    if (input instanceof ArrayBuffer) return new Uint8Array(input);
    if (ArrayBuffer.isView(input)) return new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
    if (typeof input.arrayBuffer === 'function') {
      const buf = await input.arrayBuffer();
      return new Uint8Array(buf);
    }
    throw new Error('Unsupported audio input type');
  }

  async function normalizeAudioInput(input) {
    if (Array.isArray(input)) {
      const windows = [];
      for (const w of input) {
        const audioSrc = w?.audio || w?.audioBlob || w;
        const audio = await toUint8Array(audioSrc);
        windows.push({
          audio,
          startMs: typeof w?.startMs === 'number' ? w.startMs : 0,
          sampleRateHint: typeof w?.sampleRateHint === 'number' ? w.sampleRateHint : undefined
        });
      }
      return { windows };
    }
    return { bytes: await toUint8Array(input) };
  }

  async function init(options = {}) {
    const wasmPath = options.wasmPath;
    if (!wasmPath) {
      console.warn('[alass-wasm] Missing wasmPath');
      return Fallback;
    }

    try {
      const glueUrl = (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.getURL)
        ? chrome.runtime.getURL('assets/lib/alass.js')
        : 'alass.js';
      const bindgen = await loadScript(glueUrl);
      const resolvedWasm = wasmPath || (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.getURL
        ? chrome.runtime.getURL('assets/lib/alass.wasm')
        : 'alass.wasm');
      const wasmBytes = await fetch(resolvedWasm).then(r => {
        if (!r.ok) throw new Error(`Failed to fetch alass.wasm: ${r.status}`);
        return r.arrayBuffer();
      });

      await bindgen(wasmBytes);
      if (typeof bindgen.align_audio_subtitles !== 'function') {
        throw new Error('align_audio_subtitles export missing in alass-wasm');
      }

      const alignAudio = async (audioInput, targetSrt, opts = {}) => {
        if (!audioInput) throw new Error('Audio input is required for alass alignment');
        const normalized = await normalizeAudioInput(audioInput);
        const splitPenalty = typeof opts.splitPenalty === 'number' ? opts.splitPenalty : undefined;
        const speedOptimization = typeof opts.speedOptimization === 'number' ? opts.speedOptimization : undefined;
        const allowDrift = opts.allowDrift !== false;

        let result;
        if (normalized.windows && normalized.windows.length && typeof bindgen.align_audio_windows === 'function') {
          result = bindgen.align_audio_windows(
            normalized.windows,
            targetSrt || '',
            splitPenalty ?? undefined,
            speedOptimization ?? undefined,
            allowDrift
          );
        } else {
          result = bindgen.align_audio_subtitles(
            normalized.bytes,
            targetSrt || '',
            opts.sampleRateHint ?? undefined,
            splitPenalty ?? undefined,
            speedOptimization ?? undefined,
            allowDrift
          );
        }

        const aligned = typeof result?.aligned_srt === 'function' ? result.aligned_srt() : null;
        const anchors = typeof result?.anchors === 'function' ? result.anchors() : undefined;
        const score = typeof result?.score === 'function' ? result.score() : undefined;
        const sampleRateHz = typeof result?.sample_rate_hz === 'function' ? result.sample_rate_hz() : undefined;

        if (!aligned || typeof aligned !== 'string') {
          throw new Error('alass-wasm returned empty result');
        }
        return { srt: aligned, anchors, score, sampleRateHz };
      };

      const alignSubtitles = async (referenceSrt, targetSrt, options = {}) => {
        const { splitPenalty, speedOptimization, allowDrift = true } = options || {};
        const hasOpts = typeof bindgen.align_subtitles_opts === 'function';
        const out = hasOpts
          ? bindgen.align_subtitles_opts(
              referenceSrt || '',
              targetSrt || '',
              splitPenalty ?? undefined,
              speedOptimization ?? undefined,
              allowDrift
            )
          : bindgen.align_subtitles(referenceSrt || '', targetSrt || '');
        if (!out || typeof out !== 'string') {
          throw new Error('alass-wasm returned empty subtitle result');
        }
        return out;
      };

      return { __available: true, alignAudio, alignSubtitles };
    } catch (e) {
      console.warn('[alass-wasm] Failed to initialize:', e?.message);
      return { ...Fallback, __error: e?.message || String(e) };
    }
  }

  self.SubMakerAlass = { init };
})();
