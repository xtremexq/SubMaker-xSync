var wasm_bindgen = (typeof self !== 'undefined' && self.wasm_bindgen) ? self.wasm_bindgen : undefined;
(function() {
    const __exports = {};
    let script_src;
    if (typeof document !== 'undefined' && document.currentScript !== null) {
        script_src = new URL(document.currentScript.src, location.href).toString();
    }
    let wasm = undefined;

    function debugString(val) {
        // primitive types
        const type = typeof val;
        if (type == 'number' || type == 'boolean' || val == null) {
            return  `${val}`;
        }
        if (type == 'string') {
            return `"${val}"`;
        }
        if (type == 'symbol') {
            const description = val.description;
            if (description == null) {
                return 'Symbol';
            } else {
                return `Symbol(${description})`;
            }
        }
        if (type == 'function') {
            const name = val.name;
            if (typeof name == 'string' && name.length > 0) {
                return `Function(${name})`;
            } else {
                return 'Function';
            }
        }
        // objects
        if (Array.isArray(val)) {
            const length = val.length;
            let debug = '[';
            if (length > 0) {
                debug += debugString(val[0]);
            }
            for(let i = 1; i < length; i++) {
                debug += ', ' + debugString(val[i]);
            }
            debug += ']';
            return debug;
        }
        // Test for built-in
        const builtInMatches = /\[object ([^\]]+)\]/.exec(toString.call(val));
        let className;
        if (builtInMatches && builtInMatches.length > 1) {
            className = builtInMatches[1];
        } else {
            // Failed to match the standard '[object ClassName]'
            return toString.call(val);
        }
        if (className == 'Object') {
            // we're a user defined class or Object
            // JSON.stringify avoids problems with cycles, and is generally much
            // easier than looping through ownProperties of `val`.
            try {
                return 'Object(' + JSON.stringify(val) + ')';
            } catch (_) {
                return 'Object';
            }
        }
        // errors
        if (val instanceof Error) {
            return `${val.name}: ${val.message}\n${val.stack}`;
        }
        // TODO we could test for more things here, like `Set`s and `Map`s.
        return className;
    }

    function getArrayU8FromWasm0(ptr, len) {
        ptr = ptr >>> 0;
        return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
    }

    let cachedDataViewMemory0 = null;
    function getDataViewMemory0() {
        if (cachedDataViewMemory0 === null || cachedDataViewMemory0.buffer.detached === true || (cachedDataViewMemory0.buffer.detached === undefined && cachedDataViewMemory0.buffer !== wasm.memory.buffer)) {
            cachedDataViewMemory0 = new DataView(wasm.memory.buffer);
        }
        return cachedDataViewMemory0;
    }

    function getStringFromWasm0(ptr, len) {
        ptr = ptr >>> 0;
        return decodeText(ptr, len);
    }

    let cachedUint16ArrayMemory0 = null;
    function getUint16ArrayMemory0() {
        if (cachedUint16ArrayMemory0 === null || cachedUint16ArrayMemory0.byteLength === 0) {
            cachedUint16ArrayMemory0 = new Uint16Array(wasm.memory.buffer);
        }
        return cachedUint16ArrayMemory0;
    }

    let cachedUint8ArrayMemory0 = null;
    function getUint8ArrayMemory0() {
        if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
            cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
        }
        return cachedUint8ArrayMemory0;
    }

    function isLikeNone(x) {
        return x === undefined || x === null;
    }

    function passArray16ToWasm0(arg, malloc) {
        const ptr = malloc(arg.length * 2, 2) >>> 0;
        getUint16ArrayMemory0().set(arg, ptr / 2);
        WASM_VECTOR_LEN = arg.length;
        return ptr;
    }

    function passArray8ToWasm0(arg, malloc) {
        const ptr = malloc(arg.length * 1, 1) >>> 0;
        getUint8ArrayMemory0().set(arg, ptr / 1);
        WASM_VECTOR_LEN = arg.length;
        return ptr;
    }

    function passStringToWasm0(arg, malloc, realloc) {
        if (realloc === undefined) {
            const buf = cachedTextEncoder.encode(arg);
            const ptr = malloc(buf.length, 1) >>> 0;
            getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
            WASM_VECTOR_LEN = buf.length;
            return ptr;
        }

        let len = arg.length;
        let ptr = malloc(len, 1) >>> 0;

        const mem = getUint8ArrayMemory0();

        let offset = 0;

        for (; offset < len; offset++) {
            const code = arg.charCodeAt(offset);
            if (code > 0x7F) break;
            mem[ptr + offset] = code;
        }
        if (offset !== len) {
            if (offset !== 0) {
                arg = arg.slice(offset);
            }
            ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
            const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
            const ret = cachedTextEncoder.encodeInto(arg, view);

            offset += ret.written;
            ptr = realloc(ptr, len, offset, 1) >>> 0;
        }

        WASM_VECTOR_LEN = offset;
        return ptr;
    }

    function takeFromExternrefTable0(idx) {
        const value = wasm.__wbindgen_externrefs.get(idx);
        wasm.__externref_table_dealloc(idx);
        return value;
    }

    let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
    cachedTextDecoder.decode();
    function decodeText(ptr, len) {
        return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
    }

    const cachedTextEncoder = new TextEncoder();

    if (!('encodeInto' in cachedTextEncoder)) {
        cachedTextEncoder.encodeInto = function (arg, view) {
            const buf = cachedTextEncoder.encode(arg);
            view.set(buf);
            return {
                read: arg.length,
                written: buf.length
            };
        }
    }

    let WASM_VECTOR_LEN = 0;

    const FfsubsyncOptionsFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_ffsubsyncoptions_free(ptr >>> 0, 1));

    const FfsubsyncResultFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_ffsubsyncresult_free(ptr >>> 0, 1));

    class FfsubsyncOptions {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            FfsubsyncOptionsFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_ffsubsyncoptions_free(ptr, 0);
        }
        constructor() {
            const ret = wasm.ffsubsyncoptions_new();
            this.__wbg_ptr = ret >>> 0;
            FfsubsyncOptionsFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * Frame size in milliseconds (default 10).
         * @returns {number}
         */
        get frame_ms() {
            const ret = wasm.__wbg_get_ffsubsyncoptions_frame_ms(this.__wbg_ptr);
            return ret;
        }
        /**
         * Frame size in milliseconds (default 10).
         * @param {number} arg0
         */
        set frame_ms(arg0) {
            wasm.__wbg_set_ffsubsyncoptions_frame_ms(this.__wbg_ptr, arg0);
        }
        /**
         * Maximum absolute offset to search in milliseconds (default 60000).
         * @returns {number}
         */
        get max_offset_ms() {
            const ret = wasm.__wbg_get_ffsubsyncoptions_max_offset_ms(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * Maximum absolute offset to search in milliseconds (default 60000).
         * @param {number} arg0
         */
        set max_offset_ms(arg0) {
            wasm.__wbg_set_ffsubsyncoptions_max_offset_ms(this.__wbg_ptr, arg0);
        }
        /**
         * Use golden-section search for drift detection (default false).
         * @returns {boolean}
         */
        get gss() {
            const ret = wasm.__wbg_get_ffsubsyncoptions_gss(this.__wbg_ptr);
            return ret !== 0;
        }
        /**
         * Use golden-section search for drift detection (default false).
         * @param {boolean} arg0
         */
        set gss(arg0) {
            wasm.__wbg_set_ffsubsyncoptions_gss(this.__wbg_ptr, arg0);
        }
        /**
         * Expected sample rate of incoming PCM (default 16000).
         * @returns {number}
         */
        get sample_rate() {
            const ret = wasm.__wbg_get_ffsubsyncoptions_sample_rate(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * Expected sample rate of incoming PCM (default 16000).
         * @param {number} arg0
         */
        set sample_rate(arg0) {
            wasm.__wbg_set_ffsubsyncoptions_sample_rate(this.__wbg_ptr, arg0);
        }
        /**
         * VAD aggressiveness 0..3 (controls energy threshold).
         * @returns {number}
         */
        get vad_aggressiveness() {
            const ret = wasm.__wbg_get_ffsubsyncoptions_vad_aggressiveness(this.__wbg_ptr);
            return ret;
        }
        /**
         * VAD aggressiveness 0..3 (controls energy threshold).
         * @param {number} arg0
         */
        set vad_aggressiveness(arg0) {
            wasm.__wbg_set_ffsubsyncoptions_vad_aggressiveness(this.__wbg_ptr, arg0);
        }
    }
    if (Symbol.dispose) FfsubsyncOptions.prototype[Symbol.dispose] = FfsubsyncOptions.prototype.free;
    __exports.FfsubsyncOptions = FfsubsyncOptions;

    class FfsubsyncResult {
        static __wrap(ptr) {
            ptr = ptr >>> 0;
            const obj = Object.create(FfsubsyncResult.prototype);
            obj.__wbg_ptr = ptr;
            FfsubsyncResultFinalization.register(obj, obj.__wbg_ptr, obj);
            return obj;
        }
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            FfsubsyncResultFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_ffsubsyncresult_free(ptr, 0);
        }
        constructor() {
            const ret = wasm.ffsubsyncresult_new();
            this.__wbg_ptr = ret >>> 0;
            FfsubsyncResultFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * @returns {number}
         */
        get offset_ms() {
            const ret = wasm.__wbg_get_ffsubsyncresult_offset_ms(this.__wbg_ptr);
            return ret;
        }
        /**
         * @param {number} arg0
         */
        set offset_ms(arg0) {
            wasm.__wbg_set_ffsubsyncresult_offset_ms(this.__wbg_ptr, arg0);
        }
        /**
         * @returns {number}
         */
        get drift() {
            const ret = wasm.__wbg_get_ffsubsyncresult_drift(this.__wbg_ptr);
            return ret;
        }
        /**
         * @param {number} arg0
         */
        set drift(arg0) {
            wasm.__wbg_set_ffsubsyncresult_drift(this.__wbg_ptr, arg0);
        }
        /**
         * @returns {number}
         */
        get confidence() {
            const ret = wasm.__wbg_get_ffsubsyncresult_confidence(this.__wbg_ptr);
            return ret;
        }
        /**
         * @param {number} arg0
         */
        set confidence(arg0) {
            wasm.__wbg_set_ffsubsyncresult_confidence(this.__wbg_ptr, arg0);
        }
        /**
         * @returns {number}
         */
        get segments_used() {
            const ret = wasm.__wbg_get_ffsubsyncresult_segments_used(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * @param {number} arg0
         */
        set segments_used(arg0) {
            wasm.__wbg_set_ffsubsyncresult_segments_used(this.__wbg_ptr, arg0);
        }
        /**
         * @returns {string}
         */
        get srt() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.__wbg_get_ffsubsyncresult_srt(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * @param {string} arg0
         */
        set srt(arg0) {
            const ptr0 = passStringToWasm0(arg0, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            wasm.__wbg_set_ffsubsyncresult_srt(this.__wbg_ptr, ptr0, len0);
        }
    }
    if (Symbol.dispose) FfsubsyncResult.prototype[Symbol.dispose] = FfsubsyncResult.prototype.free;
    __exports.FfsubsyncResult = FfsubsyncResult;

    /**
     * @param {Int16Array} pcm
     * @param {any} opts
     * @param {string} srt
     * @returns {FfsubsyncResult}
     */
    function align_pcm(pcm, opts, srt) {
        const ptr0 = passArray16ToWasm0(pcm, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(srt, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.align_pcm(ptr0, len0, opts, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return FfsubsyncResult.__wrap(ret[0]);
    }
    __exports.align_pcm = align_pcm;

    /**
     * @param {Uint8Array} wav_bytes
     * @param {any} opts
     * @param {string} srt
     * @returns {FfsubsyncResult}
     */
    function align_wav(wav_bytes, opts, srt) {
        const ptr0 = passArray8ToWasm0(wav_bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(srt, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.align_wav(ptr0, len0, opts, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return FfsubsyncResult.__wrap(ret[0]);
    }
    __exports.align_wav = align_wav;

    const EXPECTED_RESPONSE_TYPES = new Set(['basic', 'cors', 'default']);

    async function __wbg_load(module, imports) {
        if (typeof Response === 'function' && module instanceof Response) {
            if (typeof WebAssembly.instantiateStreaming === 'function') {
                try {
                    return await WebAssembly.instantiateStreaming(module, imports);
                } catch (e) {
                    const validResponse = module.ok && EXPECTED_RESPONSE_TYPES.has(module.type);

                    if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                        console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                    } else {
                        throw e;
                    }
                }
            }

            const bytes = await module.arrayBuffer();
            return await WebAssembly.instantiate(bytes, imports);
        } else {
            const instance = await WebAssembly.instantiate(module, imports);

            if (instance instanceof WebAssembly.Instance) {
                return { instance, module };
            } else {
                return instance;
            }
        }
    }

    function __wbg_get_imports() {
        const imports = {};
        imports.wbg = {};
        imports.wbg.__wbg_Error_52673b7de5a0ca89 = function(arg0, arg1) {
            const ret = Error(getStringFromWasm0(arg0, arg1));
            return ret;
        };
        imports.wbg.__wbg_Number_2d1dcfcf4ec51736 = function(arg0) {
            const ret = Number(arg0);
            return ret;
        };
        imports.wbg.__wbg___wbindgen_boolean_get_dea25b33882b895b = function(arg0) {
            const v = arg0;
            const ret = typeof(v) === 'boolean' ? v : undefined;
            return isLikeNone(ret) ? 0xFFFFFF : ret ? 1 : 0;
        };
        imports.wbg.__wbg___wbindgen_debug_string_adfb662ae34724b6 = function(arg0, arg1) {
            const ret = debugString(arg1);
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        };
        imports.wbg.__wbg___wbindgen_in_0d3e1e8f0c669317 = function(arg0, arg1) {
            const ret = arg0 in arg1;
            return ret;
        };
        imports.wbg.__wbg___wbindgen_is_object_ce774f3490692386 = function(arg0) {
            const val = arg0;
            const ret = typeof(val) === 'object' && val !== null;
            return ret;
        };
        imports.wbg.__wbg___wbindgen_is_undefined_f6b95eab589e0269 = function(arg0) {
            const ret = arg0 === undefined;
            return ret;
        };
        imports.wbg.__wbg___wbindgen_jsval_loose_eq_766057600fdd1b0d = function(arg0, arg1) {
            const ret = arg0 == arg1;
            return ret;
        };
        imports.wbg.__wbg___wbindgen_number_get_9619185a74197f95 = function(arg0, arg1) {
            const obj = arg1;
            const ret = typeof(obj) === 'number' ? obj : undefined;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        };
        imports.wbg.__wbg___wbindgen_string_get_a2a31e16edf96e42 = function(arg0, arg1) {
            const obj = arg1;
            const ret = typeof(obj) === 'string' ? obj : undefined;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        };
        imports.wbg.__wbg___wbindgen_throw_dd24417ed36fc46e = function(arg0, arg1) {
            throw new Error(getStringFromWasm0(arg0, arg1));
        };
        imports.wbg.__wbg_get_with_ref_key_1dc361bd10053bfe = function(arg0, arg1) {
            const ret = arg0[arg1];
            return ret;
        };
        imports.wbg.__wbg_instanceof_ArrayBuffer_f3320d2419cd0355 = function(arg0) {
            let result;
            try {
                result = arg0 instanceof ArrayBuffer;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        };
        imports.wbg.__wbg_instanceof_Uint8Array_da54ccc9d3e09434 = function(arg0) {
            let result;
            try {
                result = arg0 instanceof Uint8Array;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        };
        imports.wbg.__wbg_isSafeInteger_ae7d3f054d55fa16 = function(arg0) {
            const ret = Number.isSafeInteger(arg0);
            return ret;
        };
        imports.wbg.__wbg_length_22ac23eaec9d8053 = function(arg0) {
            const ret = arg0.length;
            return ret;
        };
        imports.wbg.__wbg_new_1ba21ce319a06297 = function() {
            const ret = new Object();
            return ret;
        };
        imports.wbg.__wbg_new_6421f6084cc5bc5a = function(arg0) {
            const ret = new Uint8Array(arg0);
            return ret;
        };
        imports.wbg.__wbg_prototypesetcall_dfe9b766cdc1f1fd = function(arg0, arg1, arg2) {
            Uint8Array.prototype.set.call(getArrayU8FromWasm0(arg0, arg1), arg2);
        };
        imports.wbg.__wbg_set_3f1d0b984ed272ed = function(arg0, arg1, arg2) {
            arg0[arg1] = arg2;
        };
        imports.wbg.__wbindgen_cast_2241b6af4c4b2941 = function(arg0, arg1) {
            // Cast intrinsic for `Ref(String) -> Externref`.
            const ret = getStringFromWasm0(arg0, arg1);
            return ret;
        };
        imports.wbg.__wbindgen_cast_d6cd19b81560fd6e = function(arg0) {
            // Cast intrinsic for `F64 -> Externref`.
            const ret = arg0;
            return ret;
        };
        imports.wbg.__wbindgen_init_externref_table = function() {
            const table = wasm.__wbindgen_externrefs;
            const offset = table.grow(4);
            table.set(0, undefined);
            table.set(offset + 0, undefined);
            table.set(offset + 1, null);
            table.set(offset + 2, true);
            table.set(offset + 3, false);
        };

        return imports;
    }

    function __wbg_finalize_init(instance, module) {
        wasm = instance.exports;
        __wbg_init.__wbindgen_wasm_module = module;
        cachedDataViewMemory0 = null;
        cachedUint16ArrayMemory0 = null;
        cachedUint8ArrayMemory0 = null;


        wasm.__wbindgen_start();
        return wasm;
    }

    function initSync(module) {
        if (wasm !== undefined) return wasm;


        if (typeof module !== 'undefined') {
            if (Object.getPrototypeOf(module) === Object.prototype) {
                ({module} = module)
            } else {
                console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
            }
        }

        const imports = __wbg_get_imports();
        if (!(module instanceof WebAssembly.Module)) {
            module = new WebAssembly.Module(module);
        }
        const instance = new WebAssembly.Instance(module, imports);
        return __wbg_finalize_init(instance, module);
    }

    async function __wbg_init(module_or_path) {
        if (wasm !== undefined) return wasm;


        if (typeof module_or_path !== 'undefined') {
            if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
                ({module_or_path} = module_or_path)
            } else {
                console.warn('using deprecated parameters for the initialization function; pass a single object instead')
            }
        }


        const imports = __wbg_get_imports();

        if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
            module_or_path = fetch(module_or_path);
        }

        const { instance, module } = await __wbg_load(await module_or_path, imports);

        return __wbg_finalize_init(instance, module);
    }

    wasm_bindgen = Object.assign(__wbg_init, { initSync }, __exports);
})();
