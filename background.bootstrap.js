/**
 * SubMaker xSync - Lightweight background bootstrap
 * Keeps the popup fast while ensuring MV3 doesn't block late importScripts.
 */

// Flag for the full worker so it knows it was bootstrapped.
self.__xsyncBootstrapped = true;
self.__xsyncPreloadErrors = self.__xsyncPreloadErrors || {};

// MV3-safe eager preloads. These must be loaded at initial worker evaluation.
const preloadScripts = [
  { key: 'transfer', url: 'assets/lib/idb-transfer.js' },
  { key: 'ffsubsync', url: 'assets/lib/ffsubsync-wasm.js' },
  { key: 'ffsubsync-glue', url: 'assets/lib/ffsubsync_wasm.js', bindgenAlias: '__SubMakerFfsubsyncBindgen' },
  { key: 'alass', url: 'assets/lib/alass-wasm.js' },
  { key: 'alass-glue', url: 'assets/lib/alass.js', bindgenAlias: '__SubMakerAlassBindgen' }
];

for (const item of preloadScripts) {
  try {
    importScripts(item.url);
    if (item.bindgenAlias) {
      if (typeof self.wasm_bindgen === 'function') {
        self[item.bindgenAlias] = self.wasm_bindgen;
      } else {
        self.__xsyncPreloadErrors[item.key] = new Error(`wasm_bindgen missing after preloading ${item.url}`);
      }
    }
  } catch (err) {
    self.__xsyncPreloadErrors[item.key] = err;
    console.warn(`[SubMaker xSync Bootstrap] Failed to preload ${item.url}:`, err?.message || err);
  }
}

// Eagerly load the heavy worker at startup so MV3 doesn't block late importScripts.
let _heavyLoaded = false;
let _heavyLoadError = null;
try {
  importScripts('background.full.js'); // registers __xsyncHandleMessage / __xsyncStatus
  _heavyLoaded = true;
} catch (err) {
  _heavyLoadError = err;
  console.error('[SubMaker xSync Bootstrap] Failed to preload heavy worker:', err);
}

function respondStatus(sendResponse) {
  try {
    const statusFn = self.__xsyncStatus;
    if (typeof statusFn === 'function') {
      const status = statusFn();
      sendResponse?.({
        active: status?.active || 0,
        extracting: status?.extracting || 0
      });
      return;
    }
  } catch (_) { /* ignore */ }
  sendResponse?.({ active: 0, extracting: 0 });
}

chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  // Fast path: respond to popup ping without loading the heavy worker.
  if (message?.type === 'GET_STATUS' && !_heavyLoaded) {
    respondStatus(sendResponse);
    return false; // synchronous response
  }

  if (!_heavyLoaded) {
    const errorMsg = _heavyLoadError?.message || 'xSync worker failed to preload';
    sendResponse?.({ success: false, error: errorMsg });
    return false;
  }

  try {
    const handler = self.__xsyncHandleMessage;
    if (typeof handler === 'function') {
      const keepAlive = handler(message, sender, sendResponse);
      if (keepAlive === true) return true; // handler will close the channel later
      return false; // synchronous or already responded
    }
    sendResponse?.({ success: false, error: 'xSync handler unavailable' });
  } catch (err) {
    sendResponse?.({ success: false, error: err?.message || 'xSync handler error' });
  }

  // Keep the message channel alive while the heavy worker loads and handles.
  return true;
});

console.log('[SubMaker xSync Bootstrap] Ready (heavy worker preloaded)');
