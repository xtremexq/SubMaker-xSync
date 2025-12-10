/**
 * SubMaker xSync - Content Script
 * Handles communication between the SubMaker sync page and the extension background worker
 */

console.log('[SubMaker xSync] Content script loaded');

// State management
let extensionReady = false;
const pendingExtractResults = new Map();
const CONFIG_TOKEN_STORAGE_KEY = 'submaker_session_token';
const DEFAULT_TOOLBOX_VIDEO_ID = 'Stream and Refresh';
const DEFAULT_TOOLBOX_FILENAME = 'Stream and Refresh';
const INSTALL_URL_INPUT_IDS = ['installUrlDisplay', 'installUrlBox'];

function translate(key, fallback) {
  try {
    if (typeof window !== 'undefined' && typeof window.t === 'function') {
      return window.t(key, {}, fallback || key);
    }
  } catch (_) {}
  try {
    if (typeof chrome !== 'undefined' && chrome.i18n?.getMessage) {
      const chromeKey = String(key || '').replace(/[^a-zA-Z0-9_]/g, '_');
      const msg = chrome.i18n.getMessage(chromeKey);
      if (msg) return msg;
    }
  } catch (_) {}
  return fallback || key;
}

function normalizeHost(hostname) {
  return hostname ? hostname.trim().toLowerCase() : null;
}

function safeHostname(url) {
  try {
    return new URL(url).hostname;
  } catch (_) {
    return null;
  }
}

function safeUrl(raw) {
  try {
    return new URL(raw);
  } catch (_) {
    return null;
  }
}

function safeOrigin(raw) {
  const parsed = safeUrl(raw);
  return parsed ? parsed.origin : null;
}

function extractConfigToken(fromUrl) {
  if (!fromUrl) return null;
  try {
    const url = new URL(fromUrl);
    const paramToken = url.searchParams.get('config');
    if (paramToken) return paramToken;

    const parts = url.pathname.split('/').filter(Boolean);
    const configureIdx = parts.findIndex(p => p.toLowerCase() === 'configure');
    if (configureIdx !== -1 && parts.length > configureIdx + 1) {
      return parts[configureIdx + 1];
    }
    const toolboxIdx = parts.findIndex(p => p.toLowerCase() === 'sub-toolbox');
    if (toolboxIdx !== -1 && parts.length > toolboxIdx + 1) {
      return parts[toolboxIdx + 1];
    }
    const addonIdx = parts.findIndex(p => p.toLowerCase() === 'addon');
    if (addonIdx !== -1 && parts.length > addonIdx + 1) {
      return parts[addonIdx + 1];
    }
    return null;
  } catch (_) {
    return null;
  }
}

function mergeSearchParams(seedUrls = [], overrides = {}, defaults = {}) {
  const params = new URLSearchParams();
  seedUrls.forEach((raw) => {
    const parsed = safeUrl(raw);
    if (!parsed) return;
    parsed.searchParams.forEach((value, key) => {
      params.set(key, value);
    });
  });
  Object.entries(overrides || {}).forEach(([key, value]) => {
    if (value === undefined || value === null || value === '') return;
    params.set(key, value);
  });
  Object.entries(defaults || {}).forEach(([key, value]) => {
    const existing = params.get(key);
    if (existing === null || existing === undefined || existing === '') {
      params.set(key, value);
    }
  });
  const sorted = new URLSearchParams();
  Array.from(params.entries())
    .sort(([a], [b]) => a.localeCompare(b))
    .forEach(([key, value]) => sorted.append(key, value));
  return sorted;
}

function deriveConfigureUrl(fromUrl, tokenOverride, fallbackUrl) {
  const baseOrigin = safeOrigin(fromUrl) || safeOrigin(fallbackUrl);
  if (!baseOrigin) return null;
  const config = tokenOverride || extractConfigToken(fromUrl) || extractConfigToken(fallbackUrl);
  const url = new URL('/configure', baseOrigin);
  const params = mergeSearchParams([fallbackUrl, fromUrl], { config }, {});
  url.search = params.toString();
  return url.toString();
}

function deriveToolboxUrl(fromUrl, tokenOverride, existingUrl) {
  const baseOrigin = safeOrigin(fromUrl) || safeOrigin(existingUrl);
  if (!baseOrigin) return null;
  const config = tokenOverride || extractConfigToken(fromUrl) || extractConfigToken(existingUrl);
  const params = mergeSearchParams(
    [existingUrl, fromUrl],
    { config },
    { videoId: DEFAULT_TOOLBOX_VIDEO_ID, filename: DEFAULT_TOOLBOX_FILENAME }
  );
  const url = new URL('/sub-toolbox', baseOrigin);
  url.search = params.toString();
  return url.toString();
}

function readInstallUrl() {
  try {
    if (typeof window !== 'undefined' && typeof window.installUrl === 'string' && window.installUrl) {
      return window.installUrl;
    }
  } catch (_) {}
  for (const id of INSTALL_URL_INPUT_IDS) {
    try {
      const el = document.getElementById(id);
      if (!el) continue;
      const candidate = (el.value || el.textContent || '').trim();
      if (candidate) return candidate;
    } catch (_) {}
  }
  return null;
}

function readStoredSessionToken() {
  try {
    const token = localStorage.getItem(CONFIG_TOKEN_STORAGE_KEY);
    return token || null;
  } catch (_) {
    return null;
  }
}

function hasToolboxParams(url) {
  const parsed = safeUrl(url);
  if (!parsed) return false;
  const videoId = parsed.searchParams.get('videoId');
  const filename = parsed.searchParams.get('filename');
  return !!(videoId && filename);
}

function normalizeUrlForCompare(url) {
  const parsed = safeUrl(url);
  if (!parsed) return url || '';
  parsed.hash = '';
  parsed.search = mergeSearchParams([parsed.toString()]).toString();
  return parsed.toString();
}

function clearPendingExtract(messageId) {
  const timer = pendingExtractResults.get(messageId);
  if (timer) clearTimeout(timer);
  pendingExtractResults.delete(messageId);
}

function schedulePendingExtractFailure(messageId, errorMsg) {
  if (!messageId) return;
  clearPendingExtract(messageId);
  const timer = setTimeout(() => {
    pendingExtractResults.delete(messageId);
    sendToPage({
      type: 'SUBMAKER_EXTRACT_RESPONSE',
      messageId,
      source: 'extension',
      success: false,
      error: errorMsg || translate('xsync.content.extractFailed', 'Extraction failed')
    });
  }, 8000);
  pendingExtractResults.set(messageId, timer);
}

function isTransientPortError(err) {
  const msg = (err?.message || err || '').toLowerCase();
  return msg.includes('message port closed') || msg.includes('receiving end does not exist');
}

function normalizeExtractModeValue(mode) {
  const cleaned = String(mode || '')
    .trim()
    .toLowerCase()
    .replace(/[-_\s]*v2$/, '')      // strip legacy -v2/_v2 suffix
    .replace(/[-_\s]+/g, '-');      // align separators for comparisons
  if (cleaned === 'complete' || cleaned === 'full' || cleaned === 'fullfetch') return 'complete';
  if (cleaned === 'smart') return 'smart';
  return 'smart';
}

// Forward progress events from the background worker to the web page
chrome.runtime.onMessage.addListener((msg) => {
  if (msg?.type === 'SYNC_PROGRESS') {
    sendToPage({
      type: 'SUBMAKER_SYNC_PROGRESS',
      source: 'extension',
      messageId: msg.messageId,
      progress: msg.progress,
      status: msg.status
    });
  } else if (msg?.type === 'EXTRACT_PROGRESS') {
    sendToPage({
      type: 'SUBMAKER_EXTRACT_PROGRESS',
      source: 'extension',
      messageId: msg.messageId,
      progress: msg.progress,
      status: msg.status
    });
  } else if (msg?.type === 'SUBMAKER_DEBUG_LOG') {
    console[msg.level === 'error' ? 'error' : msg.level === 'warn' ? 'warn' : 'log']('[SubMaker xSync][Debug]', msg.text || '', msg.messageId ? `(job ${msg.messageId})` : '');
    sendToPage({
      type: 'SUBMAKER_DEBUG_LOG',
      source: 'extension',
      messageId: msg.messageId,
      level: msg.level || 'info',
      text: msg.text || '',
      ts: msg.ts || Date.now()
    });
  } else if (msg?.type === 'EXTRACT_RESPONSE') {
    clearPendingExtract(msg.messageId);
    sendToPage({
      type: 'SUBMAKER_EXTRACT_RESPONSE',
      source: 'extension',
      messageId: msg.messageId,
      success: msg.success,
      tracks: msg.tracks || [],
      error: msg.error || null
    });
  } else if (msg?.type === 'AUTOSUB_PROGRESS') {
    sendToPage({
      type: 'SUBMAKER_AUTOSUB_PROGRESS',
      source: 'extension',
      messageId: msg.messageId,
      progress: msg.progress,
      status: msg.status,
      stage: msg.stage,
      level: msg.level
    });
  } else if (msg?.type === 'AUTOSUB_TRACK_OPTIONS') {
    sendToPage({
      type: 'SUBMAKER_AUTOSUB_TRACKS',
      source: 'extension',
      messageId: msg.messageId,
      tracks: msg.tracks || [],
      suggestedIndex: msg.suggestedIndex,
      extractedIndex: msg.extractedIndex
    });
  } else if (msg?.type === 'AUTOSUB_RESPONSE') {
    sendToPage({
      type: 'SUBMAKER_AUTOSUB_RESPONSE',
      source: 'extension',
      messageId: msg.messageId,
      success: msg.success,
      transcript: msg
    });
  }
});

// Initialize extension
(async function init() {
  try {
    // Detect whether we're on any SubMaker tool page; keep listening even if the
    // path is unexpected (e.g., cache-busted or legacy slug) so PING/PONG still works.
    const locationString = [
      window.location.pathname || '',
      window.location.search || '',
      window.location.hash || ''
    ].join(' ').toLowerCase();
    const isSupportedPage = [
      '/subtitle-sync',
      '/sync-subtitles', // legacy/addon slug
      '/embedded-subtitles',
      '/auto-subtitles',
      '/sub-toolbox',
      '/configure'
    ].some(fragment => locationString.includes(fragment));

    if (isSupportedPage) {
      console.log('[SubMaker xSync] Detected supported page, initializing...');

      // Save known URLs for the popup to use
      try {
        const currentUrl = window.location.href;
        const isConfigurePage = locationString.includes('/configure');
        const isToolboxPage = locationString.includes('/sub-toolbox');
        const isSyncPage = locationString.includes('/subtitle-sync') || locationString.includes('/sync-subtitles');
        const existing = await chrome.storage.local.get(['toolboxUrl', 'configureUrl', 'syncUrl', 'recognizedHost']);
        const storageUpdates = {};

        const currentHost = normalizeHost(safeHostname(currentUrl));
        const storedHost = normalizeHost(existing.recognizedHost) ||
          normalizeHost(safeHostname(existing.configureUrl)) ||
          normalizeHost(safeHostname(existing.toolboxUrl)) ||
          normalizeHost(safeHostname(existing.syncUrl));
        let recognizedHost = storedHost;

        if (!existing.recognizedHost && storedHost) {
          storageUpdates.recognizedHost = storedHost;
        }
        if (!recognizedHost && currentHost) {
          recognizedHost = currentHost;
          storageUpdates.recognizedHost = currentHost;
        }

        const hostMatches = !recognizedHost || !currentHost || recognizedHost === currentHost;

        if (!hostMatches) {
          console.warn('[SubMaker xSync] Skipping URL capture due to host mismatch', {
            recognizedHost,
            currentHost
          });
        } else {
          const installUrl = readInstallUrl();
          const currentToken = extractConfigToken(currentUrl) || extractConfigToken(installUrl) || readStoredSessionToken();
          const storedToken = extractConfigToken(existing.configureUrl) || extractConfigToken(existing.toolboxUrl);
          const tokenChanged = currentToken && storedToken && currentToken !== storedToken;
          const hasFreshToken = currentToken && !storedToken;

          const normalizedConfigure = deriveConfigureUrl(
            currentUrl || existing.configureUrl || installUrl,
            currentToken || storedToken,
            existing.configureUrl || installUrl
          ) || currentUrl;
          const configureChanged = normalizedConfigure && existing.configureUrl && normalizeUrlForCompare(existing.configureUrl) !== normalizeUrlForCompare(normalizedConfigure);
          if (normalizedConfigure && (!existing.configureUrl || tokenChanged || hasFreshToken || configureChanged)) {
            storageUpdates.configureUrl = normalizedConfigure;
          }

          const derivedToolbox = deriveToolboxUrl(
            currentUrl || existing.toolboxUrl || installUrl,
            currentToken || storedToken,
            existing.toolboxUrl || existing.configureUrl
          );
          const toolboxChanged = derivedToolbox && existing.toolboxUrl && normalizeUrlForCompare(existing.toolboxUrl) !== normalizeUrlForCompare(derivedToolbox);
          const toolboxMissingParams = !hasToolboxParams(existing.toolboxUrl);
          if (derivedToolbox && (!existing.toolboxUrl || tokenChanged || hasFreshToken || toolboxChanged || toolboxMissingParams)) {
            storageUpdates.toolboxUrl = derivedToolbox;
          }

          if (isSyncPage && (!existing.syncUrl || !existing.syncUrl.length)) {
            storageUpdates.syncUrl = currentUrl;
          }
        }

        if (Object.keys(storageUpdates).length > 0) {
          chrome.storage.local.set(storageUpdates);
          console.log('[SubMaker xSync] Updated known URLs:', Object.keys(storageUpdates));
        }
      } catch (e) {
        console.warn('[SubMaker xSync] Failed to save page URL', e);
      }
    } else {
      console.log('[SubMaker xSync] Page not recognized as a SubMaker tool; staying idle but listening for pings.');
    }

    // Wait for page to be fully loaded
    if (document.readyState === 'loading') {
      await new Promise(resolve => {
        document.addEventListener('DOMContentLoaded', resolve);
      });
    }

    extensionReady = true;
    console.log('[SubMaker xSync] Extension ready');

    // Start listening for messages from the page
    window.addEventListener('message', handlePageMessage);

    // Announce presence to page (only on recognized SubMaker routes)
    if (isSupportedPage) {
      setTimeout(() => {
        console.log('[SubMaker xSync] Waiting for PING from webpage...');
        sendToPage({
          type: 'SUBMAKER_PONG',
          source: 'extension',
          version: chrome.runtime.getManifest().version
        });
      }, 100);
    }

  } catch (error) {
    console.error('[SubMaker xSync] Initialization error:', error);
  }
})();

/**
 * Handle messages from the webpage
 */
async function handlePageMessage(event) {
  // Only accept messages from same origin
  if (event.source !== window) {
    return;
  }

  const message = event.data;

  // Only process explicit SubMaker webpage messages; ignore stray postMessage noise (e.g. numeric events)
  const fromWebpage = message?.source === 'webpage';
  const isSubmakerMessage = typeof message?.type === 'string' && message.type.startsWith('SUBMAKER_');
  if (!fromWebpage || !isSubmakerMessage) {
    return;
  }

  console.log('[SubMaker xSync] Received message from webpage:', message.type);

  try {
    switch (message.type) {
      case 'SUBMAKER_PING':
        await handlePing(message);
        break;

      case 'SUBMAKER_SYNC_REQUEST':
        await handleSyncRequest(message);
        break;

      case 'SUBMAKER_EXTRACT_REQUEST':
        await handleExtractRequest(message);
        break;

      case 'SUBMAKER_AUTOSUB_REQUEST':
        await handleAutoSubRequest(message);
        break;

      case 'SUBMAKER_AUTOSUB_SELECT_TRACK':
        await handleAutoSubTrackSelection(message);
        break;

      case 'SUBMAKER_EMBEDDED_RESET':
        await handleEmbeddedReset(message);
        break;

      default:
        console.log('[SubMaker xSync] Unknown message type:', message.type);
    }
  } catch (error) {
    console.error('[SubMaker xSync] Error handling message:', error);

    // Send error response if it's a sync request
    if (message.type === 'SUBMAKER_SYNC_REQUEST') {
      sendToPage({
        type: 'SUBMAKER_SYNC_RESPONSE',
        messageId: message.messageId,
        source: 'extension',
        success: false,
        error: error.message || 'Unknown error occurred'
      });
    }
    if (message.type === 'SUBMAKER_EXTRACT_REQUEST') {
      sendToPage({
        type: 'SUBMAKER_EXTRACT_RESPONSE',
        messageId: message.messageId,
        source: 'extension',
        success: false,
        error: error.message || 'Unknown error occurred'
      });
    }
    if (message.type === 'SUBMAKER_AUTOSUB_REQUEST') {
      sendToPage({
        type: 'SUBMAKER_AUTOSUB_RESPONSE',
        messageId: message.messageId,
        source: 'extension',
        success: false,
        error: error.message || 'Unknown error occurred'
      });
    }
  }
}

/**
 * Handle PING from webpage (extension detection)
 */
async function handlePing(message) {
  console.log('[SubMaker xSync] Received PING, sending PONG...');

  sendToPage({
    type: 'SUBMAKER_PONG',
    source: 'extension',
    version: chrome.runtime.getManifest().version
  });
}

/**
 * Handle sync request from webpage
 */
async function handleSyncRequest(message) {
  console.log('[SubMaker xSync] Sync request received:', {
    messageId: message.messageId,
    hasStreamUrl: !!message.data?.streamUrl,
    hasSubtitle: !!message.data?.subtitleContent
  });

  const { streamUrl, subtitleContent, mode, plan, preferAlass, preferFfsubsync, preferCtc } = message.data || {};
  const normalizedMode = plan?.preset || mode || 'smart';
  const pageHeaders = {
    referer: window.location.href || null,
    cookie: document?.cookie || null,
    userAgent: navigator?.userAgent || null
  };

  // Validate request
  if (!streamUrl || !subtitleContent) {
    throw new Error('Missing streamUrl or subtitleContent in sync request');
  }

  // Send initial progress update
  sendProgressUpdate(message.messageId, 0, 'Initializing sync process...');

  try {
    // Forward request to background worker
    console.log('[SubMaker xSync] Forwarding to background worker...');

    const response = await sendRuntimeMessage({
      type: 'SYNC_REQUEST',
      messageId: message.messageId,
      streamUrl: streamUrl,
      subtitleContent: subtitleContent,
      mode: normalizedMode,
      plan: plan || null,
      preferAlass: preferAlass === true,
      preferFfsubsync: preferFfsubsync === true,
      preferCtc: preferCtc === true,
      pageHeaders
    });

    console.log('[SubMaker xSync] Received response from background:', {
      success: response.success,
      hasResult: !!response.syncedSubtitle
    });

    // Forward response to webpage
    sendToPage({
      type: 'SUBMAKER_SYNC_RESPONSE',
      messageId: message.messageId,
      source: 'extension',
      success: response.success,
      syncedSubtitle: response.syncedSubtitle || null,
      error: response.error || null
    });

  } catch (error) {
    console.error('[SubMaker xSync] Sync request failed:', error);

    sendToPage({
      type: 'SUBMAKER_SYNC_RESPONSE',
      messageId: message.messageId,
      source: 'extension',
      success: false,
      error: error.message || 'Extension communication failed'
    });
  }
}

/**
 * Handle embedded subtitle extraction request from webpage
 */
async function handleExtractRequest(message) {
  console.log('[SubMaker xSync] Extract request received:', {
    messageId: message.messageId,
    hasStreamUrl: !!message.data?.streamUrl
  });

  const { streamUrl, filename, videoHash, mode } = message.data || {};
  const normalizedMode = normalizeExtractModeValue(mode);
  const pageHeaders = {
    referer: window.location.href || null,
    cookie: document?.cookie || null,
    userAgent: navigator?.userAgent || null
  };

  if (!streamUrl) {
    throw new Error('Missing streamUrl in extract request');
  }
  if (!/^https?:\/\//i.test(streamUrl)) {
    throw new Error('Only http(s) stream URLs are supported');
  }

  sendExtractProgress(message.messageId, 2, 'Starting extraction...');

  try {
    console.log('[SubMaker xSync] Sending EXTRACT_SUBS_REQUEST to background...');
    const response = await sendRuntimeMessage({
      type: 'EXTRACT_SUBS_REQUEST',
      messageId: message.messageId,
      streamUrl,
      filename,
      videoHash,
      mode: normalizedMode,
      pageHeaders
    });

    console.log('[SubMaker xSync] Received response from background:', {
      success: response.success,
      trackCount: response.tracks?.length,
      error: response.error
    });

    clearPendingExtract(message.messageId);
    sendToPage({
      type: 'SUBMAKER_EXTRACT_RESPONSE',
      messageId: message.messageId,
      source: 'extension',
      success: response.success,
      tracks: response.tracks || [],
      error: response.error || null
    });
  } catch (error) {
    console.error('[SubMaker xSync] Extract request failed:', error);
    console.error('[SubMaker xSync] Error details:', {
      message: error.message,
      stack: error.stack
    });
    const errorMsg = error.message || translate('xsync.content.extractFailed', 'Extraction failed');
    if (isTransientPortError(error)) {
      schedulePendingExtractFailure(message.messageId, errorMsg);
      return;
    }
    clearPendingExtract(message.messageId);
    sendToPage({
      type: 'SUBMAKER_EXTRACT_RESPONSE',
      messageId: message.messageId,
      source: 'extension',
      success: false,
      error: errorMsg
    });
  }
}

/**
 * Handle auto-subtitles request from webpage (Cloudflare via extension)
 */
async function handleAutoSubRequest(message) {
  console.log('[SubMaker xSync] Auto-sub request received:', {
    messageId: message.messageId,
    hasStreamUrl: !!message.data?.streamUrl
  });

  const { streamUrl, filename, model, sourceLanguage, diarization, useAssembly, assemblyApiKey, sendFullVideo, cfWindowSizeMb } = message.data || {};
  const pageHeaders = {
    referer: window.location.href || null,
    cookie: document?.cookie || null,
    userAgent: navigator?.userAgent || null
  };

  if (!streamUrl) {
    throw new Error('Missing streamUrl in auto-sub request');
  }
  if (!/^https?:\/\//i.test(streamUrl)) {
    throw new Error('Only http(s) stream URLs are supported');
  }

  try {
    const response = await sendRuntimeMessage({
      type: 'AUTOSUB_REQUEST',
      messageId: message.messageId,
      data: {
        streamUrl,
        filename,
        model,
        sourceLanguage,
        diarization,
        audioTrackIndex: message.data?.audioTrackIndex,
        cfAccountId: message.data?.cfAccountId || message.data?.accountId,
        cfToken: message.data?.cfToken || message.data?.token,
        useAssembly: useAssembly === true,
        assemblyApiKey: assemblyApiKey || '',
        sendFullVideo: sendFullVideo === true,
        cfWindowSizeMb: cfWindowSizeMb,
        pageHeaders
      }
    }, 'auto-subtitles');
  } catch (error) {
    console.error('[SubMaker xSync] Auto-sub request failed:', error);
    sendToPage({
      type: 'SUBMAKER_AUTOSUB_RESPONSE',
      messageId: message.messageId,
      source: 'extension',
      success: false,
      error: error.message || 'Auto-subtitles failed'
    });
  }
}

/**
 * Handle audio track selection from webpage for paused auto-sub flow
 */
async function handleAutoSubTrackSelection(message) {
  try {
    await sendRuntimeMessage({
      type: 'AUTOSUB_SELECT_TRACK',
      messageId: message.messageId,
      trackIndex: message.trackIndex
    }, 'auto-subtitles-select-track');
  } catch (error) {
    console.error('[SubMaker xSync] Auto-sub track selection failed to forward:', error);
  }
}

/**
 * Handle cleanup/reset from embedded subtitles page (e.g., refresh/unload)
 */
async function handleEmbeddedReset(message) {
  console.log('[SubMaker xSync] Embedded page requested cleanup:', message?.reason || 'unknown');
  try {
    await sendRuntimeMessage({
      type: 'RESET_EMBEDDED_PAGE',
      reason: message?.reason || 'page-reset'
    }, 'reset-embedded');
  } catch (error) {
    console.warn('[SubMaker xSync] Failed to forward reset to background:', error?.message || error);
  }
}

/**
 * Send progress update to webpage
 */
function sendProgressUpdate(messageId, progress, status) {
  sendToPage({
    type: 'SUBMAKER_SYNC_PROGRESS',
    messageId: messageId,
    source: 'extension',
    progress: progress,
    status: status
  });
}

/**
 * Send extraction progress update to webpage
 */
function sendExtractProgress(messageId, progress, status) {
  sendToPage({
    type: 'SUBMAKER_EXTRACT_PROGRESS',
    messageId,
    source: 'extension',
    progress,
    status
  });
}

/**
 * Send message to webpage
 */
function sendToPage(message) {
  window.postMessage(message, '*');
}

/**
 * Wrapper around chrome.runtime.sendMessage with detailed logging
 */
function sendRuntimeMessage(payload, debugLabel = 'runtime-message') {
  const attemptSend = (retry = false) => new Promise((resolve, reject) => {
    const startedAt = Date.now();
    chrome.runtime.sendMessage(payload, (response) => {
      const duration = Date.now() - startedAt;
      const lastErr = chrome.runtime.lastError;
      if (lastErr) {
        const msg = lastErr.message || 'Unknown sendMessage error';
        console.error(`[SubMaker xSync] sendMessage error (${debugLabel}) after ${duration}ms:`, msg);
        sendToPage({
          type: 'SUBMAKER_DEBUG_LOG',
          source: 'extension',
          messageId: payload?.messageId,
          level: 'error',
          text: `Runtime message failed (${debugLabel}): ${msg}`,
          ts: Date.now()
        });
        const shouldRetry = !retry && /message port closed|receiving end does not exist/i.test(msg);
        if (shouldRetry) {
          // Retry once after a brief delay to give the service worker time to wake up
          setTimeout(() => {
            attemptSend(true).then(resolve).catch(reject);
          }, 200);
          return;
        }
        reject(new Error(msg));
        return;
      }
      console.log(`[SubMaker xSync] sendMessage success (${debugLabel}) after ${duration}ms`, {
        hasResponse: typeof response !== 'undefined',
        success: response?.success,
        messageId: payload?.messageId
      });
      resolve(response);
    });
  });

  return attemptSend(false);
}

console.log('[SubMaker xSync] Content script initialized');
