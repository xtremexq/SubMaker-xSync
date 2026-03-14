/**
 * SubMaker xSync - Popup Script
 * Mirrors the configure page styling while tracking live stats.
 */

const SETTINGS_KEY = 'xsync-settings';
const DEFAULT_LOCALE = { lang: (navigator.language || 'en').split('-')[0], messages: {} };
let locale = DEFAULT_LOCALE;
const _popupBootTs = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
const FALLBACK_VERSION = '1.0.1'; // keep in sync with manifest; avoids runtime getManifest
const PUBLIC_BASE = 'https://submaker.elfhosted.com';
const DEFAULT_PATHS = {
    configure: '/configure',
    sync: '/subtitle-sync',
    toolbox: '/sub-toolbox'
};

const versionEl = document.getElementById('version');
const activeEl = document.getElementById('activeSyncs');
const totalEl = document.getElementById('totalSynced');
const engineLabelEl = document.getElementById('engineLabel');
const engineStateEl = document.getElementById('engineState');
const pulseFillEl = document.getElementById('pulseFill');
const themeToggleEl = document.getElementById('themeToggle');
const configureBtn = document.getElementById('configureBtn');
const settingsBtn = document.getElementById('settingsBtn');
const reloadBtn = document.getElementById('reloadBtn');
const openSyncPageBtn = document.getElementById('openSyncPage');
const openToolboxBtn = document.getElementById('openToolbox');
const resetExtensionBtn = document.getElementById('resetExtensionBtn');
const linkedHostUrlEl = document.getElementById('linkedHostUrl');
const toolsHeader = document.getElementById('toolsHeader');
const toolsSection = document.getElementById('toolsSection');

const THEME_KEY = 'xsync-theme';
const THEMES = ['light', 'dark', 'true-dark'];
let currentTheme = document.documentElement.getAttribute('data-theme') || 'light';
let refreshTimer = null;
let refreshMs = 5000;
let statsLoading = false;
let liveStatusEnabled = false; // avoid waking SW unless user opts in

init();

async function init() {
    console.log('[Popup][Timing] init start');
    // Apply bundled translations immediately (no network roundtrip).
    initLocale();
    // Snap theme from localStorage before any paint to avoid flash.
    const cachedTheme = safeGetTheme(true);
    if (cachedTheme) applyTheme(cachedTheme);

    setVersion();
    initThemeToggle();
    bindButtons();
    initToolsToggle();
    updateLinkedHost();

    // Do not touch chrome.* APIs on init to avoid waking the background.
    loadSettings(); // local-only

    // Mark init complete after first paint to better reflect perceived load.
    requestAnimationFrame(() => {
        const end = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
        console.log('[Popup][Timing] init complete in', (end - _popupBootTs).toFixed(1), 'ms');
    });
}

function t(key, vars = {}, fallback = '') {
    try {
        if (typeof window.t === 'function') {
            return window.t(key, vars, fallback || key);
        }
    } catch (_) {}
    const parts = String(key || '').split('.');
    let current = locale.messages || {};
    for (const part of parts) {
        if (current && Object.prototype.hasOwnProperty.call(current, part)) {
            current = current[part];
        } else {
            current = null;
            break;
        }
    }
    const template = (typeof current === 'string' && current) || fallback || key;
    return template.replace(/\{(\w+)\}/g, (match, k) => Object.prototype.hasOwnProperty.call(vars, k) ? vars[k] : match);
}

function initLocale() {
    const lang = (navigator.language || 'en').split('-')[0] || 'en';
    locale = { ...DEFAULT_LOCALE, lang };
    applyTranslations();
}

function applyTranslations() {
    try {
        if (document?.documentElement) {
            document.documentElement.lang = locale.lang || 'en';
        }
        document.title = t('xsync.popup.title', {}, 'SubMaker xSync');
    } catch (_) {}
    const brandIcon = document.getElementById('brandIcon');
    if (brandIcon) brandIcon.alt = t('xsync.popup.iconAlt', {}, 'SubMaker xSync icon');
    const brandTitle = document.getElementById('brandTitle');
    if (brandTitle) brandTitle.textContent = t('xsync.popup.title', {}, 'SubMaker xSync');
    if (engineLabelEl) engineLabelEl.textContent = t('xsync.popup.standingBy', {}, 'Standing by');
    const activeLabel = document.getElementById('activeLabel');
    if (activeLabel) activeLabel.textContent = t('xsync.popup.active', {}, 'Active');
    const totalLabel = document.getElementById('totalLabel');
    if (totalLabel) totalLabel.textContent = t('xsync.popup.total', {}, 'Total');

    const configureText = configureBtn?.querySelector('span');
    if (configureText) configureText.textContent = t('xsync.popup.configure', {}, 'Configure');
    const settingsText = settingsBtn?.querySelector('span');
    if (settingsText) settingsText.textContent = t('xsync.popup.settings', {}, 'Settings');
    const toolboxText = openToolboxBtn?.querySelector('span');
    if (toolboxText) toolboxText.textContent = t('xsync.popup.toolbox', {}, 'Toolbox');

    const toolsTitle = document.querySelector('.tools-title-text');
    if (toolsTitle) toolsTitle.textContent = t('xsync.popup.advanced', {}, 'Advanced');

    const toolLabels = document.querySelectorAll('.tool-row .tool-label');
    if (toolLabels && toolLabels.length >= 3) {
        const labelKeys = ['syncPage', 'connection', 'factoryReset'];
        toolLabels.forEach((el, idx) => {
            const key = labelKeys[idx] || '';
            el.textContent = t(`xsync.popup.${key}`, {}, el.textContent || '');
        });
    }
    const toolButtons = document.querySelectorAll('.tool-row .tool-action');
    toolButtons.forEach(btn => {
        const action = btn.classList.contains('danger') ? 'reset' : (btn.id === 'reloadBtn' ? 'reload' : 'open');
        btn.textContent = t(`xsync.popup.${action}`, {}, btn.textContent || '');
    });

    const footer = document.getElementById('footerCopy');
    if (footer) footer.textContent = t('xsync.popup.copyright', {}, 'SubMaker xSync © 2025');
}

function setVersion() {
    let ver = FALLBACK_VERSION;
    try { ver = chrome.runtime.getManifest().version; } catch (_) {}
    if (versionEl) versionEl.textContent = `v${ver}`;
}

function initThemeToggle() {
    const saved = safeGetTheme();
    applyTheme(saved || currentTheme);

    themeToggleEl?.addEventListener('click', () => {
        const idx = THEMES.indexOf(currentTheme);
        const next = THEMES[(idx + 1) % THEMES.length];
        applyTheme(next);
    });
}

function safeGetTheme(localOnly = false) {
    try {
        const local = localStorage.getItem(THEME_KEY);
        if (localOnly) return local;
        return local;
    } catch (error) {
        console.warn('Could not load saved theme', error);
        return null;
    }
}

function applyTheme(theme) {
    const resolved = theme === 'system' ? detectSystemTheme() : theme;
    currentTheme = resolved || 'light';
    document.documentElement.setAttribute('data-theme', currentTheme);
    if (themeToggleEl) {
        themeToggleEl.dataset.theme = theme || currentTheme;
        const aria = t('xsync.popup.themeAria', { theme: currentTheme }, `Theme: ${currentTheme}`);
        themeToggleEl.setAttribute('aria-label', aria);
    }
    try {
        localStorage.setItem(THEME_KEY, theme || currentTheme);
    } catch (_) {
        // Ignore storage failures in private mode
    }
}

function detectSystemTheme() {
    return window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

function bindButtons() {
    settingsBtn?.addEventListener('click', openSettings);
    configureBtn?.addEventListener('click', openConfigure);

    resetExtensionBtn?.addEventListener('click', resetExtension);
    reloadBtn?.addEventListener('click', () => {
        enableLiveStatus();
    });

    openSyncPageBtn?.addEventListener('click', async () => {
        const target = await resolveTargetUrl('sync');
        if (target) window.open(target, '_blank');
    });

    openToolboxBtn?.addEventListener('click', async () => {
        const target = await resolveTargetUrl('toolbox');
        if (target) window.open(target, '_blank');
    });
}

function initToolsToggle() {
    toolsHeader?.addEventListener('click', () => {
        toolsSection.classList.toggle('open');
    });
}

async function openSettings() {
    const target = await resolveTargetUrl('configure');
    if (!target) return;

    if (chrome.runtime.openOptionsPage) {
        chrome.runtime.openOptionsPage(() => {
            if (chrome.runtime.lastError) {
                window.open(target, '_blank');
            }
        });
    } else {
        window.open(target, '_blank');
    }
}

async function openConfigure(event) {
    event?.preventDefault();
    const target = await resolveTargetUrl('configure');
    if (target) window.open(target, '_blank');
}

async function getStoredUrls() {
    try {
        const data = await chrome.storage.local.get(['toolboxUrl', 'configureUrl', 'syncUrl']);
        return {
            toolbox: data.toolboxUrl,
            configure: data.configureUrl,
            sync: data.syncUrl
        };
    } catch (e) {
        return {};
    }
}

function getDefaultUrl(kind) {
    const path = DEFAULT_PATHS[kind] || '';
    return `${PUBLIC_BASE}${path}`;
}

function safeOrigin(url) {
    try {
        return new URL(url).origin;
    } catch (_) {
        return null;
    }
}

async function checkHealth(origin) {
    if (!origin) return false;
    const controller = typeof AbortController !== 'undefined' ? new AbortController() : null;
    const timer = controller ? setTimeout(() => controller.abort(), 1500) : null;
    try {
        const res = await fetch(`${origin}/health`, { cache: 'no-store', signal: controller?.signal });
        return res.ok;
    } catch (_) {
        return false;
    } finally {
        if (timer) clearTimeout(timer);
    }
}

async function resolveTargetUrl(kind) {
    const urls = await getStoredUrls();
    const stored = urls[kind];
    const fallback = getDefaultUrl(kind);
    let target = stored || fallback;
    const origin = safeOrigin(target);
    const reachable = await checkHealth(origin);

    // If nothing was captured yet, always prompt before using the hosted default.
    if (!stored) {
        const msg = reachable
            ? 'Use the hosted SubMaker setup now? (Choose “No” if you want to start your own server first.)'
            : 'SubMaker is not reachable. Start your SubMaker or open the hosted setup?';
        const proceed = confirm(msg);
        if (!proceed) return null;
        try {
            const update = {};
            update[`${kind}Url`] = fallback;
            await chrome.storage.local.set(update);
        } catch (_) { /* ignore */ }
        return fallback;
    }

    // If we have a stored URL but it is unreachable, offer to switch to hosted.
    if (!reachable) {
        const switchMsg = 'SubMaker is not reachable. Switch to the hosted setup?';
        const useHosted = confirm(switchMsg);
        if (!useHosted) return null;
        target = fallback;
        try {
            const update = {};
            update[`${kind}Url`] = fallback;
            await chrome.storage.local.set(update);
        } catch (_) { /* ignore */ }
    }

    return target;
}

async function updateLinkedHost() {
    try {
        const urls = await getStoredUrls();
        const raw = urls.configure || PUBLIC_BASE;
        const parsed = new URL(raw);
        if (linkedHostUrlEl) linkedHostUrlEl.textContent = parsed.host;
    } catch (_) {
        if (linkedHostUrlEl) linkedHostUrlEl.textContent = new URL(PUBLIC_BASE).host;
    }
}

async function resetExtension() {
    if (!confirm(t('xsync.popup.resetConfirm', {}, 'Are you sure you want to reset the extension? This will clear all settings and data.'))) {
        return;
    }
    try {
        await chrome.storage.local.clear();
        await chrome.storage.sync.clear();
        chrome.runtime.reload();
    } catch (error) {
        console.error('Failed to reset extension:', error);
        alert(t('xsync.popup.resetFailed', {}, 'Failed to reset extension. Please try removing and reinstalling it.'));
    }
}

async function loadSettings() {
    const started = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
    try {
        let settings = {};
        // Local-only (no chrome.*) to avoid waking SW
        const raw = localStorage.getItem(SETTINGS_KEY);
        if (raw) {
            try { settings = JSON.parse(raw); } catch (_) { settings = {}; }
        }

        if (settings.theme) {
            applyTheme(settings.theme);
        }
    } catch (error) {
        console.warn('Could not load popup settings', error);
    } finally {
        const now = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
        console.log('[Popup][Timing] settings applied in', (now - started).toFixed(1), 'ms (async)');
    }
}

function startRefreshLoop() {
    refreshTimer = setInterval(loadStatistics, refreshMs);
}

function restartRefreshLoop() {
    if (refreshTimer) clearInterval(refreshTimer);
    startRefreshLoop();
}

async function loadStatistics() {
    if (!liveStatusEnabled) return; // do not wake SW unless user opted in
    if (statsLoading) return;
    statsLoading = true;
    const start = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
    try {
        // Get live status from background (explicit opt-in)
        const sendTs = Date.now();
        console.log('[Popup][Timing] GET_STATUS send at', sendTs);
        chrome.runtime.sendMessage({ type: 'GET_STATUS' }, (response) => {
            if (chrome.runtime.lastError) {
                updateStats({ activeSyncs: 0, totalSynced: 0 });
                console.log('[Popup][Timing] GET_STATUS error', chrome.runtime.lastError.message);
            } else {
                updateStats({
                    activeSyncs: response?.active || 0,
                    totalSynced: 0
                });
            }
            console.log('[Popup][Timing] GET_STATUS roundtrip', Date.now() - sendTs, 'ms');
        });
    } catch (error) {
        console.error('Failed to load statistics:', error);
    } finally {
        const end = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
        console.log('[Popup][Timing] loadStatistics completed in', (end - start).toFixed(1), 'ms');
        statsLoading = false;
    }
}

// Allow users/actions to enable live status on demand without blocking first paint.
function enableLiveStatus() {
    if (liveStatusEnabled) return;
    liveStatusEnabled = true;
    restartRefreshLoop();
    loadStatistics();
}

function updateStats({ activeSyncs = 0, totalSynced = 0 } = {}) {
    const active = Number(activeSyncs) || 0;
    const total = Number(totalSynced) || 0;

    if (activeEl) activeEl.textContent = active;
    if (totalEl) totalEl.textContent = total;

    const busy = active > 0;
    if (engineLabelEl) engineLabelEl.textContent = busy ? t('xsync.popup.engineBusy', {}, 'Syncing now') : t('xsync.popup.engineIdle', {}, 'Standing by');

    engineStateEl?.classList.toggle('busy', busy);
    pulseFillEl?.classList.toggle('active', busy);

    if (pulseFillEl) {
        // In the new design, width is controlled by CSS class 'active' which sets it to 100% with animation
        // But we can also set it explicitly if needed, though CSS animation is smoother
        pulseFillEl.style.width = busy ? '100%' : '0%';
    }
}
