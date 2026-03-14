const DEFAULTS = {
  autoSync: true,
  theme: 'light',
  refreshInterval: 5,
  preferAlass: true,
  concurrencyLimit: 2,
  fallbackBehavior: 'retry',
  quietMode: false,
  endpoint: 'http://localhost:7001',
  detectPages: true,
  offscreenEnabled: true,
  notifyStart: true,
  notifySuccess: true,
  notifyError: true,
  notifySound: false,
  quietHours: false,
  quietStart: '22:00',
  quietEnd: '07:00',
  streamBufferMode: 'disk',
  lastSavedAt: null
};

const STORAGE_KEY = 'xsync-settings';
const THEME_KEY = 'xsync-theme';
const THEMES = ['light', 'dark', 'true-dark'];
const STATUS_REFRESH_MS = 5000;
const DEFAULT_LOCALE = { lang: (typeof chrome !== 'undefined' && chrome.i18n?.getUILanguage ? chrome.i18n.getUILanguage().split('-')[0] : 'en'), messages: {} };
let locale = DEFAULT_LOCALE;

const $ = (id) => document.getElementById(id);

const els = {
  version: $('versionBadge'),
  status: $('statusLabel'),
  statusDot: $('statusDot'),
  lastSaved: $('lastSaved'),
  lastSavedDot: $('lastSavedDot'),
  themeToggle: $('themeToggle'),
  toast: $('toast'),
  importFile: $('importFile'),
  saveBtn: $('saveBtn'),
  toolbox: $('toolboxBadge'),
  toolboxDot: $('toolboxDot'),
  configure: $('configureBadge'),
  configureDot: $('configureDot')
};

let statusTimer = null;

document.addEventListener('DOMContentLoaded', () => {
  initLocale();
  setVersion();
  wireThemeToggle();
  wireForm();
  wireActions();
  setLinkState(els.toolbox, null);
  setLinkState(els.configure, null);
  hydrate();
  hydrateKnownUrls();
});

function t(key, vars = {}, fallback = '') {
  const chromeMsg = getChromeMessage(key);
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
  const template = chromeMsg || (typeof current === 'string' && current) || fallback || key;
  return template.replace(/\{(\w+)\}/g, (match, k) => Object.prototype.hasOwnProperty.call(vars, k) ? vars[k] : match);
}

const tOpt = (key, fallback = '') => t(`xsync.options.${key}`, {}, fallback);

function getChromeMessage(key) {
  try {
    if (typeof chrome !== 'undefined' && chrome.i18n?.getMessage) {
      const chromeKey = String(key || '').replace(/[^a-zA-Z0-9_]/g, '_');
      return chrome.i18n.getMessage(chromeKey) || '';
    }
  } catch (_) {}
  return '';
}

function initLocale() {
  // Use bundled Chrome i18n locale; no network fetch required.
  const lang = (navigator.language || 'en').split('-')[0] || 'en';
  locale = { ...DEFAULT_LOCALE, lang };
  try {
    if (document?.documentElement) {
      document.documentElement.lang = locale.lang || 'en';
    }
  } catch (_) {}
  applyTranslations();
}

function applyTranslations() {
  try {
    if (document?.documentElement) {
      document.documentElement.lang = locale.lang || 'en';
    }
    document.title = tOpt('title', 'SubMaker xSync Settings');
  } catch (_) {}
  const heroTitle = document.getElementById('heroTitle');
  if (heroTitle) heroTitle.textContent = tOpt('title', 'SubMaker xSync Settings');
  const heroSubtitle = document.getElementById('heroSubtitle');
  if (heroSubtitle) heroSubtitle.textContent = tOpt('subtitle', 'Settings & Configuration');

  const statusLabelTitle = document.getElementById('statusLabelTitle');
  if (statusLabelTitle) statusLabelTitle.textContent = tOpt('status', 'Status');
  const configureLabel = document.getElementById('configureLabel');
  if (configureLabel) configureLabel.textContent = tOpt('configure', 'Configure');
  const toolboxLabel = document.getElementById('toolboxLabel');
  if (toolboxLabel) toolboxLabel.textContent = tOpt('toolbox', 'Toolbox');
  const lastSavedLabel = document.getElementById('lastSavedLabel');
  if (lastSavedLabel) lastSavedLabel.textContent = tOpt('lastSave', 'Last Save');
  const configureBadge = document.getElementById('configureBadge');
  if (configureBadge) configureBadge.textContent = t('xsync.options.notCaptured', {}, 'Not captured');
  const toolboxBadge = document.getElementById('toolboxBadge');
  if (toolboxBadge) toolboxBadge.textContent = t('xsync.options.notCaptured', {}, 'Not captured');
  const lastSaved = document.getElementById('lastSaved');
  if (lastSaved) lastSaved.textContent = t('xsync.options.notYet', {}, 'Not yet');

  const generalEyebrow = document.getElementById('generalEyebrow');
  if (generalEyebrow) generalEyebrow.textContent = t('xsync.options.generalEyebrow', {}, 'General');
  const generalTitle = document.getElementById('generalTitle');
  if (generalTitle) generalTitle.textContent = t('xsync.options.generalTitle', {}, 'Global Behaviour');
  const autoSyncLabel = document.getElementById('autoSyncLabel');
  if (autoSyncLabel) autoSyncLabel.textContent = t('xsync.options.autoSync', {}, 'Auto Sync');
  const autoSyncHint = document.getElementById('autoSyncHint');
  if (autoSyncHint) autoSyncHint.textContent = t('xsync.options.autoSyncHint', {}, 'Keep automatic syncing active whenever SubMaker is detected.');

  const themePreferenceLabel = document.getElementById('themePreferenceLabel');
  if (themePreferenceLabel) themePreferenceLabel.textContent = t('xsync.options.themePreference', {}, 'Theme Preference');
  const themeToggleButton = document.getElementById('themeToggle');
  if (themeToggleButton) {
    const aria = tOpt('themeToggleAria', 'Toggle theme');
    themeToggleButton.setAttribute('aria-label', aria);
    themeToggleButton.title = aria;
  }
  const themeLightLabel = document.getElementById('themeLightLabel');
  if (themeLightLabel) themeLightLabel.textContent = tOpt('themeLight', 'Light');
  const themeDarkLabel = document.getElementById('themeDarkLabel');
  if (themeDarkLabel) themeDarkLabel.textContent = tOpt('themeDark', 'Dark');
  const themeTrueDarkLabel = document.getElementById('themeTrueDarkLabel');
  if (themeTrueDarkLabel) themeTrueDarkLabel.textContent = tOpt('themeTrueDark', 'True Dark');

  const streamBufferModeLabel = document.getElementById('streamBufferModeLabel');
  if (streamBufferModeLabel) streamBufferModeLabel.textContent = tOpt('streamBufferMode', 'Stream Buffer Mode');
  const streamBufferModeHint = document.getElementById('streamBufferModeHint');
  if (streamBufferModeHint) streamBufferModeHint.textContent = tOpt('streamBufferModeHint', 'How large downloads are buffered. Disk is safer for big files; RAM is faster but may crash on files >2 GB.');
  const streamBufferDisk = document.getElementById('streamBufferDisk');
  if (streamBufferDisk) streamBufferDisk.textContent = tOpt('streamBufferDisk', 'Disk (default)');
  const streamBufferRam = document.getElementById('streamBufferRam');
  if (streamBufferRam) streamBufferRam.textContent = tOpt('streamBufferRam', 'RAM');
  const syncEyebrow = document.getElementById('syncEyebrow');
  if (syncEyebrow) syncEyebrow.textContent = tOpt('syncEyebrow', 'Sync Behaviour');
  const syncTitle = document.getElementById('syncTitle');
  if (syncTitle) syncTitle.textContent = tOpt('syncTitle', 'Automation & Safety');
  const preferAlassLabel = document.getElementById('preferAlassLabel');
  if (preferAlassLabel) preferAlassLabel.textContent = tOpt('preferAlass', 'Prefer ALASS');
  const preferAlassHint = document.getElementById('preferAlassHint');
  if (preferAlassHint) preferAlassHint.textContent = tOpt('preferAlassHint', 'Favour ALASS when available for higher-accuracy alignment.');
  const concurrencyLabel = document.getElementById('concurrencyLabel');
  if (concurrencyLabel) concurrencyLabel.textContent = tOpt('concurrency', 'Concurrency');
  const concurrencyHint = document.getElementById('concurrencyHint');
  if (concurrencyHint) concurrencyHint.textContent = tOpt('concurrencyHint', 'Prevent overload when multiple tabs sync at once.');
  const concurrencyOption1 = document.getElementById('concurrencyOption1');
  if (concurrencyOption1) concurrencyOption1.textContent = tOpt('concurrencyOption1', 'Single job');
  const concurrencyOption2 = document.getElementById('concurrencyOption2');
  if (concurrencyOption2) concurrencyOption2.textContent = tOpt('concurrencyOption2', 'Up to 2 jobs');
  const concurrencyOption3 = document.getElementById('concurrencyOption3');
  if (concurrencyOption3) concurrencyOption3.textContent = tOpt('concurrencyOption3', 'Up to 3 jobs');
  const concurrencyOption4 = document.getElementById('concurrencyOption4');
  if (concurrencyOption4) concurrencyOption4.textContent = tOpt('concurrencyOption4', 'Up to 4 jobs');
  const fallbackLabel = document.getElementById('fallbackLabel');
  if (fallbackLabel) fallbackLabel.textContent = tOpt('fallbackBehavior', 'Fallback Behaviour');
  const fallbackHint = document.getElementById('fallbackHint');
  if (fallbackHint) fallbackHint.textContent = tOpt('fallbackHint', 'How to handle hiccups during background syncing.');
  const fallbackOptionRetry = document.getElementById('fallbackOptionRetry');
  if (fallbackOptionRetry) fallbackOptionRetry.textContent = tOpt('fallbackOptionRetry', 'Retry quietly');
  const fallbackOptionManual = document.getElementById('fallbackOptionManual');
  if (fallbackOptionManual) fallbackOptionManual.textContent = tOpt('fallbackOptionManual', 'Prompt me');
  const fallbackOptionSkip = document.getElementById('fallbackOptionSkip');
  if (fallbackOptionSkip) fallbackOptionSkip.textContent = tOpt('fallbackOptionSkip', 'Skip failed sync');
  const quietModeLabel = document.getElementById('quietModeLabel');
  if (quietModeLabel) quietModeLabel.textContent = tOpt('quietMode', 'Quiet Mode');
  const quietModeHint = document.getElementById('quietModeHint');
  if (quietModeHint) quietModeHint.textContent = tOpt('quietModeHint', 'Pause automatic sync until re-enabled.');

  const integrationsEyebrow = document.getElementById('integrationsEyebrow');
  if (integrationsEyebrow) integrationsEyebrow.textContent = tOpt('integrationsEyebrow', 'Integrations');
  const integrationsTitle = document.getElementById('integrationsTitle');
  if (integrationsTitle) integrationsTitle.textContent = tOpt('integrationsTitle', 'SubMaker Link');
  const detectPagesLabel = document.getElementById('detectPagesLabel');
  if (detectPagesLabel) detectPagesLabel.textContent = tOpt('detectPages', 'Detect SubMaker Pages');
  const detectPagesHint = document.getElementById('detectPagesHint');
  if (detectPagesHint) detectPagesHint.textContent = tOpt('detectPagesHint', 'Listen for the sync page to auto-connect.');
  const offscreenLabel = document.getElementById('offscreenLabel');
  if (offscreenLabel) offscreenLabel.textContent = tOpt('offscreenWorker', 'Offscreen Worker');
  const offscreenHint = document.getElementById('offscreenHint');
  if (offscreenHint) offscreenHint.textContent = tOpt('offscreenHint', 'Allow the offscreen document for processing.');

  const notificationsEyebrow = document.getElementById('notificationsEyebrow');
  if (notificationsEyebrow) notificationsEyebrow.textContent = tOpt('notificationsEyebrow', 'Notifications');
  const notificationsTitle = document.getElementById('notificationsTitle');
  if (notificationsTitle) notificationsTitle.textContent = tOpt('notificationsTitle', 'Signals & Quiet Hours');
  const notifyStartLabel = document.getElementById('notifyStartLabel');
  if (notifyStartLabel) notifyStartLabel.textContent = tOpt('notifyStart', 'On Start');
  const notifyStartHint = document.getElementById('notifyStartHint');
  if (notifyStartHint) notifyStartHint.textContent = tOpt('notifyStartHint', 'Show a toast when a sync kicks off.');
  const notifySuccessLabel = document.getElementById('notifySuccessLabel');
  if (notifySuccessLabel) notifySuccessLabel.textContent = tOpt('notifySuccess', 'On Success');
  const notifySuccessHint = document.getElementById('notifySuccessHint');
  if (notifySuccessHint) notifySuccessHint.textContent = tOpt('notifySuccessHint', 'Celebrate when a sync finishes.');
  const notifyErrorLabel = document.getElementById('notifyErrorLabel');
  if (notifyErrorLabel) notifyErrorLabel.textContent = tOpt('notifyError', 'On Error');
  const notifyErrorHint = document.getElementById('notifyErrorHint');
  if (notifyErrorHint) notifyErrorHint.textContent = tOpt('notifyErrorHint', 'Surface issues immediately.');
  const notifySoundLabel = document.getElementById('notifySoundLabel');
  if (notifySoundLabel) notifySoundLabel.textContent = tOpt('notifySound', 'Sounds');
  const notifySoundHint = document.getElementById('notifySoundHint');
  if (notifySoundHint) notifySoundHint.textContent = tOpt('notifySoundHint', 'Play subtle cues with notifications.');
  const quietHoursLabel = document.getElementById('quietHoursLabel');
  if (quietHoursLabel) quietHoursLabel.textContent = tOpt('quietHours', 'Quiet Hours');
  const quietHoursHint = document.getElementById('quietHoursHint');
  if (quietHoursHint) quietHoursHint.textContent = tOpt('quietHoursHint', 'Mute notifications during a window.');
  const quietStartLabel = document.getElementById('quietStartLabel');
  if (quietStartLabel) quietStartLabel.textContent = tOpt('quietStart', 'Quiet Start');
  const quietEndLabel = document.getElementById('quietEndLabel');
  if (quietEndLabel) quietEndLabel.textContent = tOpt('quietEnd', 'Quiet End');

  const supportEyebrow = document.getElementById('supportEyebrow');
  if (supportEyebrow) supportEyebrow.textContent = tOpt('supportEyebrow', 'Support & Data');
  const supportTitle = document.getElementById('supportTitle');
  if (supportTitle) supportTitle.textContent = tOpt('supportTitle', 'Backups, Resets, Diagnostics');
  const exportBtn = document.getElementById('exportBtn');
  if (exportBtn) exportBtn.textContent = tOpt('export', 'Export Settings');
  const importBtn = document.getElementById('importBtn');
  if (importBtn) importBtn.textContent = tOpt('import', 'Import Settings');
  const clearStatsBtn = document.getElementById('clearStatsBtn');
  if (clearStatsBtn) clearStatsBtn.textContent = tOpt('resetStats', 'Reset Stats');
  const resetBtn = document.getElementById('resetBtn');
  if (resetBtn) resetBtn.textContent = tOpt('resetDefaults', 'Reset to Defaults');
  const supportHint = document.getElementById('supportHint');
  if (supportHint) supportHint.textContent = tOpt('supportHint', 'Exports are JSON. Stats reset only clears popup metrics (active/total).');

  const saveEyebrow = document.getElementById('saveEyebrow');
  if (saveEyebrow) saveEyebrow.textContent = tOpt('saveEyebrow', 'Save');
  const saveSubline = document.getElementById('saveSubline');
  if (saveSubline) saveSubline.textContent = tOpt('saveSubline', 'Applies instantly across the extension.');
  const saveBtn = document.getElementById('saveBtn');
  if (saveBtn) saveBtn.textContent = t('xsync.options.saveButton', {}, 'Save Settings');
}

function setVersion() {
  try {
    const version = chrome.runtime.getManifest().version;
    if (els.version) els.version.textContent = version;
  } catch (error) {
    console.error('Could not read manifest version', error);
  }
}

function wireThemeToggle() {
  const savedChoice = readThemePreference() || 'light';
  applyTheme(savedChoice);

  els.themeToggle?.addEventListener('click', () => {
    const currentChoice = document.documentElement.getAttribute('data-theme') || 'light';
    const idx = THEMES.indexOf(currentChoice);
    const nextChoice = THEMES[(idx + 1) % THEMES.length];
    applyTheme(nextChoice);
  });
}

function readThemePreference() {
  try {
    return localStorage.getItem(THEME_KEY);
  } catch (_) {
    return null;
  }
}

function applyTheme(theme) {
  const chosen = THEMES.includes(theme) ? theme : 'light';
  
  document.documentElement.setAttribute('data-theme', chosen);
  
  if (els.themeToggle) {
    els.themeToggle.dataset.theme = chosen;
    const ariaLabel = tOpt('themeAria', 'Theme: {theme}').replace('{theme}', chosen);
    els.themeToggle.setAttribute('aria-label', ariaLabel);
  }
  
  try {
    localStorage.setItem(THEME_KEY, chosen);
  } catch (_) {
    // ignore private mode failures
  }
  
  selectThemeRadio(chosen);
}

function selectThemeRadio(theme) {
  const radios = document.querySelectorAll('input[name="theme"]');
  radios.forEach((radio) => {
    const isActive = radio.value === theme;
    radio.checked = isActive;
    radio.parentElement.classList.toggle('active', isActive);
  });
}

function wireForm() {
  document.querySelectorAll('.pill-select input').forEach((input) => {
    input.addEventListener('change', () => {
      document.querySelectorAll('.pill-select').forEach((p) => p.classList.remove('active'));
      if (input.checked) {
        input.parentElement.classList.add('active');
        applyTheme(input.value);
      }
    });
  });

  $('settingsForm')?.addEventListener('submit', async (e) => {
    e.preventDefault();
    await saveSettings();
  });
}

function wireActions() {
  $('exportBtn')?.addEventListener('click', exportSettings);
  $('importBtn')?.addEventListener('click', () => els.importFile?.click());
  $('resetBtn')?.addEventListener('click', resetDefaults);
  $('clearStatsBtn')?.addEventListener('click', clearStats);
  els.importFile?.addEventListener('change', handleImportFile);
}

async function hydrate() {
  try {
    const stored = await chrome.storage.sync.get(STORAGE_KEY);
    const data = { ...DEFAULTS, ...(stored?.[STORAGE_KEY] || {}) };
    populate(data);
    setLastSaved(data.lastSavedAt);
    updateStatus(tOpt('statusReady', 'Ready'), 'online');
  } catch (error) {
    console.error('Failed to load settings', error);
    updateStatus(tOpt('statusLoadingError', 'Error loading'), 'offline', true);
    showToast(tOpt('loadError', 'Could not load settings'), true);
  } finally {
    refreshRuntimeStatus();
    startStatusPolling();
  }
}

function populate(data) {
  $('autoSync').checked = !!data.autoSync;
  $('preferAlass').checked = !!data.preferAlass;
  $('concurrencyLimit').value = String(data.concurrencyLimit ?? DEFAULTS.concurrencyLimit);
  $('fallbackBehavior').value = data.fallbackBehavior || DEFAULTS.fallbackBehavior;
  $('quietMode').checked = !!data.quietMode;
  // Endpoint removed from UI
  $('detectPages').checked = !!data.detectPages;
  $('offscreenEnabled').checked = !!data.offscreenEnabled;
  $('notifyStart').checked = !!data.notifyStart;
  $('notifySuccess').checked = !!data.notifySuccess;
  $('notifyError').checked = !!data.notifyError;
  $('notifySound').checked = !!data.notifySound;
  $('quietHours').checked = !!data.quietHours;
  $('quietStart').value = data.quietStart || DEFAULTS.quietStart;
  $('quietEnd').value = data.quietEnd || DEFAULTS.quietEnd;
  $('streamBufferMode').value = data.streamBufferMode || DEFAULTS.streamBufferMode;

  applyTheme(data.theme || DEFAULTS.theme);
}

function collectForm() {
  return {
    autoSync: $('autoSync').checked,
    theme: getSelectedTheme(),
    refreshInterval: DEFAULTS.refreshInterval,
    preferAlass: $('preferAlass').checked,
    concurrencyLimit: Number($('concurrencyLimit')?.value) || DEFAULTS.concurrencyLimit,
    fallbackBehavior: $('fallbackBehavior')?.value || DEFAULTS.fallbackBehavior,
    quietMode: $('quietMode').checked,
    endpoint: DEFAULTS.endpoint, // Always use default since UI is removed
    detectPages: $('detectPages').checked,
    offscreenEnabled: $('offscreenEnabled').checked,
    notifyStart: $('notifyStart').checked,
    notifySuccess: $('notifySuccess').checked,
    notifyError: $('notifyError').checked,
    notifySound: $('notifySound').checked,
    quietHours: $('quietHours').checked,
    quietStart: $('quietStart')?.value || DEFAULTS.quietStart,
    quietEnd: $('quietEnd')?.value || DEFAULTS.quietEnd,
    streamBufferMode: $('streamBufferMode')?.value || DEFAULTS.streamBufferMode
  };
}

function getSelectedTheme() {
  const checked = document.querySelector('input[name="theme"]:checked');
  return checked ? checked.value : DEFAULTS.theme;
}

async function saveSettings() {
  const payload = collectForm();
  const savedAt = Date.now();
  payload.lastSavedAt = savedAt;
  setSaving(true);
  try {
    await chrome.storage.sync.set({ [STORAGE_KEY]: payload });
    updateStatus(tOpt('saveSuccess', 'Saved'), 'online');
    setLastSaved(savedAt);
    showToast(t('xsync.options.saveSuccess', {}, 'Settings saved'));
    applyTheme(payload.theme);
  } catch (error) {
    console.error('Save failed', error);
    updateStatus(tOpt('saveError', 'Save failed'), 'offline', true);
    showToast(t('xsync.options.saveError', {}, 'Failed to save settings'), true);
  } finally {
    setSaving(false);
  }
}

function setSaving(state) {
  if (!els.saveBtn) return;
  els.saveBtn.disabled = state;
  els.saveBtn.textContent = state ? tOpt('saving', 'Saving') : tOpt('saveButton', 'Save Settings');
}

function updateStatus(text, state = 'idle', isError = false) {
  let resolvedState = state;
  let errorFlag = isError;
  if (typeof state === 'boolean') {
    errorFlag = state;
    resolvedState = errorFlag ? 'offline' : 'online';
  }
  if (els.status) {
    els.status.textContent = text;
    els.status.style.color = errorFlag ? '#ef4444' : 'inherit';
  }
  setDotState(els.statusDot, errorFlag ? 'offline' : resolvedState);
}

function showToast(message, isError = false) {
  if (!els.toast) return;
  els.toast.textContent = message;
  els.toast.classList.toggle('error', isError);
  els.toast.classList.add('show');
  setTimeout(() => els.toast?.classList.remove('show'), 2000);
}

async function exportSettings() {
  try {
    const payload = collectForm();
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'submaker-xsync-settings.json';
    a.click();
    URL.revokeObjectURL(url);
    showToast(tOpt('exported', 'Exported settings'));
  } catch (error) {
    console.error('Export failed', error);
    showToast(tOpt('exportFailed', 'Export failed'), true);
  }
}

function handleImportFile(event) {
  const file = event.target.files?.[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = async () => {
    try {
      const parsed = JSON.parse(reader.result);
      const merged = { ...DEFAULTS, ...parsed, lastSavedAt: Date.now() };
      await chrome.storage.sync.set({ [STORAGE_KEY]: merged });
      populate(merged);
      showToast(tOpt('imported', 'Imported settings'));
      updateStatus(tOpt('statusImported', 'Imported'), 'online');
      setLastSaved(merged.lastSavedAt);
    } catch (error) {
    console.error('Import failed', error);
    showToast(tOpt('importFailed', 'Import failed'), true);
    updateStatus(tOpt('statusImportFailed', 'Import failed'), 'offline', true);
  } finally {
    event.target.value = '';
  }
  };
  reader.readAsText(file);
}

async function resetDefaults() {
  if (!confirm(tOpt('resetConfirm', 'Are you sure you want to reset the extension? This will clear all settings and data.'))) return;
  try {
    await chrome.storage.local.clear();
    await chrome.storage.sync.clear();
    showToast(tOpt('resetSuccess', 'Extension reset; reloading...'));
    updateStatus(tOpt('statusResetting', 'Resetting...'), 'idle');
    chrome.runtime.reload();
  } catch (error) {
    console.error('Reset failed', error);
    showToast(tOpt('resetFailed', 'Reset failed'), true);
    updateStatus(tOpt('statusResetFailed', 'Reset failed'), 'offline', true);
  }
}

async function clearStats() {
  if (!confirm(tOpt('clearStatsConfirm', 'Reset popup stats (active/total sync counters)?'))) return;
  try {
    await chrome.storage.local.set({ activeSyncs: 0, totalSynced: 0 });
    showToast(tOpt('statsReset', 'Stats reset'));
  } catch (error) {
    console.error('Failed to reset stats', error);
    showToast(tOpt('statsResetFailed', 'Could not reset stats'), true);
  }
}

async function refreshRuntimeStatus() {
  try {
    const response = await sendRuntimeMessage({ type: 'GET_STATUS' });
    const active = Number(response?.active) || 0;
    const extracting = Number(response?.extracting) || 0;
    const busy = active > 0 || extracting > 0;
    const parts = [];
    if (active) parts.push(t('xsync.options.statusActiveCount', { count: active }, `${active} syncing`));
    if (extracting) parts.push(t('xsync.options.statusExtractingCount', { count: extracting }, `${extracting} extracting`));
    const label = busy ? parts.join(' / ') : tOpt('statusIdle', 'Idle');
    updateStatus(label || tOpt('statusIdle', 'Idle'), busy ? 'online' : 'idle');
  } catch (error) {
    console.warn('Could not refresh runtime status', error);
    updateStatus(tOpt('statusOffline', 'Offline'), 'offline', true);
  }
}

function startStatusPolling() {
  if (statusTimer) clearInterval(statusTimer);
  statusTimer = setInterval(refreshRuntimeStatus, STATUS_REFRESH_MS);
}

function sendRuntimeMessage(message) {
  return new Promise((resolve, reject) => {
    try {
      chrome.runtime.sendMessage(message, (response) => {
        if (chrome.runtime.lastError) {
          return reject(chrome.runtime.lastError);
        }
        resolve(response);
      });
    } catch (error) {
      reject(error);
    }
  });
}

function setLastSaved(timestamp) {
  if (!els.lastSaved) return;
  if (!timestamp) {
    els.lastSaved.textContent = tOpt('notYet', 'Not yet');
    setDotState(els.lastSavedDot, 'offline');
    return;
  }
  const date = new Date(timestamp);
  if (Number.isNaN(date.getTime())) {
    els.lastSaved.textContent = tOpt('lastSavedUnknown', 'Unknown');
    setDotState(els.lastSavedDot, 'offline');
    return;
  }
  els.lastSaved.textContent = date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
  setDotState(els.lastSavedDot, 'online');
}

async function hydrateKnownUrls() {
  try {
    const data = await chrome.storage.local.get(['toolboxUrl', 'configureUrl', 'syncUrl']);
    setUrlBadge(els.toolbox, els.toolboxDot, data.toolboxUrl);
    setUrlBadge(els.configure, els.configureDot, data.configureUrl);
  } catch (error) {
    console.warn('Could not hydrate known URLs', error);
    setUrlBadge(els.toolbox, els.toolboxDot, null);
    setUrlBadge(els.configure, els.configureDot, null);
  }
}

function setUrlBadge(el, dotEl, url) {
  if (!el) return;
  if (!url) {
    el.textContent = t('xsync.options.notCaptured', {}, 'Not captured');
    el.removeAttribute('title');
    setLinkState(el, null);
    setDotState(dotEl, 'offline');
    return;
  }
  const host = safeHostname(url);
  el.textContent = host || url;
  el.title = url;
  setLinkState(el, url);
  setDotState(dotEl, 'online');
}

function setLinkState(el, url) {
  const isLink = el.tagName === 'A';
  if (!isLink) return;
  if (!url) {
    el.removeAttribute('href');
    el.classList.remove('clickable');
    el.classList.add('disabled');
    return;
  }
  el.href = url;
  el.target = '_blank';
  el.rel = 'noreferrer noopener';
  el.classList.remove('disabled');
  el.classList.add('clickable');
}

function safeHostname(url) {
  try {
    return new URL(url).hostname;
  } catch (_) {
    return null;
  }
}

function setDotState(dotEl, state = 'offline') {
  if (!dotEl) return;
  const allowed = ['online', 'offline', 'idle'];
  const resolved = allowed.includes(state) ? state : 'offline';
  dotEl.className = `dot ${resolved}`;
}
