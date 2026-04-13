// ==UserScript==
// @ignorecache
// @name           Widget Statusbar
// @description    Configurable widget-based bottom bar for Zen.
// ==/UserScript==

(() => {
  "use strict";

  const BAR_ID = "zen-developer-statusbar-root";
  const MAIN_WINDOW_ID = "main-window";
  const MOUNT_SELECTOR = "#zen-tabbox-wrapper";
  const ACTIVE_CLASS = "zen-developer-statusbar-active";
  const PREF_BRANCH = "zen.widgetStatusbar.";
  const LEGACY_PREF_BRANCH = "zen.developerStatusBar.";
  const CONTROLLER_KEY = "__zenWidgetStatusbarController";
  const LEGACY_CONTROLLER_KEY = "__zenDeveloperStatusBarController";
  const LAYOUT_VERSION = 2;
  const LAYOUT_VERSION_PREF = `${PREF_BRANCH}layoutVersion`;
  const PAGE_MEMORY_REFRESH_MS = 30_000;
  const WIDGET_IDS = [
    "domain",
    "clock",
    "date",
    "timeOnPage",
    "pageMemory",
    "appMemory",
    "battery",
    "pomodoro",
  ];
  const WIDGET_META = {
    domain: { label: "Site" },
    clock: { label: "Clock" },
    date: { label: "Date" },
    timeOnPage: { label: "On Page" },
    pageMemory: { label: "Page Mem" },
    appMemory: { label: "App Mem" },
    battery: { label: "Battery" },
    pomodoro: { label: "Pomodoro" },
  };

  const DEFAULT_PREFS = {
    widgets: {
      domain: { enabled: true, side: "right", order: 10 },
      clock: { enabled: true, side: "left", order: 10 },
      date: { enabled: true, side: "left", order: 20 },
      timeOnPage: { enabled: true, side: "right", order: 20 },
      pageMemory: { enabled: true, side: "right", order: 30 },
      appMemory: { enabled: true, side: "right", order: 40 },
      battery: { enabled: true, side: "left", order: 30 },
      pomodoro: { enabled: true, side: "center", order: 10 },
    },
    clockFormat: "locale",
    dateFormat: "short",
    pomodoro: {
      workMinutes: 25,
      breakMinutes: 5,
      autoStartBreak: true,
      autoStartWork: false,
      phase: "work",
      running: false,
      endsAtSeconds: 0,
      remainingSeconds: 25 * 60,
    },
  };

  const POMODORO_PREFS = {
    workMinutes: `${PREF_BRANCH}pomodoro.workMinutes`,
    breakMinutes: `${PREF_BRANCH}pomodoro.breakMinutes`,
    autoStartBreak: `${PREF_BRANCH}pomodoro.autoStartBreak`,
    autoStartWork: `${PREF_BRANCH}pomodoro.autoStartWork`,
    phase: `${PREF_BRANCH}pomodoro.phase`,
    running: `${PREF_BRANCH}pomodoro.running`,
    endsAtSeconds: `${PREF_BRANCH}pomodoro.endsAtSeconds`,
    remainingSeconds: `${PREF_BRANCH}pomodoro.remainingSeconds`,
  };

  function log(...args) {
    console.log("[WidgetStatusbar]", ...args);
  }

  function getWidgetPrefPath(widgetId, key) {
    return `${PREF_BRANCH}widgets.${widgetId}.${key}`;
  }

  function getLegacyPrefPath(prefName) {
    if (!prefName.startsWith(PREF_BRANCH)) {
      return prefName;
    }

    return `${LEGACY_PREF_BRANCH}${prefName.slice(PREF_BRANCH.length)}`;
  }

  class WidgetStatusbar {
    constructor(win) {
      this.window = win;
      this.document = win.document;
      this.root = null;
      this.leftGroup = null;
      this.centerGroup = null;
      this.rightGroup = null;
      this.widgetElements = new Map();
      this.widgetsBuilt = false;
      this.pageSessions = new WeakMap();
      this.prefRefreshTimer = 0;
      this.pendingRebuild = false;
      this.tickInterval = 0;
      this.memoryPulse = 0;
      this.destroyed = false;
      this.initialized = false;
      this.clockFormatters = new Map();
      this.dateFormatters = new Map();
      this.batteryReady = false;
      this.batteryInfo = null;
      this.batteryListener = null;
      this.pageMemoryPending = false;
      this.pageMemoryCollectionInFlight = false;
      this.pageMemoryCollectionQueued = false;
      this.pageMemoryLastCollectedAt = 0;
      this.pageMemoryLastWindowId = null;
      this.memorySnapshot = {
        appMemory: null,
        pageMemory: null,
      };
      this.prefObserver = {
        observe: (_subject, topic, data) => {
          if (topic !== "nsPref:changed" || !data.startsWith(PREF_BRANCH)) {
            return;
          }
          const needsRebuild =
            data.includes(".enabled") ||
            data.endsWith(".side") ||
            data.endsWith(".order");
          this.schedulePrefRefresh(needsRebuild);
        },
      };
      this.tabEventNames = ["TabSelect", "TabOpen", "TabClose"];
      this.boundTabEvent = () => {
        if (this.destroyed) {
          return;
        }
        this.refreshMemorySnapshot({ forcePageCollection: true });
        this.refreshVisibleWidgets(["domain", "timeOnPage", "pageMemory"]);
      };
      this.progressListener = {
        onLocationChange: (browser, webProgress, _request, location) => {
          if (this.destroyed) {
            return;
          }
          if (!browser || !location) {
            return;
          }
          if (webProgress && webProgress.isTopLevel === false) {
            return;
          }
          this.pageSessions.set(browser, {
            spec: location.spec || "",
            startedAt: Date.now(),
          });
          if (browser === this.getSelectedBrowser()) {
            this.refreshMemorySnapshot({ forcePageCollection: true });
            this.refreshVisibleWidgets(["domain", "timeOnPage", "pageMemory"]);
          }
        },
      };
      this.boundCleanup = this.cleanup.bind(this);
    }

    init() {
      if (this.initialized || this.destroyed) {
        return;
      }

      if (this.document.readyState !== "complete") {
        this.window.addEventListener("load", () => this.init(), { once: true });
        return;
      }

      this.initialized = true;
      this.migrateLegacyPrefs();
      this.ensureDefaultPrefs();
      this.applyLayoutMigration();
      this.captureExistingPageSessions();
      this.ensureMounted();
      this.rebuildWidgets();
      this.observePrefs();
      this.installTabListeners();
      this.installProgressListener();
      this.startTicking();
      this.initBattery();
      this.refreshMemorySnapshot({ forcePageCollection: true });
      this.refreshVisibleWidgets();

      if (typeof this.window.addUnloadListener === "function") {
        this.window.addUnloadListener(this.boundCleanup);
      }

      this.window.addEventListener("unload", this.boundCleanup, { once: true });
      this.window.addEventListener("beforeunload", this.boundCleanup, {
        once: true,
      });
    }

    cleanup() {
      if (this.destroyed) {
        return;
      }

      this.destroyed = true;

      if (this.prefRefreshTimer) {
        this.window.clearTimeout(this.prefRefreshTimer);
        this.prefRefreshTimer = 0;
      }

      if (this.tickInterval) {
        this.window.clearInterval(this.tickInterval);
        this.tickInterval = 0;
      }

      try {
        Services.prefs.removeObserver(PREF_BRANCH, this.prefObserver);
      } catch {}

      if (this.window.gBrowser?.tabContainer) {
        this.tabEventNames.forEach(eventName => {
          this.window.gBrowser.tabContainer.removeEventListener(
            eventName,
            this.boundTabEvent
          );
        });
      }

      if (this.window.gBrowser?.removeTabsProgressListener) {
        try {
          this.window.gBrowser.removeTabsProgressListener(this.progressListener);
        } catch {}
      }

      if (this.batteryInfo && this.batteryListener) {
        ["chargingchange", "levelchange"].forEach(eventName => {
          this.batteryInfo.removeEventListener(eventName, this.batteryListener);
        });
      }
      this.batteryInfo = null;
      this.batteryListener = null;

      this.pageMemoryPending = false;
      this.pageMemoryCollectionInFlight = false;
      this.pageMemoryCollectionQueued = false;
      this.pageMemoryLastCollectedAt = 0;
      this.pageMemoryLastWindowId = null;

      this.window.removeEventListener("unload", this.boundCleanup);
      this.window.removeEventListener("beforeunload", this.boundCleanup);

      const mainWindow = this.document.getElementById(MAIN_WINDOW_ID);
      if (mainWindow) {
        mainWindow.classList.remove(ACTIVE_CLASS);
      }

      if (this.root?.isConnected) {
        this.root.remove();
      }

      this.widgetElements.clear();
      this.clockFormatters.clear();
      this.dateFormatters.clear();
      this.widgetsBuilt = false;
      this.root = null;
      this.leftGroup = null;
      this.centerGroup = null;
      this.rightGroup = null;

      if (this.window[CONTROLLER_KEY] === this) {
        delete this.window[CONTROLLER_KEY];
      }
      if (this.window[LEGACY_CONTROLLER_KEY] === this) {
        delete this.window[LEGACY_CONTROLLER_KEY];
      }
    }

    observePrefs() {
      try {
        Services.prefs.addObserver(PREF_BRANCH, this.prefObserver);
      } catch (error) {
        log("Could not observe prefs:", error);
      }
    }

    installTabListeners() {
      if (!this.window.gBrowser?.tabContainer) {
        return;
      }

      this.tabEventNames.forEach(eventName => {
        this.window.gBrowser.tabContainer.addEventListener(
          eventName,
          this.boundTabEvent
        );
      });
    }

    installProgressListener() {
      if (!this.window.gBrowser?.addTabsProgressListener) {
        return;
      }

      try {
        this.window.gBrowser.addTabsProgressListener(this.progressListener);
      } catch (error) {
        log("Could not install progress listener:", error);
      }
    }

    startTicking() {
      if (this.tickInterval) {
        this.window.clearInterval(this.tickInterval);
      }

      this.tickInterval = this.window.setInterval(() => {
        if (this.destroyed) {
          return;
        }

        this.ensureMounted();
        this.advancePomodoroIfNeeded();
        this.refreshVisibleWidgets([
          "clock",
          "date",
          "timeOnPage",
          "pomodoro",
        ]);

        this.memoryPulse += 1;
        if (this.memoryPulse % 5 === 0) {
          this.refreshMemorySnapshot({
            allowPageCollection: this.memoryPulse % 30 === 0,
          });
        }
      }, 1000);
    }

    schedulePrefRefresh(needsRebuild) {
      if (this.destroyed) {
        return;
      }

      if (this.prefRefreshTimer) {
        this.window.clearTimeout(this.prefRefreshTimer);
      }

      this.pendingRebuild = this.pendingRebuild || needsRebuild;
      this.prefRefreshTimer = this.window.setTimeout(() => {
        const shouldRebuild = this.pendingRebuild;
        this.pendingRebuild = false;
        this.prefRefreshTimer = 0;

        if (this.destroyed) {
          return;
        }

        if (shouldRebuild) {
          this.rebuildWidgets();
        }

        this.refreshMemorySnapshot();
        this.refreshVisibleWidgets();
      }, 60);
    }

    migrateLegacyPrefs() {
      const prefNames = [
        `${PREF_BRANCH}clock.format`,
        `${PREF_BRANCH}date.format`,
        LAYOUT_VERSION_PREF,
        ...Object.values(POMODORO_PREFS),
      ];

      WIDGET_IDS.forEach(widgetId => {
        prefNames.push(getWidgetPrefPath(widgetId, "enabled"));
        prefNames.push(getWidgetPrefPath(widgetId, "side"));
        prefNames.push(getWidgetPrefPath(widgetId, "order"));
      });

      prefNames.forEach(prefName => this.migrateLegacyPref(prefName));
    }

    migrateLegacyPref(prefName) {
      if (Services.prefs.getPrefType(prefName) > 0) {
        return;
      }

      const legacyPrefName = getLegacyPrefPath(prefName);
      if (
        legacyPrefName === prefName ||
        Services.prefs.getPrefType(legacyPrefName) === 0
      ) {
        return;
      }

      const missing = {};
      const legacyValue = this.readPref(legacyPrefName, missing);
      if (legacyValue !== missing) {
        this.writePref(prefName, legacyValue);
      }
    }

    ensureDefaultPrefs() {
      WIDGET_IDS.forEach(widgetId => {
        const defaults = DEFAULT_PREFS.widgets[widgetId];
        this.setDefaultPref(getWidgetPrefPath(widgetId, "enabled"), defaults.enabled);
        this.setDefaultPref(getWidgetPrefPath(widgetId, "side"), defaults.side);
        this.setDefaultPref(getWidgetPrefPath(widgetId, "order"), defaults.order);
      });

      this.setDefaultPref(
        `${PREF_BRANCH}clock.format`,
        DEFAULT_PREFS.clockFormat
      );
      this.setDefaultPref(`${PREF_BRANCH}date.format`, DEFAULT_PREFS.dateFormat);
      this.setDefaultPref(
        POMODORO_PREFS.workMinutes,
        DEFAULT_PREFS.pomodoro.workMinutes
      );
      this.setDefaultPref(
        POMODORO_PREFS.breakMinutes,
        DEFAULT_PREFS.pomodoro.breakMinutes
      );
      this.setDefaultPref(
        POMODORO_PREFS.autoStartBreak,
        DEFAULT_PREFS.pomodoro.autoStartBreak
      );
      this.setDefaultPref(
        POMODORO_PREFS.autoStartWork,
        DEFAULT_PREFS.pomodoro.autoStartWork
      );
      this.setDefaultPref(POMODORO_PREFS.phase, DEFAULT_PREFS.pomodoro.phase);
      this.setDefaultPref(
        POMODORO_PREFS.running,
        DEFAULT_PREFS.pomodoro.running
      );
      this.setDefaultPref(
        POMODORO_PREFS.endsAtSeconds,
        DEFAULT_PREFS.pomodoro.endsAtSeconds
      );
      this.setDefaultPref(
        POMODORO_PREFS.remainingSeconds,
        DEFAULT_PREFS.pomodoro.remainingSeconds
      );
    }

    applyLayoutMigration() {
      const currentVersion = Number(this.readPref(LAYOUT_VERSION_PREF, 0));
      if (currentVersion >= LAYOUT_VERSION) {
        return;
      }

      Object.entries(DEFAULT_PREFS.widgets).forEach(([widgetId, defaults]) => {
        this.writePref(getWidgetPrefPath(widgetId, "side"), defaults.side);
        this.writePref(getWidgetPrefPath(widgetId, "order"), defaults.order);
      });

      this.writePref(LAYOUT_VERSION_PREF, LAYOUT_VERSION);
    }

    setDefaultPref(prefName, value) {
      if (Services.prefs.getPrefType(prefName) > 0) {
        return;
      }

      this.writePref(prefName, value);
    }

    writePref(prefName, value) {
      if (typeof value === "boolean") {
        Services.prefs.setBoolPref(prefName, value);
        return;
      }

      if (typeof value === "number") {
        Services.prefs.setIntPref(prefName, value);
        return;
      }

      Services.prefs.setStringPref(prefName, String(value));
    }

    readPref(prefName, fallback) {
      const prefType = Services.prefs.getPrefType(prefName);
      if (prefType === 0) {
        return fallback;
      }

      try {
        if (prefType === Services.prefs.PREF_BOOL) {
          return Services.prefs.getBoolPref(prefName);
        }

        if (prefType === Services.prefs.PREF_INT) {
          return Services.prefs.getIntPref(prefName);
        }

        if (prefType === Services.prefs.PREF_STRING) {
          return Services.prefs.getStringPref(prefName);
        }
      } catch {}

      return fallback;
    }

    getWidgetConfig(widgetId) {
      const defaults = DEFAULT_PREFS.widgets[widgetId];
      const enabled = Boolean(
        this.readPref(getWidgetPrefPath(widgetId, "enabled"), defaults.enabled)
      );
      const sidePref = this.readPref(
        getWidgetPrefPath(widgetId, "side"),
        defaults.side
      );
      const orderPref = Number(
        this.readPref(getWidgetPrefPath(widgetId, "order"), defaults.order)
      );

      return {
        enabled,
        side: ["left", "center", "right"].includes(sidePref)
          ? sidePref
          : defaults.side,
        order: Number.isFinite(orderPref) ? orderPref : defaults.order,
      };
    }

    getPomodoroSnapshot() {
      const phase = this.readPref(POMODORO_PREFS.phase, "work");
      const running = Boolean(this.readPref(POMODORO_PREFS.running, false));
      const endsAtSeconds = Number(
        this.readPref(POMODORO_PREFS.endsAtSeconds, 0)
      );
      const storedRemaining = Number(
        this.readPref(
          POMODORO_PREFS.remainingSeconds,
          DEFAULT_PREFS.pomodoro.remainingSeconds
        )
      );
      const now = this.nowSeconds();
      const remainingSeconds = running
        ? Math.max(0, endsAtSeconds - now)
        : Math.max(0, storedRemaining);

      return {
        phase: phase === "break" ? "break" : "work",
        running,
        endsAtSeconds: Number.isFinite(endsAtSeconds) ? endsAtSeconds : 0,
        remainingSeconds: Number.isFinite(remainingSeconds)
          ? remainingSeconds
          : 0,
      };
    }

    writePomodoroState(nextState) {
      this.writePref(POMODORO_PREFS.phase, nextState.phase);
      this.writePref(POMODORO_PREFS.running, nextState.running);
      this.writePref(POMODORO_PREFS.endsAtSeconds, nextState.endsAtSeconds);
      this.writePref(POMODORO_PREFS.remainingSeconds, nextState.remainingSeconds);
    }

    nowSeconds() {
      return Math.floor(Date.now() / 1000);
    }

    getPhaseDurationSeconds(phase) {
      const prefName =
        phase === "break"
          ? POMODORO_PREFS.breakMinutes
          : POMODORO_PREFS.workMinutes;
      const fallback =
        phase === "break"
          ? DEFAULT_PREFS.pomodoro.breakMinutes
          : DEFAULT_PREFS.pomodoro.workMinutes;
      const minutes = Number(this.readPref(prefName, fallback));
      const safeMinutes = Number.isFinite(minutes) && minutes > 0 ? minutes : fallback;
      return safeMinutes * 60;
    }

    togglePomodoro() {
      const snapshot = this.getPomodoroSnapshot();
      const now = this.nowSeconds();
      if (snapshot.running) {
        this.writePomodoroState({
          phase: snapshot.phase,
          running: false,
          endsAtSeconds: 0,
          remainingSeconds: Math.max(0, snapshot.endsAtSeconds - now),
        });
      } else {
        const duration =
          snapshot.remainingSeconds > 0
            ? snapshot.remainingSeconds
            : this.getPhaseDurationSeconds(snapshot.phase);
        this.writePomodoroState({
          phase: snapshot.phase,
          running: true,
          endsAtSeconds: now + duration,
          remainingSeconds: duration,
        });
      }
    }

    resetPomodoro(phase = "work") {
      const nextPhase = phase === "break" ? "break" : "work";
      this.writePomodoroState({
        phase: nextPhase,
        running: false,
        endsAtSeconds: 0,
        remainingSeconds: this.getPhaseDurationSeconds(nextPhase),
      });
    }

    advancePomodoroIfNeeded() {
      const snapshot = this.getPomodoroSnapshot();
      if (!snapshot.running || snapshot.endsAtSeconds > this.nowSeconds()) {
        return;
      }

      const nextPhase = snapshot.phase === "work" ? "break" : "work";
      const autoStartPref =
        nextPhase === "break"
          ? POMODORO_PREFS.autoStartBreak
          : POMODORO_PREFS.autoStartWork;
      const autoStart = Boolean(this.readPref(autoStartPref, false));
      const duration = this.getPhaseDurationSeconds(nextPhase);
      const now = this.nowSeconds();

      this.writePomodoroState({
        phase: nextPhase,
        running: autoStart,
        endsAtSeconds: autoStart ? now + duration : 0,
        remainingSeconds: duration,
      });
    }

    ensureMounted() {
      if (this.destroyed) {
        return false;
      }

      const mountPoint = this.document.querySelector(MOUNT_SELECTOR);
      if (!mountPoint) {
        return false;
      }

      if (this.root?.isConnected && this.root.parentNode === mountPoint) {
        return true;
      }

      if (this.root?.isConnected) {
        this.root.remove();
      }

      this.root = this.document.createElement("div");
      this.root.id = BAR_ID;
      this.root.setAttribute("role", "toolbar");
      this.root.setAttribute("aria-label", "Widget Statusbar");

      this.leftGroup = this.document.createElement("div");
      this.leftGroup.className = "zen-developer-statusbar-group is-left";

      this.centerGroup = this.document.createElement("div");
      this.centerGroup.className = "zen-developer-statusbar-group is-center";

      this.rightGroup = this.document.createElement("div");
      this.rightGroup.className = "zen-developer-statusbar-group is-right";

      this.root.append(this.leftGroup, this.centerGroup, this.rightGroup);
      mountPoint.appendChild(this.root);
      this.widgetsBuilt = false;
      return true;
    }

    rebuildWidgets() {
      if (this.destroyed || !this.ensureMounted()) {
        return;
      }

      this.widgetElements.clear();
      this.leftGroup.replaceChildren();
      this.centerGroup.replaceChildren();
      this.rightGroup.replaceChildren();

      const orderedWidgets = {
        left: [],
        center: [],
        right: [],
      };

      WIDGET_IDS.forEach((widgetId, index) => {
        const config = this.getWidgetConfig(widgetId);
        if (!config.enabled) {
          return;
        }

        orderedWidgets[config.side].push({
          widgetId,
          order: config.order,
          index,
        });
      });

      ["left", "center", "right"].forEach(side => {
        orderedWidgets[side]
          .sort((a, b) => a.order - b.order || a.index - b.index)
          .forEach(({ widgetId }) => {
            const widget = this.createWidget(widgetId);
            if (!widget) {
              return;
            }

            this.widgetElements.set(widgetId, widget);
            const targetGroup =
              side === "left"
                ? this.leftGroup
                : side === "center"
                  ? this.centerGroup
                  : this.rightGroup;
            targetGroup.appendChild(widget);
          });
      });

      const hasWidgets = this.widgetElements.size > 0;
      this.widgetsBuilt = true;
      this.root.hidden = !hasWidgets;

      const mainWindow = this.document.getElementById(MAIN_WINDOW_ID);
      if (mainWindow) {
        mainWindow.classList.toggle(ACTIVE_CLASS, hasWidgets);
      }

      this.refreshMemorySnapshot();
      this.refreshVisibleWidgets();
    }

    createWidget(widgetId) {
      if (widgetId === "pomodoro") {
        return this.createPomodoroWidget();
      }

      if (widgetId === "battery" && !(this.batteryReady && this.batteryInfo)) {
        return null;
      }

      return this.createTextWidget(widgetId, WIDGET_META[widgetId].label);
    }

    createTextWidget(widgetId, label) {
      const widget = this.document.createElement("div");
      widget.className = "zen-developer-statusbar-widget";
      widget.dataset.widgetId = widgetId;

      const labelNode = this.document.createElement("span");
      labelNode.className = "zen-developer-statusbar-widget-label";
      labelNode.textContent = label;

      const valueNode = this.document.createElement("span");
      valueNode.className = "zen-developer-statusbar-widget-value";
      widget._zenValueNode = valueNode;

      widget.append(labelNode, valueNode);
      return widget;
    }

    createPomodoroWidget() {
      const widget = this.document.createElement("div");
      widget.className =
        "zen-developer-statusbar-widget zen-developer-statusbar-widget-pomodoro";
      widget.dataset.widgetId = "pomodoro";

      const labelNode = this.document.createElement("span");
      labelNode.className = "zen-developer-statusbar-widget-label";
      labelNode.textContent = WIDGET_META.pomodoro.label;

      const phaseNode = this.document.createElement("span");
      phaseNode.className = "zen-developer-statusbar-widget-phase";

      const valueNode = this.document.createElement("span");
      valueNode.className = "zen-developer-statusbar-widget-value";

      const controls = this.document.createElement("div");
      controls.className = "zen-developer-statusbar-controls";

      const primary = this.document.createElement("button");
      primary.type = "button";
      primary.className = "zen-developer-statusbar-button";
      primary.addEventListener("click", event => {
        event.preventDefault();
        event.stopPropagation();
        this.togglePomodoro();
      });

      const reset = this.document.createElement("button");
      reset.type = "button";
      reset.className =
        "zen-developer-statusbar-button zen-developer-statusbar-button-reset";
      reset.textContent = "Reset";
      reset.addEventListener("click", event => {
        event.preventDefault();
        event.stopPropagation();
        this.resetPomodoro("work");
      });

      controls.append(primary, reset);
      widget._zenPhaseNode = phaseNode;
      widget._zenValueNode = valueNode;
      widget._zenPrimaryButton = primary;
      widget.append(labelNode, phaseNode, valueNode, controls);
      return widget;
    }

    refreshVisibleWidgets(widgetIds = WIDGET_IDS) {
      if (this.destroyed) {
        return;
      }

      if (!this.ensureMounted()) {
        return;
      }

      if (!this.widgetsBuilt) {
        this.rebuildWidgets();
        return;
      }

      widgetIds.forEach(widgetId => {
        const widget = this.widgetElements.get(widgetId);
        if (!widget) {
          return;
        }

        this.updateWidget(widgetId, widget);
      });
    }

    updateWidget(widgetId, widget) {
      switch (widgetId) {
        case "domain":
          this.setWidgetValue(
            widget,
            this.formatSelectedBrowserLabel(),
            this.getSelectedBrowser()?.currentURI?.spec || ""
          );
          break;
        case "clock":
          this.setWidgetValue(widget, this.formatClock());
          break;
        case "date":
          this.setWidgetValue(widget, this.formatDate());
          break;
        case "timeOnPage":
          this.setWidgetValue(widget, this.formatTimeOnPage());
          break;
        case "pageMemory":
          this.setWidgetValue(widget, this.formatPageMemory());
          break;
        case "appMemory":
          this.setWidgetValue(widget, this.formatAppMemory());
          break;
        case "battery":
          this.setWidgetValue(widget, this.formatBattery());
          break;
        case "pomodoro":
          this.updatePomodoroWidget(widget);
          break;
        default:
          break;
      }
    }

    getCachedWidgetNode(widget, propertyName, selector) {
      if (widget[propertyName]?.isConnected) {
        return widget[propertyName];
      }

      const node = widget.querySelector(selector);
      if (node) {
        widget[propertyName] = node;
      }
      return node;
    }

    setWidgetValue(widget, value, title = "") {
      const valueNode = this.getCachedWidgetNode(
        widget,
        "_zenValueNode",
        ".zen-developer-statusbar-widget-value"
      );
      if (!valueNode) {
        return;
      }

      const nextValue = String(value);
      if (valueNode.textContent !== nextValue) {
        valueNode.textContent = nextValue;
      }
      if (title) {
        if (widget.title !== title) {
          widget.title = title;
        }
      } else if (widget.hasAttribute("title")) {
        widget.removeAttribute("title");
      }
    }

    updatePomodoroWidget(widget) {
      const snapshot = this.getPomodoroSnapshot();
      const phaseNode = this.getCachedWidgetNode(
        widget,
        "_zenPhaseNode",
        ".zen-developer-statusbar-widget-phase"
      );
      const valueNode = this.getCachedWidgetNode(
        widget,
        "_zenValueNode",
        ".zen-developer-statusbar-widget-value"
      );
      const primaryButton = this.getCachedWidgetNode(
        widget,
        "_zenPrimaryButton",
        ".zen-developer-statusbar-button"
      );

      if (!phaseNode || !valueNode || !primaryButton) {
        return;
      }

      const phaseText = snapshot.phase === "break" ? "Break" : "Work";
      if (phaseNode.textContent !== phaseText) {
        phaseNode.textContent = phaseText;
      }

      const durationText = this.formatDuration(snapshot.remainingSeconds * 1000);
      if (valueNode.textContent !== durationText) {
        valueNode.textContent = durationText;
      }

      const primaryText = snapshot.running ? "Pause" : "Start";
      if (primaryButton.textContent !== primaryText) {
        primaryButton.textContent = primaryText;
      }
      widget.dataset.phase = snapshot.phase;
    }

    getSelectedBrowser() {
      return this.window.gBrowser?.selectedBrowser || null;
    }

    captureExistingPageSessions() {
      if (!this.window.gBrowser?.tabs) {
        return;
      }

      Array.from(this.window.gBrowser.tabs).forEach(tab => {
        if (tab?.linkedBrowser) {
          this.pageSessions.set(tab.linkedBrowser, {
            spec: tab.linkedBrowser.currentURI?.spec || "",
            startedAt: Date.now(),
          });
        }
      });
    }

    getPageSession(browser) {
      if (!browser) {
        return null;
      }

      const spec = browser.currentURI?.spec || "";
      const existing = this.pageSessions.get(browser);
      if (existing && existing.spec === spec) {
        return existing;
      }

      const next = {
        spec,
        startedAt: Date.now(),
      };
      this.pageSessions.set(browser, next);
      return next;
    }

    formatSelectedBrowserLabel() {
      const browser = this.getSelectedBrowser();
      const uri = browser?.currentURI;
      if (!uri) {
        return "No Page";
      }

      try {
        const host = uri.host || uri.asciiHost || "";
        if (host) {
          return host.replace(/^www\./, "");
        }
      } catch {}

      const spec = uri.spec || "";
      if (!spec) {
        return "No Page";
      }

      if (spec.startsWith("about:")) {
        return spec;
      }

      if (spec.startsWith("file:")) {
        return "file://";
      }

      return spec.length > 32 ? `${spec.slice(0, 29)}...` : spec;
    }

    getClockFormatter(format) {
      if (!this.clockFormatters.has(format)) {
        const options = {
          hour: "2-digit",
          minute: "2-digit",
        };
        if (format === "12h") {
          options.hour12 = true;
        } else if (format === "24h") {
          options.hour12 = false;
        }
        this.clockFormatters.set(
          format,
          new Intl.DateTimeFormat(undefined, options)
        );
      }

      return this.clockFormatters.get(format);
    }

    formatClock() {
      const format = this.readPref(
        `${PREF_BRANCH}clock.format`,
        DEFAULT_PREFS.clockFormat
      );
      return this.getClockFormatter(format).format(Date.now());
    }

    getDateFormatter(format) {
      if (!this.dateFormatters.has(format)) {
        const options = {
          month: "short",
          day: "numeric",
        };
        if (format === "long") {
          options.year = "numeric";
        } else if (format === "weekday") {
          options.weekday = "short";
        }
        this.dateFormatters.set(
          format,
          new Intl.DateTimeFormat(undefined, options)
        );
      }

      return this.dateFormatters.get(format);
    }

    formatDate() {
      const format = this.readPref(
        `${PREF_BRANCH}date.format`,
        DEFAULT_PREFS.dateFormat
      );
      return this.getDateFormatter(format).format(Date.now());
    }

    formatTimeOnPage() {
      const session = this.getPageSession(this.getSelectedBrowser());
      if (!session) {
        return "00:00";
      }

      return this.formatDuration(Date.now() - session.startedAt);
    }

    formatDuration(milliseconds) {
      const totalSeconds = Math.max(0, Math.floor(milliseconds / 1000));
      const hours = Math.floor(totalSeconds / 3600);
      const minutes = Math.floor((totalSeconds % 3600) / 60);
      const seconds = totalSeconds % 60;

      if (hours > 0) {
        return `${hours}h ${String(minutes).padStart(2, "0")}m`;
      }

      return `${String(minutes).padStart(2, "0")}:${String(seconds).padStart(2, "0")}`;
    }

    formatBytes(bytes) {
      if (!Number.isFinite(bytes) || bytes <= 0) {
        return "N/A";
      }

      const units = ["B", "KB", "MB", "GB", "TB"];
      let size = bytes;
      let unitIndex = 0;
      while (size >= 1024 && unitIndex < units.length - 1) {
        size /= 1024;
        unitIndex += 1;
      }

      const digits = size >= 10 || unitIndex === 0 ? 0 : 1;
      return `${size.toFixed(digits)} ${units[unitIndex]}`;
    }

    getMemoryManager() {
      try {
        return Cc["@mozilla.org/memory-reporter-manager;1"].getService(
          Ci.nsIMemoryReporterManager
        );
      } catch {
        return null;
      }
    }

    readAppMemory() {
      const manager = this.getMemoryManager();
      if (!manager) {
        return null;
      }

      const candidates = [
        "residentUnique",
        "residentFast",
        "resident",
        "explicit",
        "heapAllocated",
      ];

      for (const key of candidates) {
        try {
          const value = Number(manager[key]);
          if (Number.isFinite(value) && value > 0) {
            return value;
          }
        } catch {}
      }

      return null;
    }

    readPageMemory() {
      return null;
    }

    refreshMemorySnapshot({
      forcePageCollection = false,
      allowPageCollection = true,
    } = {}) {
      if (this.destroyed) {
        return;
      }

      if (this.widgetElements.has("appMemory")) {
        this.memorySnapshot.appMemory = this.readAppMemory();
      }

      if (this.widgetElements.has("pageMemory")) {
        this.maybeCollectPageMemory({
          forceCollection: forcePageCollection,
          allowCollection: allowPageCollection,
        });
      } else {
        this.memorySnapshot.pageMemory = null;
        this.pageMemoryPending = false;
      }

      this.refreshVisibleWidgets(["appMemory", "pageMemory"]);
    }

    getSelectedOuterWindowId() {
      return (
        this.getSelectedBrowser()?.browsingContext?.currentWindowGlobal?.outerWindowId ||
        null
      );
    }

    maybeCollectPageMemory({
      forceCollection = false,
      allowCollection = true,
    } = {}) {
      const outerWindowId = this.getSelectedOuterWindowId();
      if (!outerWindowId) {
        this.memorySnapshot.pageMemory = null;
        this.pageMemoryPending = false;
        return;
      }

      const now = Date.now();
      const shouldCollect =
        forceCollection ||
        (
          allowCollection &&
          (
            !this.pageMemoryLastCollectedAt ||
            this.pageMemoryLastWindowId !== outerWindowId ||
            now - this.pageMemoryLastCollectedAt >= PAGE_MEMORY_REFRESH_MS
          )
        );

      if (!shouldCollect) {
        return;
      }

      this.collectPageMemory(outerWindowId);
    }

    async collectPageMemory(outerWindowId) {
      if (!outerWindowId) {
        this.memorySnapshot.pageMemory = null;
        this.pageMemoryPending = false;
        return;
      }

      if (this.pageMemoryCollectionInFlight) {
        this.pageMemoryCollectionQueued = true;
        return;
      }

      this.pageMemoryCollectionInFlight = true;
      this.pageMemoryCollectionQueued = false;
      this.pageMemoryPending = true;
      this.memorySnapshot.pageMemory = null;
      this.refreshVisibleWidgets(["pageMemory"]);

      try {
        const total = await this.collectWindowObjectMemory(outerWindowId);
        if (this.destroyed) {
          return;
        }

        if (this.getSelectedOuterWindowId() !== outerWindowId) {
          this.pageMemoryCollectionQueued = true;
          return;
        }

        this.memorySnapshot.pageMemory = total;
        this.pageMemoryLastCollectedAt = Date.now();
        this.pageMemoryLastWindowId = outerWindowId;
      } catch (error) {
        log("Could not collect page memory:", error);
        if (!this.destroyed && this.getSelectedOuterWindowId() === outerWindowId) {
          this.memorySnapshot.pageMemory = null;
        }
      } finally {
        this.pageMemoryPending = false;
        this.pageMemoryCollectionInFlight = false;
        if (this.destroyed) {
          this.pageMemoryCollectionQueued = false;
        } else {
          this.refreshVisibleWidgets(["pageMemory"]);

          if (this.pageMemoryCollectionQueued) {
            this.pageMemoryCollectionQueued = false;
            this.collectPageMemory(this.getSelectedOuterWindowId());
          }
        }
      }
    }

    collectWindowObjectMemory(outerWindowId) {
      const manager = this.getMemoryManager();
      if (!manager || !outerWindowId) {
        return Promise.resolve(null);
      }

      return new Promise(resolve => {
        let total = 0;
        let matches = 0;

        const handleReport = (_process, path, kind, units, amount) => {
          if (
            kind !== Ci.nsIMemoryReporter.KIND_HEAP ||
            units !== Ci.nsIMemoryReporter.UNITS_BYTES ||
            !Number.isFinite(amount) ||
            amount <= 0
          ) {
            return;
          }

          if (
            !path.startsWith("explicit/window-objects/top(") ||
            !path.includes(`id=${outerWindowId})`)
          ) {
            return;
          }

          total += amount;
          matches += 1;
        };

        try {
          manager.getReports(
            handleReport,
            null,
            () => resolve(matches > 0 ? total : null),
            null,
            false
          );
        } catch (error) {
          log("getReports failed for page memory:", error);
          resolve(null);
        }
      });
    }

    formatAppMemory() {
      return this.formatBytes(this.memorySnapshot.appMemory);
    }

    formatPageMemory() {
      if (this.pageMemoryPending) {
        return "...";
      }
      if (!this.memorySnapshot.pageMemory) {
        return "N/A";
      }
      return this.formatBytes(this.memorySnapshot.pageMemory);
    }

    async initBattery() {
      if (this.destroyed) {
        return;
      }

      this.batteryReady = true;

      if (typeof this.window.navigator.getBattery !== "function") {
        if (!this.destroyed) {
          this.rebuildWidgets();
        }
        return;
      }

      try {
        const batteryInfo = await this.window.navigator.getBattery();
        if (this.destroyed) {
          return;
        }
        this.batteryInfo = batteryInfo;
        this.batteryListener = () => {
          if (!this.destroyed) {
            this.refreshVisibleWidgets(["battery"]);
          }
        };
        ["chargingchange", "levelchange"].forEach(eventName => {
          this.batteryInfo.addEventListener(eventName, this.batteryListener);
        });
      } catch (error) {
        log("Battery API unavailable:", error);
        this.batteryInfo = null;
      }

      if (!this.destroyed) {
        this.rebuildWidgets();
      }
    }

    formatBattery() {
      if (!this.batteryInfo) {
        return "N/A";
      }

      const level = Math.round((this.batteryInfo.level || 0) * 100);
      if (this.batteryInfo.charging) {
        return `Charging ${level}%`;
      }

      return `${level}%`;
    }
  }

  const previousController =
    window[CONTROLLER_KEY] || window[LEGACY_CONTROLLER_KEY];
  if (previousController) {
    try {
      previousController.cleanup();
    } catch (error) {
      log("Previous controller cleanup failed:", error);
    }
  }

  const controller = new WidgetStatusbar(window);
  window[CONTROLLER_KEY] = controller;
  window[LEGACY_CONTROLLER_KEY] = controller;
  controller.init();
})();
