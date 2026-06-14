import { useState, useRef, useEffect, useCallback } from 'react';
import { CLOSED_PANELS, PANELS_CONFIG } from '../config/panels';

const PANEL_ORDER = PANELS_CONFIG.map(p => p.id);
// Next open panel after removeId, by config order (wraps); null if none remain.
const nextOpenPanelId = (panelsState, removeId) => {
  const start = PANEL_ORDER.indexOf(removeId);
  for (let i = 1; i <= PANEL_ORDER.length; i++) {
    const cand = PANEL_ORDER[(start + i) % PANEL_ORDER.length];
    if (cand !== removeId && panelsState[cand]) return cand;
  }
  return null;
};

// Chrome state shared by desktop and mobile: the panels accordion, the mobile
// drawers (tools/shapes/panels), the mobile context menu + long-press
// bookkeeping, and the mobile toolbar's measured-width/safe-area layout
// metrics. Mobile-only state is force-closed when leaving mobile widths.
export function useUIShell({ isMobile, viewportSize, mobileBottomInset }) {
  const [mobileToolsOpen, setMobileToolsOpen] = useState(false);
  const [mobilePanelsOpen, setMobilePanelsOpen] = useState(false);
  const [mobileShapePanelOpen, setMobileShapePanelOpen] = useState(false);
  const [mobileToolbarWidth, setMobileToolbarWidth] = useState(0);
  const [canvasContextMenu, setCanvasContextMenu] = useState(null);
  const [openPanels, setOpenPanels] = useState(CLOSED_PANELS);
  const [expandedPanel, setExpandedPanel] = useState(null);
  const [uiHidden, setUiHidden] = useState(false);
  const mobileToolbarShellRef = useRef(null);
  const mobileLongPressRef = useRef({ timerId: null, pointerId: null, startX: 0, startY: 0, targetType: null, targetId: null, triggered: false });

  const clearMobileLongPress = useCallback(() => {
    const longPressState = mobileLongPressRef.current;
    if (longPressState.timerId) {
      clearTimeout(longPressState.timerId);
    }
    mobileLongPressRef.current = {
      timerId: null,
      pointerId: null,
      startX: 0,
      startY: 0,
      targetType: null,
      targetId: null,
      triggered: false
    };
  }, []);

  const closeCanvasContextMenu = useCallback(() => {
    setCanvasContextMenu(null);
  }, []);

  useEffect(() => {
    if (!isMobile) {
      setMobileToolbarWidth(0);
      return;
    }
    const toolbarShell = mobileToolbarShellRef.current;
    if (!toolbarShell) return;

    const syncMobileToolbarWidth = () => {
      const measured = Math.round(toolbarShell.getBoundingClientRect().width);
      if (measured > 0) {
        setMobileToolbarWidth(prev => (prev === measured ? prev : measured));
      }
    };

    syncMobileToolbarWidth();
    let observer = null;
    if (typeof ResizeObserver !== 'undefined') {
      observer = new ResizeObserver(syncMobileToolbarWidth);
      observer.observe(toolbarShell);
    }

    window.addEventListener('resize', syncMobileToolbarWidth);
    window.visualViewport?.addEventListener('resize', syncMobileToolbarWidth);
    return () => {
      observer?.disconnect();
      window.removeEventListener('resize', syncMobileToolbarWidth);
      window.visualViewport?.removeEventListener('resize', syncMobileToolbarWidth);
    };
  }, [isMobile]);

  useEffect(() => {
    if (!isMobile) {
      setMobileToolsOpen(false);
      setMobilePanelsOpen(false);
      setMobileShapePanelOpen(false);
    }
  }, [isMobile]);

  useEffect(() => {
    if (!isMobile) {
      setCanvasContextMenu(null);
      clearMobileLongPress();
    }
  }, [isMobile, clearMobileLongPress]);

  useEffect(() => () => {
    clearMobileLongPress();
  }, [clearMobileLongPress]);

  // Remove a panel from the stack; if it was the active tab, advance to the
  // next open panel by config order.
  const removePanel = (panelId) => {
    setOpenPanels(prev => {
      const next = { ...prev, [panelId]: false };
      setExpandedPanel(cur => (cur === panelId ? nextOpenPanelId(next, panelId) : cur));
      return next;
    });
  };

  // Toolbar entry point: toggles a panel's membership in the stack. Opening a
  // panel makes it the active tab; toggling the already-open one removes it.
  const togglePanel = (panelId) => {
    setMobileToolsOpen(false);
    setMobileShapePanelOpen(false);
    if (openPanels[panelId]) {
      removePanel(panelId);
      return;
    }
    setExpandedPanel(panelId);
    setMobilePanelsOpen(true);
    setOpenPanels(prev => ({ ...prev, [panelId]: true }));
  };

  useEffect(() => {
    if (!Object.values(openPanels).some(Boolean)) {
      setMobilePanelsOpen(false);
    }
  }, [openPanels]);

  const anyPanelOpen = Object.values(openPanels).some(Boolean);
  const closeAllPanels = () => {
    setCanvasContextMenu(null);
    setMobileToolsOpen(false);
    setMobileShapePanelOpen(false);
    setMobilePanelsOpen(false);
    setOpenPanels({ ...CLOSED_PANELS });
    setExpandedPanel(null);
  };
  // Mobile "open this panel" entry point: ensure it's in the stack and active
  // (without closing the others — the stack's nav/× manage membership). Matches
  // the unified desktop behavior.
  const openMobilePanel = (panelId) => {
    setCanvasContextMenu(null);
    setMobileToolsOpen(false);
    setMobileShapePanelOpen(false);
    setOpenPanels(prev => ({ ...prev, [panelId]: true }));
    setExpandedPanel(panelId);
    setMobilePanelsOpen(true);
  };
  const toggleMobileToolsMenu = () => {
    if (mobileToolsOpen) {
      setMobileToolsOpen(false);
      return;
    }
    closeAllPanels();
    setMobileToolsOpen(true);
  };
  const clearTapFocus = (event) => {
    if (event?.currentTarget && typeof event.currentTarget.blur === 'function') {
      event.currentTarget.blur();
    }
  };

  const anyMobileOverlayOpen = mobileToolsOpen || mobileShapePanelOpen || mobilePanelsOpen || anyPanelOpen;
  const mobileControlGapPx = 8;
  const mobileToolbarRowHeightPx = 48;
  const mobilePanelOffsetPx = mobileToolbarRowHeightPx + mobileControlGapPx;
  const mobileToolbarMinimumClearancePx = 44;
  const mobileToolbarDesignGapPx = 16;
  const resolvedMobileInsetPx = Math.max(mobileBottomInset, mobileToolbarMinimumClearancePx);
  const computedBottomInset = `max(env(safe-area-inset-bottom, 0px), ${resolvedMobileInsetPx}px)`;
  const mobileToolbarBottom = `calc(${computedBottomInset} + ${mobileToolbarDesignGapPx}px)`;
  const mobileMenuDrawerBottom = `calc(${mobileToolbarBottom} + ${mobilePanelOffsetPx}px)`;
  const mobileShapePanelBottom = `calc(${mobileToolbarBottom} + ${mobilePanelOffsetPx}px)`;
  const mobileToolbarMaxWidth = Math.max(0, viewportSize.width - 16);
  const measuredMobileToolbarWidth = mobileToolbarWidth > 0
    ? Math.min(mobileToolbarWidth, mobileToolbarMaxWidth)
    : mobileToolbarMaxWidth;
  const mobileToolbarSharedWidthStyle = {
    width: measuredMobileToolbarWidth > 0 ? `${measuredMobileToolbarWidth}px` : 'calc(100vw - 16px)',
    maxWidth: 'calc(100vw - 16px)'
  };
  const mobileTopInset = 'calc(env(safe-area-inset-top, 0px) + 8px)';

  const toggleUiHidden = useCallback(() => setUiHidden(prev => !prev), []);

  return {
    // panels accordion
    openPanels, setOpenPanels,
    expandedPanel, setExpandedPanel,
    togglePanel,
    removePanel,
    anyPanelOpen,
    closeAllPanels,
    openMobilePanel,
    // quiet UI (Ctrl+\ on desktop, drawer button on mobile)
    uiHidden, toggleUiHidden,
    // mobile drawers + context menu
    mobileToolsOpen, setMobileToolsOpen,
    mobilePanelsOpen, setMobilePanelsOpen,
    mobileShapePanelOpen, setMobileShapePanelOpen,
    canvasContextMenu, setCanvasContextMenu,
    closeCanvasContextMenu,
    toggleMobileToolsMenu,
    mobileLongPressRef,
    clearMobileLongPress,
    anyMobileOverlayOpen,
    clearTapFocus,
    // mobile layout metrics
    mobileToolbarShellRef,
    mobileToolbarBottom,
    mobileMenuDrawerBottom,
    mobileShapePanelBottom,
    mobileToolbarSharedWidthStyle,
    mobileTopInset
  };
}
