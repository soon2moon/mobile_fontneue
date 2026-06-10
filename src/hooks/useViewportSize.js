import { useState, useEffect } from 'react';

export function useViewportSize() {
  const [viewportSize, setViewportSize] = useState({
    width: window.innerWidth,
    height: window.innerHeight
  });
  const [mobileBottomInset, setMobileBottomInset] = useState(0);
  const isMobile = viewportSize.width <= 900;

  useEffect(() => {
    const handleResize = () => {
      setViewportSize({
        width: window.innerWidth,
        height: window.innerHeight
      });
    };
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  useEffect(() => {
    const updateMobileBottomInset = () => {
      const layoutHeight = document.documentElement?.clientHeight || window.innerHeight;
      if (!window.visualViewport) {
        const fallbackInset = Math.max(0, window.innerHeight - layoutHeight);
        setMobileBottomInset(Math.round(fallbackInset));
        return;
      }
      const viewport = window.visualViewport;
      const visualBottom = viewport.height + viewport.offsetTop;
      const viewportInset = Math.max(0, layoutHeight - visualBottom);
      const windowInset = Math.max(0, window.innerHeight - visualBottom);
      setMobileBottomInset(Math.round(Math.max(viewportInset, windowInset)));
    };

    updateMobileBottomInset();
    window.addEventListener('resize', updateMobileBottomInset);
    window.addEventListener('orientationchange', updateMobileBottomInset);
    window.visualViewport?.addEventListener('resize', updateMobileBottomInset);
    window.visualViewport?.addEventListener('scroll', updateMobileBottomInset);

    return () => {
      window.removeEventListener('resize', updateMobileBottomInset);
      window.removeEventListener('orientationchange', updateMobileBottomInset);
      window.visualViewport?.removeEventListener('resize', updateMobileBottomInset);
      window.visualViewport?.removeEventListener('scroll', updateMobileBottomInset);
    };
  }, []);

  return { viewportSize, isMobile, mobileBottomInset };
}
