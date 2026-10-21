(function () {
  'use strict';
  if (document.documentElement.dataset.enhanced) return;
  document.documentElement.dataset.enhanced = 'true';
  const legacy = document.querySelector('[data-legacy]');
  if (legacy) {
    const link = legacy.querySelector('[data-legacy-target]');
    if (link) {
      const destination = new URL(link.href, document.baseURI); destination.search = location.search;
      const known = ['top','watch','contract-formation','execution','delegation','completion','research','formal-evidence','feasibility-evidence','adversarial-evidence','foundations','technical-report'];
      destination.hash = legacy.dataset.legacy === 'positions' ? 'open-positions' : known.includes(location.hash.slice(1)) ? location.hash : 'top';
      location.replace(destination.href); return;
    }
  }
  const header = document.querySelector('.v2-header');
  const menu = document.querySelector('.menu-toggle');
  const nav = document.getElementById('project-navigation');
  if (header && menu && nav) {
    const updateHeight = () => document.documentElement.style.setProperty('--header-height', header.getBoundingClientRect().height + 'px');
    const closeMenu = (focus) => { menu.setAttribute('aria-expanded','false'); delete nav.dataset.open; if (focus) menu.focus(); updateHeight(); };
    menu.addEventListener('click', () => { const open = menu.getAttribute('aria-expanded') !== 'true'; menu.setAttribute('aria-expanded', String(open)); if (open) nav.dataset.open = ''; else delete nav.dataset.open; updateHeight(); });
    document.addEventListener('keydown', event => { if (event.key === 'Escape' && menu.getAttribute('aria-expanded') === 'true') { closeMenu(true); } });
    nav.addEventListener('click', event => { if (event.target.closest('a')) closeMenu(false); });
    document.addEventListener('click', event => { if (!header.contains(event.target)) closeMenu(false); });
    if (typeof ResizeObserver === 'function') new ResizeObserver(updateHeight).observe(header);
    window.addEventListener('resize', () => { if (window.innerWidth > 960) closeMenu(false); updateHeight(); });
    updateHeight();
    if (location.hash) requestAnimationFrame(() => document.getElementById(decodeURIComponent(location.hash.slice(1)))?.scrollIntoView());
  }
})();
