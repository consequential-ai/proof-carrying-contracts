import { SiteHeader, SiteFooter } from './site-chrome';
export function LegacyPage({ kind }: { kind: 'protocol' | 'positions' }) {
  const protocol = kind === 'protocol';
  return <><SiteHeader /><main id="main" className="v2" data-legacy={kind}><section id="top" className="v2-page-opening shell"><h1>This page has moved.</h1><a className="text-link" data-legacy-target href={protocol?'/overview':'/get-involved#open-positions'}>{protocol?'Continue to the PC2 overview.':'Continue to PC2 positions and participation.'}</a></section></main><SiteFooter /></>;
}
