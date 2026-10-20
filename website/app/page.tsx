/* oxlint-disable next/no-img-element -- Local SVG diagrams and institution marks retain their intrinsic aspect ratios. */
import { SiteLink } from '@/components/site-link';
import { SiteHeader, SiteFooter, Arrow, FoundationsPaper, PaperLink } from '@/components/site-chrome';
import { HomeIllustration } from '@/components/site-figures';
import { Paragraphs } from '@/components/copy';
import { c, table } from '@/lib/site-data';

const institutions = [
  ['SDA Bocconi School of Management', 'sda-bocconi.svg', 'bocconi', 'REAL', 'https://www.sdabocconi.it/en/faculty-research/faculty-knowledge/alessandro-rudi/'],
  ['Italian Institute of Artificial Intelligence for Industry', 'ai4i.png', 'ai4i', 'PRAXIS', 'https://ai4i.it/rde-labs/#PRAXIS'],
  ['University College London', 'ucl.svg', 'ucl', 'Computer Science', 'https://profiles.ucl.ac.uk/60171-carlo-ciliberto'],
  ['Inria', 'inria.svg', 'inria', 'STAMP', 'https://www.inria.fr/en/stamp'],
];
export default function Home() {
  return <><SiteHeader /><main id="main" className="v2 home-v2">
    <section className="home-hero shell" id="top" aria-labelledby="home-title">
      <div className="hero-copy">
        <p className="eyebrow">{c('3.1',0)}</p>
        <h1 id="home-title"><span>Proof Carrying</span>{' '}<span>Contracts</span></h1>
        <p className="hero-tagline">{c('3.1',1)}</p>
        <p className="lead">{c('3.1',2)}</p>
        <div className="hero-actions"><SiteLink className="primary-link" href="/overview">How PC2 works <Arrow /></SiteLink><PaperLink local /></div>
      </div>
    </section>
    <section className="v2-section shell mission-section" id="editorial-vision" aria-labelledby="stakes-title">
      <div className="section-intro"><p className="eyebrow">The mission</p><h2 id="stakes-title">{c('3.2',0)}</h2></div>
      <div className="mission-copy"><Paragraphs text={c('3.2',1)} /></div>
    </section>
    <section className="v2-section mechanism-band" id="approach" aria-labelledby="approach-title"><div className="shell">
      <div className="section-intro"><p className="eyebrow">{c('3.3',0)}</p><h2 id="approach-title">{c('3.3',1)}</h2><p>{c('3.3',2)}</p></div>
      <ol className="mechanism-sequence">{table('3.3').map(([number,title,text],i)=><li key={number}>
        <HomeIllustration step={i} />
        <div className="mechanism-copy"><span className="row-number">{number}</span><h3>{title}</h3><p>{text}</p></div>
      </li>)}</ol>
      <SiteLink className="text-link" href="/overview#contract-formation">{c('3.3',3)} <Arrow /></SiteLink>
    </div></section>
    <section className="v2-section shell" id="research" aria-labelledby="research-title"><div className="section-intro"><p className="eyebrow">The research programme</p><h2 id="research-title">{c('3.4',0)}</h2><p>{c('3.4',1)}</p></div>
      <div className="research-rows">{table('3.4').map(([number,title,text])=><article className="research-row" key={number}><div><span className="row-number">{number}</span><h3>{title}</h3></div><p>{text}</p></article>)}</div>
      <SiteLink className="text-link" href="/overview#research">{c('3.4',2)} <Arrow /></SiteLink>
    </section>
    <section className="v2-section shell paper-section" id="foundations" aria-label="PC2 foundations paper"><FoundationsPaper /></section>
    <section className="v2-section shell" id="consortium" aria-labelledby="consortium-title"><div className="section-intro"><p className="eyebrow">Research consortium</p><h2 id="consortium-title">{c('3.6',0)}</h2><Paragraphs text={c('3.6',1)} /></div>
      <div className="institution-grid">{institutions.map(([name,image,css,label,href])=><a href={href} className={`institution ${css}`} key={name}><div className="logo-slot"><img src={`/logos/${image}`} alt={name} loading="lazy" /></div><span>{label}</span></a>)}</div>
    </section>
    <section className="v2-section participation-close" id="join" aria-labelledby="join-title"><div className="shell"><p className="eyebrow">Get involved</p><h2 id="join-title">{c('3.7',0)}</h2><Paragraphs className="section-intro" text={c('3.7',1)} /><div className="hero-actions"><SiteLink className="primary-link" href="/get-involved#open-positions">Open positions <Arrow /></SiteLink><SiteLink className="text-link" href="/get-involved#collaboration">Collaboration and community <Arrow /></SiteLink></div></div></section>
  </main><SiteFooter /></>;
}
