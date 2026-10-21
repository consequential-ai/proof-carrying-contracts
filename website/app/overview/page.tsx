import { SiteHeader, SiteFooter, FoundationsPaper, PaperLink, Arrow } from '@/components/site-chrome';
import { SiteLink } from '@/components/site-link';
import { ProcessFilm } from '@/components/process-film';
import { SiteFigure } from '@/components/site-figures';
import { Paragraphs } from '@/components/copy';
import { c, table, config, pageMetadata } from '@/lib/site-data';
export const metadata = pageMetadata('How PC2 works | Proof Carrying Contracts', 'An accessible introduction to PC2 contracts, proof checking, controlled execution and delegation.', '/overview');
const contents = table('4.1');
export default function Overview() {
  const releaseUrls = [config.implementation.demoUrl, config.implementation.repositoryUrl];
  return <><SiteHeader active="overview" /><main id="main" className="v2 overview-v2">
    <section className="v2-page-opening shell" id="top" aria-labelledby="overview-title"><div className="reading-column"><p className="eyebrow">Protocol overview</p><h1 id="overview-title">{c('4.1',0)}</h1><p className="lead">{c('4.1',1)}</p><p>{c('4.1',2)}</p><div className="hero-actions"><a className="primary-link" href="#watch">Watch the walkthrough <Arrow down /></a><PaperLink local down /></div></div></section>
    <div className="shell overview-layout"><aside className="contents-rail"><details className="contents" open><summary>On this page</summary><nav aria-label="On this page">{contents.map(([label,id])=><a href={`#${id}`} key={id}>{label}</a>)}</nav></details></aside><div className="overview-article">
      <section id="watch" className="overview-section" aria-labelledby="watch-title"><div className="reading-column"><h2 id="watch-title">{c('4.2',0)}</h2><p>{c('4.2',1)}</p></div><ProcessFilm /></section>
      <section id="contract-formation" className="overview-section" aria-labelledby="formation-title"><div className="reading-column"><p className="eyebrow">01 · Agreement</p><h2 id="formation-title">{c('4.3',0)}</h2><Paragraphs text={c('4.3',1)} /></div><SiteFigure kind="formation" /><div className="reading-column"><Paragraphs text={c('4.3',4)} /><details className="explanation"><summary>{c('4.3',5)}</summary><p>{c('4.3',6)}</p></details></div></section>
      <section id="execution" className="overview-section" aria-labelledby="execution-title"><div className="reading-column"><p className="eyebrow">02 · Execution</p><h2 id="execution-title">{c('4.4',0)}</h2><Paragraphs text={c('4.4',1)} /><dl className="proof-distinction">{table('4.4').map(([label,text])=><div key={label}><dt>{label}</dt><dd>{text}</dd></div>)}</dl></div><SiteFigure kind="execution" /><div className="reading-column"><Paragraphs text={c('4.4',4)} /></div></section>
      <section id="delegation" className="overview-section" aria-labelledby="delegation-title"><div className="reading-column"><p className="eyebrow">03 · Delegation</p><h2 id="delegation-title">{c('4.5',0)}</h2><Paragraphs text={c('4.5',1)} /></div><SiteFigure kind="delegation" /><div className="reading-column"><Paragraphs text={c('4.5',4)} /></div></section>
      <section id="completion" className="overview-section" aria-labelledby="completion-title"><div className="reading-column"><p className="eyebrow">04 · Completion</p><h2 id="completion-title">{c('4.6',0)}</h2><Paragraphs text={c('4.6',1)} /></div></section>
      <section id="research" className="overview-section" aria-labelledby="research-title"><div className="reading-column"><p className="eyebrow">Scientific programme</p><h2 id="research-title">{c('4.7',0)}</h2><p>{c('4.7',1)}</p><div className="overview-research">{table('4.7').map(([id,title,text])=><article key={id} aria-labelledby={id}><h3 id={id}>{title}</h3><Paragraphs text={text} /></article>)}</div><p>{c('4.7',2)}</p></div></section>
      <section id="foundations" className="overview-section" aria-labelledby="foundations-title"><div className="reading-column"><h2 id="foundations-title">{c('4.8',0)}</h2></div><FoundationsPaper headingLevel={3} /><dl className="release-list">{table('4.8').map(([item,text],i)=><div key={item}><dt>{item}</dt><dd><p>{text}</p><div className="release-actions">{(!releaseUrls[i] || config.implementation.status !== 'released') && <span className="status-label">Upcoming</span>}{releaseUrls[i] && <a className="text-link" href={releaseUrls[i]!}>{i === 1 ? 'GitHub repository' : 'Explore'} <Arrow /></a>}</div></dd></div>)}</dl><SiteLink className="text-link" href="/get-involved#open-positions">Explore the research positions <Arrow /></SiteLink></section>
    </div></div>
  </main><SiteFooter /></>;
}
