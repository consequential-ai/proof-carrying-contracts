import { SiteHeader, SiteFooter, Arrow } from '@/components/site-chrome';
import { SiteLink } from '@/components/site-link';
import { Paragraphs } from '@/components/copy';
import { c, table, config, collaborationHref, statusLabel, positionCounts, pageMetadata } from '@/lib/site-data';
import { positions } from '@/lib/positions';
export const metadata = pageMetadata('Get involved | Proof Carrying Contracts', 'Research and engineering positions, collaboration and opportunities to contribute to Proof Carrying Contracts.', '/get-involved');
export default function GetInvolved() {
  const hasOpen = Object.values(config.positions).some(p=>p.status==='open');
  const groups = ['Research engineering','Postdoctoral research'];
  const cards = table('5.2');
  return <><SiteHeader active="get-involved" /><main id="main" className="v2 involved-v2">
    <section className="v2-page-opening shell" id="top" aria-labelledby="involved-title"><p className="eyebrow">Research and engineering</p><h1 id="involved-title">{c('5.1',0)}</h1><p className="lead section-intro">{c('5.1',1)}</p><div className="hero-actions"><a className="primary-link" href="#open-positions">Open positions <Arrow down /></a><a className="text-link" href="#collaboration">Collaboration and community <Arrow down /></a></div></section>
    <section className="v2-section shell" id="open-positions" aria-labelledby="positions-title"><div className="openings-heading"><h2 id="positions-title">Open positions</h2><span>{positionCounts()}</span></div><p className="section-intro">{hasOpen ? 'Explore the research and engineering appointments below. Each role page provides its current availability and application instructions.' : c('5.2',0)}</p>
      {groups.map(group=><div className="opening-group" key={group}><h3>{group}</h3>{cards.map(([,title,summary],i)=>{
        const position=positions[i]; const status=config.positions[position.slug].status;
        if((i<2?groups[0]:groups[1])!==group || status==='closed') return null;
        return <article className="opening" key={position.slug}><SiteLink className="opening-link" href={`/positions/${position.slug}`} aria-label={`${title}, ${position.city}, ${position.host}; ${statusLabel(status)}; role details`}><div className="opening-copy"><h4>{title}</h4><p className="opening-summary">{summary}</p></div><div className="opening-location"><strong>{position.host}</strong><span>{position.city}</span><span className="status-label">{statusLabel(status)}</span><span className="opening-read">Role details <Arrow /></span></div></SiteLink></article>;
      })}</div>)}
      <p className="section-intro positions-ending">{c('5.2',1)}</p>
    </section>
    <section className="v2-section collaboration-band" id="collaboration" aria-labelledby="collaboration-title"><div className="shell"><div className="section-intro"><p className="eyebrow">Beyond an appointment</p><h2 id="collaboration-title">{c('5.3',0)}</h2><Paragraphs text={c('5.3',1)} /></div>
      <div className="participation-routes">
        <article id="follow"><span className="row-number">01</span><h3>Follow the programme</h3><p>{c('5.3',2)}</p>{config.community.updatesUrl ? <a className="text-link" href={config.community.updatesUrl}>Receive project updates ↗</a> : <p className="channel-status">{c('5.3',3)}</p>}</article>
        <article id="discuss"><span className="row-number">02</span><h3>Discuss and collaborate</h3><Paragraphs text={c('5.3',4)} />{collaborationHref ? <a className="text-link" href={collaborationHref}>{config.community.collaborationUrl?'Start a conversation ↗':'Contact the project →'}</a> : <p className="channel-status">{c('5.3',5)}</p>}</article>
        <article id="contribute"><span className="row-number">03</span><h3>Test and contribute</h3><p className="status-label">Upcoming with the first implementation release</p><Paragraphs text={c('5.3',6)} />{config.community.contributionInterestUrl ? <a className="text-link" href={config.community.contributionInterestUrl}>Register interest in testing ↗</a> : collaborationHref ? <a className="text-link" href="#discuss">Discuss a contribution <Arrow /></a> : <p className="channel-status">Contribution instructions forthcoming</p>}</article>
      </div>
    </div></section>
  </main><SiteFooter /></>;
}
