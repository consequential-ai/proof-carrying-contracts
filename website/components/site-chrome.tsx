import { SiteLink } from '@/components/site-link';
import { FileText } from 'lucide-react';
import { AirlockMark } from './airlock-mark';
import { GitHubMark } from './github-mark';
import { c, config, paperPublished } from '@/lib/site-data';

export function Arrow({ down = false }: { down?: boolean }) {
  return <span aria-hidden="true" className="arrow">{down ? '↓' : '→'}</span>;
}
export function PaperLink({ local = false, className = 'text-link', down = false }: { local?: boolean; className?: string; down?: boolean }) {
  return <SiteLink className={className} href={paperPublished ? (config.paper.pdfUrl || config.paper.arxivUrl!) : local ? '#foundations' : '/overview#foundations'}>
    <FileText size={17} strokeWidth={1.6} aria-hidden="true" />
    <span>{paperPublished ? 'Read the PC2 foundations paper' : 'PC2 foundations paper (forthcoming)'}</span>
    <span aria-hidden="true">{paperPublished ? '↗' : down ? '↓' : ''}</span>
  </SiteLink>;
}
export function RepositoryLink({ iconOnly = false }: { iconOnly?: boolean }) {
  if (!config.implementation.repositoryUrl) return null;
  return <a className={iconOnly ? 'repository-icon-link' : 'text-link'} href={config.implementation.repositoryUrl} aria-label={iconOnly ? 'PC2 repository on GitHub' : undefined} title={iconOnly ? 'PC2 repository on GitHub' : undefined}>
    <GitHubMark size={iconOnly ? 24 : 18} />
    {!iconOnly && <><span>GitHub repository</span><span aria-hidden="true">↗</span></>}
  </a>;
}
export function SiteHeader({ active }: { active?: 'overview' | 'get-involved' }) {
  return <>
    <a className="skip-link" href="#main">Skip to content</a>
    <header className="site-header v2-header">
      <div className="shell header-inner">
        <SiteLink className="brand" href="/" aria-label="PC2, Proof Carrying Contracts, home">
          <AirlockMark className="brand-mark" />
          <span className="brand-word">PC<sup>2</sup></span>
          <span className="brand-name">Proof Carrying<br />Contracts</span>
        </SiteLink>
        <button className="menu-toggle" type="button" aria-expanded="false" aria-controls="project-navigation">Menu <span aria-hidden="true">☰</span></button>
        <nav id="project-navigation" aria-label="Project navigation">
          <SiteLink href="/overview" aria-current={active === 'overview' ? 'page' : undefined}>Overview</SiteLink>
          <SiteLink href="/get-involved" aria-current={active === 'get-involved' ? 'page' : undefined}>Get involved</SiteLink>
          <RepositoryLink iconOnly />
          <PaperLink className="nav-paper" />
        </nav>
      </div>
    </header>
  </>;
}
export function SiteFooter() {
  return <footer className="site-footer shell v2-footer">
    <div><SiteLink className="footer-brand" href="/"><AirlockMark className="brand-mark" />PC2 | Proof Carrying Contracts</SiteLink>
      <p>An academically backed initiative developing an open commitment protocol for AI agents.</p></div>
    <nav aria-label="Footer navigation"><SiteLink href="/overview">Overview</SiteLink><SiteLink href="/get-involved">Get involved</SiteLink><RepositoryLink iconOnly /><PaperLink /><a href="#top">Back to top <span aria-hidden="true">↑</span></a></nav>
  </footer>;
}
export function FoundationsPaper({ headingLevel = 2 }: { headingLevel?: 2 | 3 }) {
  const Heading = headingLevel === 2 ? 'h2' : 'h3';
  const { paper, implementation } = config;
  const bothReleased = implementation.status === 'released' && !!implementation.demoUrl && !!implementation.repositoryUrl;
  return <>
    <span id="technical-report" className="anchor-target" />
    <article className="paper-feature" aria-labelledby="paper-title">
      <div className="paper-feature-symbol" aria-hidden="true"><AirlockMark /><FileText size={40} strokeWidth={1.3} /></div>
      <div>
        {paperPublished && <p className="eyebrow">PC2 foundations paper</p>}
        <Heading id="paper-title">{paperPublished ? paper.title : 'PC2 foundations paper'}</Heading>
        {!paperPublished && <span className="status-label">Forthcoming</span>}
        <p>{paperPublished ? 'The paper develops the mathematical model of contracts, execution and delegation, with proofs under stated assumptions.' : c('3.5', 0).split('\n\n')[0]}</p>
        {paperPublished && paper.authors.length > 0 && <p className="paper-authors">{paper.authors.join(', ')}</p>}
        {paperPublished && paper.publishedDate && <p><time dateTime={paper.publishedDate}>{paper.publishedDate}</time></p>}
        {paperPublished && <div className="hero-actions"><a className="primary-link" href={paper.pdfUrl || paper.arxivUrl!}>Read the PC2 foundations paper <span aria-hidden="true">↗</span></a>{paper.pdfUrl && <a className="text-link" href={paper.pdfUrl}>Download PDF <span aria-hidden="true">↗</span></a>}</div>}
        <div className="implementation-release"><p>{bothReleased ? 'The demonstration and repository provide instructions for running an initial example and examining its contract and execution.' : c('3.5', 0).split('\n\n')[1]}</p>
          {(implementation.demoUrl || implementation.repositoryUrl) && <div className="release-actions">
            {implementation.demoUrl ? <a className="text-link" href={implementation.demoUrl}>Explore the demonstration ↗</a> : <span>Demonstration · Upcoming</span>}
            {implementation.repositoryUrl ? <RepositoryLink /> : <span>Repository · Upcoming</span>}
          </div>}
        </div>
      </div>
    </article>
  </>;
}
