import type { Metadata } from 'next';
import { SiteLink } from '@/components/site-link';
import { notFound } from 'next/navigation';
import { SiteHeader, SiteFooter, Arrow } from '@/components/site-chrome';
import { positions } from '@/lib/positions';
import details from '@/lib/position-details.json';
import { config, statusLabel, pageMetadata } from '@/lib/site-data';

type Props = { params: Promise<{ slug: string }> };
export function generateStaticParams() {
  return positions.map(({ slug }) => ({ slug }));
}
export const dynamicParams = false;

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const { slug } = await params;
  const position = positions.find((item) => item.slug === slug);
  return pageMetadata(position ? `${position.title} | ${position.city}` : 'Position not found', position?.description || '', `/positions/${slug}`);
}

export default async function PositionPage({ params }: Props) {
  const { slug } = await params;
  const position = positions.find((item) => item.slug === slug);
  if (!position) notFound();
  return (
    <>
      <SiteHeader active="get-involved" />
      <main id="main">
        <section
          className="subpage-hero role-hero shell"
          id="top"
          aria-labelledby="role-title"
        >
          <SiteLink className="role-back" href="/get-involved#open-positions">
            ← All positions
          </SiteLink>
          <p className="eyebrow">{position.type}</p>
          <h1 id="role-title">{position.title}</h1>
          <div className="role-facts">
            <span>{position.host}</span>
            <span>{position.city}</span>
            <span>Full time · Two years</span>
          </div>
          <p className="status-label">{statusLabel(config.positions[slug].status)}</p>
          {config.positions[slug].status === 'open' && config.positions[slug].applicationUrl && <p><a className="text-link" href={config.positions[slug].applicationUrl!}>Application instructions <Arrow /></a></p>}
          {config.positions[slug].deadline && <p>Deadline: <time dateTime={config.positions[slug].deadline!}>{config.positions[slug].deadline}</time></p>}
          <p className="subpage-intro">{position.description}</p>
          <a
            className="text-link section-link"
            href={`#${position.id}-how-to-apply`}
          >
            Application materials <Arrow down />
          </a>
        </section>
        <div className="section shell">
          {/* Static, locally extracted role copy; no scripts or user-submitted HTML. */}
          <div
            className="role-content reading-column"
            dangerouslySetInnerHTML={{
              __html: details[position.id as keyof typeof details],
            }}
          />
        </div>
      </main>
      <SiteFooter />
    </>
  );
}
