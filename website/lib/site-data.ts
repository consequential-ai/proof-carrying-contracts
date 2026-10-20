import copy from './site-copy.json';
import rawConfig from './site-config.json';
import type { Metadata } from 'next';

export type PositionStatus = 'upcoming' | 'open' | 'closed';
export type ReleaseConfig = {
  mode: 'preview' | 'production';
  siteUrl: string | null;
  paper: { status: string; title: string | null; authors: string[]; arxivUrl: string | null; pdfUrl: string | null; publishedDate: string | null };
  implementation: { status: string; demoUrl: string | null; repositoryUrl: string | null };
  community: { updatesUrl: string | null; collaborationUrl: string | null; contactEmail: string | null; contributionInterestUrl: string | null };
  positions: Record<string, { status: PositionStatus; applicationUrl: string | null; deadline: string | null }>;
  updates: unknown[];
};
export const config = rawConfig as ReleaseConfig;
export const preview = (process.env.PC2_BUILD_MODE || config.mode) !== 'production';
export const paperPublished = config.paper.status === 'published' && !!config.paper.title && !!config.paper.arxivUrl;
export const collaborationHref = config.community.collaborationUrl || (config.community.contactEmail ? `mailto:${config.community.contactEmail}?subject=PC2%20collaboration` : null);
export const c = (section: keyof typeof copy, block: number) => copy[section].blocks[block];
export const table = (section: keyof typeof copy, index = 0) => copy[section].tables[index].slice(1);
export const statusLabel = (status: PositionStatus) => ({ upcoming: 'Call upcoming', open: 'Applications open', closed: 'Call closed' })[status];
export function positionCounts() {
  const values = Object.values(config.positions);
  const open = values.filter(p => p.status === 'open').length;
  const upcoming = values.filter(p => p.status === 'upcoming').length;
  if (!open) return `${upcoming} planned appointment${upcoming === 1 ? '' : 's'}`;
  return `${open} accepting applications${upcoming ? ` · ${upcoming} upcoming` : ''}`;
}
export function pageMetadata(title: string, description: string, route: string): Metadata {
  const base = config.siteUrl ? config.siteUrl.replace(/\/$/, '') + '/' : null;
  const path = route === '/' ? 'index.html' : `data/${route.replace(/^\//, '')}.html`;
  const canonical = base ? new URL(path, base).href : undefined;
  return {
    title: { absolute: title }, description,
    robots: { index: !preview, follow: !preview },
    ...(canonical ? {
      alternates: { canonical },
      openGraph: { title, description, url: canonical, images: [{ url: new URL('data/media/site/pc2-social-preview.png', base!).href, width: 1200, height: 630 }] },
    } : {}),
  };
}
