import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
export function validateRelease(config, mode = config.mode) {
  const errors = [];
  const https = value => { try { return new URL(value).protocol === 'https:'; } catch { return false; } };
  if (!['preview','production'].includes(mode)) errors.push('Mode must be preview or production.');
  const urlValues = [config.siteUrl, config.paper.arxivUrl, config.paper.pdfUrl, config.implementation.demoUrl, config.implementation.repositoryUrl, ...Object.entries(config.community).filter(([k])=>k.endsWith('Url')).map(([,v])=>v)];
  for (const url of urlValues) if (url && !https(url)) errors.push(`Release URL must use HTTPS: ${url}`);
  const date = value => /^\d{4}-\d{2}-\d{2}$/.test(value) && !Number.isNaN(Date.parse(value)) && new Date(value).toISOString().slice(0,10) === value;
  if (config.paper.publishedDate && !date(config.paper.publishedDate)) errors.push('Paper publication date must be an actual ISO date.');
  const published = config.paper.status === 'published';
  if (published && (!config.paper.title || !config.paper.arxivUrl)) errors.push('Published paper requires its approved title and arXiv URL.');
  if (config.paper.arxivUrl && !/^https:\/\/arxiv\.org\/(abs|html)\//.test(config.paper.arxivUrl)) errors.push('Paper URL must be a direct arXiv article URL.');
  if (config.community.contactEmail && !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(config.community.contactEmail)) errors.push('Contact email must be a complete approved address.');
  for (const [slug, role] of Object.entries(config.positions)) {
    if (!['upcoming','open','closed'].includes(role.status)) errors.push(`Invalid role status: ${slug}`);
    if (role.applicationUrl && !https(role.applicationUrl)) errors.push(`Application URL must use HTTPS: ${slug}`);
    if (role.status === 'open' && !role.applicationUrl) errors.push(`Open role needs an approved application URL: ${slug}`);
    if (role.deadline && !date(role.deadline)) errors.push(`Deadline must be an actual ISO date: ${slug}`);
  }
  if (config.updates.length) errors.push('Implement and verify article destination pages before adding update records.');
  if (mode === 'production') {
    if (!published || !config.paper.title || !config.paper.arxivUrl) errors.push('Public launch requires the published paper title and arXiv URL.');
    if (!config.community.collaborationUrl && !config.community.contactEmail) errors.push('Public launch requires an approved collaboration route.');
    if (!config.siteUrl) errors.push('Public launch requires the approved production site URL.');
  }
  return errors;
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const config = JSON.parse(fs.readFileSync(new URL('../lib/site-config.json',import.meta.url)));
  const mode = process.argv.includes('--production') ? 'production' : process.env.PC2_BUILD_MODE || config.mode;
  const errors = validateRelease(config, mode);
  if (errors.length) { console.error(errors.join('\n')); process.exitCode=1; }
  else console.log(`Release configuration validated (${mode}). No deployment is performed.`);
}
