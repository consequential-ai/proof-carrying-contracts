/* oxlint-disable typescript/no-implied-eval -- Compile only trusted local TSX to test actual server components with isolated release data. */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { createRequire } from 'node:module';
import ts from 'typescript';
import React from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { validateRelease } from './check-release.mjs';
const require = createRequire(import.meta.url);
const root = process.cwd();
const release = JSON.parse(fs.readFileSync('lib/site-config.json'));
assert.deepEqual(validateRelease(release), []);
const original = JSON.parse(fs.readFileSync('scripts/fixtures/unreleased-site-config.json'));
// Render the actual server components against isolated data. Never write test URLs
// into the site's configuration or public export.
function loader(config) {
  const cache = new Map();
  function load(id, from = root + '/test.ts') {
    if (id === 'next/image') return ({unoptimized: _unused, ...props}) => React.createElement('img', props);
    if (id === 'next/navigation') return {notFound(){throw Error('Not found');}};
    if (!id.startsWith('.') && !id.startsWith('@/') && !id.startsWith('/')) return require(id);
    const base = id.startsWith('@/') ? path.join(root,id.slice(2)) : path.resolve(path.dirname(from),id);
    const filename = ['', '.ts', '.tsx', '.json'].map(ext=>base+ext).find(p=>fs.existsSync(p)&&fs.statSync(p).isFile());
    assert(filename, id);
    if (filename.endsWith('/site-config.json')) return config;
    if (filename.endsWith('.json')) return JSON.parse(fs.readFileSync(filename));
    if (cache.has(filename)) return cache.get(filename).exports;
    const compiled = {exports:{}}; cache.set(filename,compiled);
    const js = ts.transpileModule(fs.readFileSync(filename,'utf8'),{compilerOptions:{module:ts.ModuleKind.CommonJS,jsx:ts.JsxEmit.ReactJSX,esModuleInterop:true,target:ts.ScriptTarget.ES2022}}).outputText;
    new Function('require','module','exports',js)(child=>load(child,filename),compiled,compiled.exports);
    return compiled.exports;
  }
  return load;
}
const defaults=loader(original);
assert.deepEqual(validateRelease(original),[]);
assert.equal(validateRelease(original,'production').length,3);
const defaultPage=renderToStaticMarkup(React.createElement(defaults('@/app/get-involved/page').default));
assert(defaultPage.includes('7 planned appointments'));
assert(!defaultPage.includes('Application instructions</a>'));
assert(defaultPage.includes('A project contact route will be added before public launch.'));
assert(defaultPage.includes('Contribution instructions forthcoming'));
const sample=structuredClone(original);
sample.mode='production'; sample.siteUrl='https://example.org/PC2/';
sample.paper={status:'published',title:'TEST FIXTURE: approved title',arxivUrl:'https://arxiv.org/abs/2601.00001',pdfUrl:'https://arxiv.org/pdf/2601.00001',authors:['Test Author'],publishedDate:'2026-09-15'};
sample.community={updatesUrl:'https://example.org/updates',collaborationUrl:'https://example.org/contact',contactEmail:null,contributionInterestUrl:'https://example.org/test'};
sample.implementation={status:'released',demoUrl:'https://example.org/demo',repositoryUrl:'https://example.org/repo'};
Object.values(sample.positions).slice(0,2).forEach(role=>{role.status='open';role.applicationUrl='https://example.org/apply';});
assert.deepEqual(validateRelease(sample),[]);
const configured=loader(sample);
const involvement=renderToStaticMarkup(React.createElement(configured('@/app/get-involved/page').default));
assert(involvement.includes('2 accepting applications · 5 upcoming'));
for(const url of Object.values(sample.community).filter(Boolean)) assert(involvement.includes(`href="${url}"`));
const overview=renderToStaticMarkup(React.createElement(configured('@/app/overview/page').default));
for(const url of [sample.paper.pdfUrl,sample.implementation.demoUrl,sample.implementation.repositoryUrl]) assert(overview.includes(`href="${url}"`));
assert(overview.includes(sample.paper.title)); assert(!overview.includes('PC2 foundations paper (forthcoming)')); assert(overview.includes('Read the PC2 foundations paper'));
const meta=configured('@/lib/site-data').pageMetadata('Test','Test','/positions/contract-calculi-turin');
assert.equal(meta.alternates.canonical,'https://example.org/PC2/data/positions/contract-calculi-turin.html');
assert.equal(meta.openGraph.images[0].url,'https://example.org/PC2/data/media/site/pc2-social-preview.png');
assert.equal(meta.robots.index,true);
sample.community.collaborationUrl=null; sample.community.contactEmail='test@example.org';
assert(loader(sample)('@/lib/site-data').collaborationHref==='mailto:test@example.org?subject=PC2%20collaboration');
sample.positions['contract-calculi-milan'].status='closed';
const closed=renderToStaticMarkup(React.createElement(loader(sample)('@/app/get-involved/page').default));
assert(!closed.includes('href="/positions/contract-calculi-milan"'));
sample.positions['agent-safety-infrastructure'].applicationUrl=null;
assert(validateRelease(sample).some(s=>s.includes('Open role needs')));
sample.updates=[{title:'unbuilt'}]; assert(validateRelease(sample).some(s=>s.includes('destination pages')));
for(const slug of Object.keys(original.positions)) {
 const element=await defaults('@/app/positions/[slug]/page').default({params:Promise.resolve({slug})});
 const html=renderToStaticMarkup(element);
 assert(html.includes('Call upcoming')); assert(html.includes('href="/get-involved#open-positions"'));
}
console.log('PASS: real server-component renders for null, published, mixed-call, closed-call and email fallback states; metadata subpaths; seven roles; production release blockers. Test URLs remain isolated.');
