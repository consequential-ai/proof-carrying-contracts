#!/usr/bin/env python3
"""Audit the delivered HTML, exact copy, source preservation and local assets."""
from html.parser import HTMLParser
from pathlib import Path
from collections import Counter
from urllib.parse import urlsplit,unquote
import json,re,hashlib,os
root=Path(__file__).resolve().parents[1]; export=root/'outputs/pc2-website-static'
fixtures=root/'scripts/fixtures/initial'
reports=root/'outputs/v3-checks'
reports.mkdir(parents=True,exist_ok=True)
config=json.loads((root/'lib/site-config.json').read_text())
preview=os.environ.get('PC2_BUILD_MODE',config['mode'])!='production'
class Document(HTMLParser):
 def __init__(self,text):
  super().__init__();self.tags=[];self.words=[];self.feed(text)
 def handle_starttag(self,tag,attrs):self.tags.append((tag,dict(attrs)))
 def handle_data(self,text):self.words.append(text)
def norm(text):return re.sub(r'\s+',' ',text).strip()
docs={p:Document(p.read_text()) for p in export.rglob('*.html')}
assert docs,'Build and package the website before auditing it.'
for p,doc in docs.items():
 ids=[a['id'] for t,a in doc.tags if 'id' in a]; assert all(v==1 for v in Counter(ids).values()),(p,'duplicate id')
 assert sum(t=='h1' for t,a in doc.tags)==1,p
 assert sum(t=='main' for t,a in doc.tags)==1,p
 for t,a in doc.tags:
  if t=='img':assert 'alt' in a,(p,a)
  for key in ('aria-controls','aria-labelledby','aria-describedby'):
   for id in a.get(key,'').split():assert id in ids,(p,key,id)
  for key in ('href','src','poster','srcset'):
   if key not in a:continue
   url=urlsplit(a[key]);
   if url.scheme or url.netloc:continue
   target=(p.parent/unquote(url.path)).resolve() if url.path else p
   assert target.is_file(),(p,key,a[key])
   if url.fragment and target in docs:assert url.fragment in [a.get('id') for t,a in docs[target].tags],(p,url.fragment)
  assert a.get('href')!='#',(p,'fake link')
 if p.stem!='identity':
  robots=next(a.get('content') for t,a in doc.tags if t=='meta' and a.get('name')=='robots')
  expected='noindex, nofollow' if preview else 'noindex, follow' if p.stem in ('protocol','positions') else 'index, follow'
  assert robots==expected,(p,robots)
 if config['siteUrl'] and p.stem not in ('identity','protocol','positions'):
  base=config['siteUrl'].rstrip('/')+'/'
  canonical=next(a['href'] for t,a in doc.tags if t=='link' and a.get('rel')=='canonical')
  assert canonical==base+p.relative_to(export).as_posix(),(p,canonical)
  image=next(a['content'] for t,a in doc.tags if t=='meta' and a.get('property')=='og:image')
  assert image==base+'data/media/site/pc2-social-preview.png',(p,image)
copy=json.loads((root/'lib/site-copy.json').read_text())
# Authored copy is compared with rendered public text, including each paragraph.
for page,prefix in [('index.html','3.'),('data/overview.html','4.'),('data/get-involved.html','5.')]:
 public=norm(' '.join(docs[export/page].words))
 for section,data in copy.items():
  if not section.startswith(prefix):continue
  for i,block in enumerate(data['blocks']):
   if section=='3.6' and i==2:
    for label in block.splitlines():assert label in public
    continue
   for paragraph in block.split('\n\n'):
    assert norm(paragraph) in public,(page,section,i,paragraph[:60])
# Job text changes must be reproducible from the approved editorial ledger.
def baseline(name):return (fixtures/name).read_bytes()
before=json.loads(baseline('lib/position-details.json'));after=json.loads((root/'lib/position-details.json').read_text())
for edit in json.loads((root/'docs/v3-job-prose-edits.json').read_text()):
 role=edit['role'];before[role]=before[role].replace(edit['before'],edit['after'])
assert before==after,'Unlogged role text edits'
# Markup, section IDs, roles, cities, supervisors, eligibility structure are retained.
old=json.loads(baseline('lib/position-details.json'))
for role in old:
 assert re.findall(r'<[^>]+>',old[role])==re.findall(r'<[^>]+>',after[role]),role
for name,digest in json.loads((fixtures/'media-sha256.json').read_text()).items():
 assert digest==hashlib.sha256((root/name).read_bytes()).hexdigest(),name
for name in ['lib/overview-film.json','public/media/overview/pc2-overview.vtt','public/media/overview/pc2-overview.txt']:
 assert baseline(name).decode().replace('Proof-Carrying','Proof Carrying')==(root/name).read_text(),name
assert baseline('lib/positions.ts').decode().replace('Multi-Agent','Multiagent')==(root/'lib/positions.ts').read_text()
home=(export/'index.html').read_text();assert '.mp4' not in home and '.mp3' not in home and 'film.js' not in home
assert {p.stem for p in (export/'data/positions').glob('*.html')}==set(config['positions'])
# WCAG luminance for every text token on all supplied flat surfaces.
def lum(colour):
 values=[int(colour[i:i+2],16)/255 for i in (1,3,5)]
 values=[v/12.92 if v<=.04045 else ((v+.055)/1.055)**2.4 for v in values]
 return sum(v*w for v,w in zip(values,(.2126,.7152,.0722)))
contrasts={}
for fg in ['#242820','#62645c','#b63b29','#4e6472','#37645d']:
 for bg in ['#faf9f6','#f0f0ea','#ebe6dc','#f1f2ee']:
  a,b=sorted([lum(fg),lum(bg)]);ratio=(b+.05)/(a+.05);assert ratio>=4.5,(fg,bg,ratio);contrasts[f'{fg}/{bg}']=round(ratio,2)
class Prose(HTMLParser):
 def __init__(self,text):
  super().__init__();self.text=[];self.ignore=0;self.feed(text)
 def handle_starttag(self,t,attrs):
  a=dict(attrs)
  if t in ('script','style','code','pre'):self.ignore+=1
  if not self.ignore:
   for key in ('alt','aria-label','title'):
    if a.get(key):self.text.append(a[key])
   if t=='meta' and (a.get('name')=='description' or a.get('property') in ('og:title','og:description','og:site_name','og:image:alt')):self.text.append(a.get('content',''))
 def handle_endtag(self,t):
  if t in ('script','style','code','pre'):self.ignore-=1
 def handle_data(self,t):
  if not self.ignore:self.text.append(t)
stale=['Paper forthcoming','The foundations have to work in practice.','One task. Different principals.','Give the undertaking a precise meaning.','Delegate the work, not the right to break the agreement.','A commitment layer, not a replacement for the stack.','Make the commitment practical.','Inspect the foundations. Follow the implementation.','Different expertise. A shared direction.']
issues=[]
for p in [*docs.keys(),*(export/'data/media/site').glob('*.svg')]:
 if p.stem=='identity':continue
 prose=Prose(p.read_text()).text
 for t in prose:
  # Published titles and established technical terms retain their exact spelling.
  editorial_text=t.replace(config['paper']['title'],'publication title') if config['paper']['title'] else t
  editorial_text=re.sub(r'\b(?:multi-principal|PC2-Bench|machine-checked|held-out|self-evaluation|e-mail|sub-agents?)\b','technical term',editorial_text,flags=re.I)
  if re.search(r'[-\u2010-\u2015]',editorial_text):issues.append((str(p.relative_to(export)),'dash',t))
  if re.search(r'\bnot\s+(?:just|only)\b|\brather than\b|\bnot\b[^.!?]{0,100}\bbut\b',t,re.I):issues.append((str(p.relative_to(export)),'contrast',t))
 for old in stale:
  if old in ' '.join(prose):issues.append((str(p.relative_to(export)),'stale',old))
(reports/'prose-audit.json').write_text(json.dumps(issues,indent=2))
assert not issues,issues
report={'pages':len(docs),'roles':7,'exact_v3_copy':'passed','controlled_job_edits':'passed','film_and_timing_preserved':'passed','local_references':'passed','accessibility_markup':'passed','contrast':contrasts}
(reports/'export-checks.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
