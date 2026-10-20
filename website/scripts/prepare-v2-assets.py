#!/usr/bin/env python3
"""Build the v3 diagrams as native SVG geometry and preserve the film timing.

The historic filename is retained as the existing build entry point. All three
Overview schematics share native SVG primitives and the retained Geist subset.
"""
from pathlib import Path
import html, json, re
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'public/media/site'
COPY=json.loads((ROOT/'lib/site-copy.json').read_text())
INK='#242820'; SLATE='#4e6472'; TEAL='#37645d'; RED='#b63b29'; RULE='#cbd1cd'; PAPER='#faf9f6'; TINT='#edf2ef'
def esc(s): return html.escape(s,quote=True)
def txt(x,y,s,size=24,color=INK,weight=400,anchor='middle'):
    lines=s.split('|')
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" fill="{color}" font-size="{size}" font-weight="{weight}">'+''.join(f'<tspan x="{x}" dy="{0 if i==0 else size*1.25}">{esc(line)}{" " if i<len(lines)-1 else ""}</tspan>' for i,line in enumerate(lines))+'</text>'
def path(d,color=SLATE,arrow=True,dash=False):
    marker='teal' if color==TEAL else 'slate'
    end=f'marker-end="url(#arrow-{marker})"' if arrow else ''
    dotted='stroke-dasharray="6 5"' if dash else ''
    return f'<path d="{d}" fill="none" stroke="{color}" stroke-width="2" stroke-linejoin="round" {dotted} {end}/>'
def mark(x,y,size=64): return f'<g transform="translate({x} {y}) scale({size/64})" stroke="{RED}" stroke-width="3" fill="none"><path d="M17 12H8V52H17M47 12H56V52H47M25 22V42M25 32H42"/></g>'
def svg(w,h,body,title,desc):
    markers=''.join(f'<marker id="arrow-{n}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M1 1L9 5L1 9" fill="none" stroke="{c}" stroke-width="1.5"/></marker>' for n,c in [('slate',SLATE),('teal',TEAL)])
    return f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}" role="img" aria-labelledby="title desc"><title id="title">{esc(title)}</title><desc id="desc">{esc(desc)}</desc><defs><style>text{{font-family:Arial,Helvetica,sans-serif}}</style>{markers}</defs>{body}</svg>'
# Homepage illustrations are retained assets; only Overview diagrams are generated.
from agreement_figures import prepare_formation, prepare_delegation
from execution_figure import prepare_execution
prepare_formation(ROOT, COPY['6.5']['blocks'][1])
prepare_execution(ROOT, COPY['6.6']['blocks'][1])
prepare_delegation(ROOT, COPY['6.7']['blocks'][1])
# Build the unchanged playback implementation with editable caption orthography.
def seconds(s):
    h,m,ss=s.split(':'); return int(h)*3600+int(m)*60+float(ss)
vtt=(ROOT/'public/media/overview/pc2-overview.vtt').read_text(); cues=[]
for block in re.split(r'\n\s*\n',vtt.strip()):
    lines=block.splitlines()
    for i,line in enumerate(lines):
        if ' --> ' in line:
            a,b=line.split(' --> '); cues.append({'start':seconds(a),'end':seconds(b),'text':'\n'.join(lines[i+1:])})
film={'timeline':json.loads((ROOT/'lib/overview-film.json').read_text()),'cues':cues}
(ROOT/'public/film.js').write_text('const pc2FilmData = '+json.dumps(film,ensure_ascii=False)+';\n'+(ROOT/'scripts/static-film.js').read_text())
social=f'<rect width="1200" height="630" fill="{PAPER}"/>'+mark(72,60,80)+txt(180,118,'PC²',54,weight=500,anchor='start')
social+=f'<text x="80" y="283" fill="{INK}" style="font-family:Georgia,serif" font-size="82">Proof Carrying<tspan x="80" dy="91">Contracts</tspan></text>'
social+=path('M80 428H1120',arrow=False)+txt(80,503,'A commitment layer for the agent economy.',34,anchor='start')
(ROOT/'design/v2/pc2-social-preview.svg').write_text(svg(1200,630,social,'Proof Carrying Contracts','A commitment layer for the agent economy.'))
print('Prepared three responsive overview figures and film enhancements; homepage illustrations retained.')
