"""Shared native SVG typography, boxes and connectors for Overview figures."""
import base64
import html
from pathlib import Path

INK = '#242820'
SLATE = '#4e6472'
RED = '#b63b29'
GREEN = '#37645d'
PAPER = '#faf9f6'
RULE = '#d7d8d0'
MUTED = '#62645c'


def text(x, y, words, size=20, color=INK, weight=400, anchor='middle'):
    lines = words.split('|')
    spans = ''.join(f'<tspan x="{x}" dy="{0 if i == 0 else size * 1.3}">{html.escape(line)}</tspan>' for i, line in enumerate(lines))
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-size="{size}" font-weight="{weight}" fill="{color}">{spans}</text>'


def line(d, color=SLATE, arrow=False, width=1.8):
    marker = f' marker-end="url(#{"accepted" if color == GREEN else "blocked" if color == RED else "flow"})"' if arrow else ''
    return f'<path d="{d}" fill="none" stroke="{color}" stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"{marker}/>'


def box(x, y, w, h, label, size=21, stroke=SLATE, weight=400):
    rows = label.count('|') + 1
    baseline = y + h / 2 - (rows - 1) * size * 1.3 / 2 + size * .35
    return (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="3" '
            f'fill="{PAPER}" stroke="{stroke}" stroke-width="1.6"/>'
            + text(x + w / 2, baseline, label, size, weight=weight))


def frame(w, h, body, description, root, title='The proof check controls the tool call'):
    font = base64.b64encode((root / 'design/v2/geist-latin.woff2').read_bytes()).decode('ascii')
    markers = ''.join(f'<marker id="{name}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M2 1L8 5L2 9" fill="none" stroke="{color}" stroke-width="1.5"/></marker>' for name, color in [('flow', SLATE), ('accepted', GREEN), ('blocked', RED)])
    return f'''<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}" role="img" aria-labelledby="title desc">
<title id="title">{html.escape(title)}</title><desc id="desc">{html.escape(description)}</desc>
<defs><style>@font-face{{font-family:Geist;src:url(data:font/woff2;base64,{font}) format('woff2');font-weight:100 900}}text{{font-family:Geist,Arial,sans-serif}}</style>{markers}</defs>
<rect width="{w}" height="{h}" fill="{PAPER}"/>{body}</svg>'''
