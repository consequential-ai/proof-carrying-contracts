"""Embed the exported experiment page and its assets in one shareable HTML file."""
import base64
import html
import mimetypes
from pathlib import Path
import re
from urllib.parse import urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
PAGE = ROOT / 'outputs/github-pages/data/experiments.html'
OUTPUT = ROOT / 'outputs/pc2-experiments.html'
PUBLIC_PAGE = 'https://consequential-ai.github.io/proof-carrying-contracts/data/experiments.html'


def embedded(path):
    mime = mimetypes.guess_type(path.name)[0] or 'application/octet-stream'
    return 'data:' + mime + ';base64,' + base64.b64encode(path.read_bytes()).decode('ascii')


def stylesheet(match):
    return '<style>' + (PAGE.parent / html.unescape(match.group(1))).read_text() + '</style>'


def script(match):
    source = (PAGE.parent / html.unescape(match.group(1))).read_text()
    return '<script>' + source.replace('</script', '<\\/script') + '</script>'


def tag(match):
    value = match.group(0)
    ref = re.search(r'\b(href|src)="([^"]+)"', value)
    if not ref:
        return value
    name, raw = ref.groups()
    url = html.unescape(raw)
    parsed = urlsplit(url)
    if parsed.scheme or parsed.netloc or not parsed.path:
        return value
    if parsed.path.endswith('.html'):
        replacement = '#top' if parsed.path == 'experiments.html' else urljoin(PUBLIC_PAGE, url)
    else:
        local = PAGE.parent / parsed.path
        replacement = embedded(local)
        if value.startswith('<a '):
            value = re.sub(r'\s(?:target|rel|download)="[^"]*"', '', value)
            value = value[:-1] + ' download="' + html.escape(local.name, quote=True) + '">'
    return value.replace(name + '="' + raw + '"', name + '="' + html.escape(replacement, quote=True) + '"')


def main():
    text = PAGE.read_text()
    text = re.sub(r'<link\b[^>]*rel="stylesheet"[^>]*href="([^"]+)"[^>]*>', stylesheet, text)
    text = re.sub(r'<script\b[^>]*src="([^"]+)"[^>]*>\s*</script>', script, text)
    text = re.sub(r'<(?:a|img|link)\b[^>]*>', tag, text)
    text = text.replace('Open the full size chart', 'Download the full size chart')
    text = text.replace('View the full-size chart', 'Download the full-size chart')
    text = text.replace('View the resource comparison chart', 'Download the resource comparison chart')
    OUTPUT.write_text(text)
    print(f'{OUTPUT} ({OUTPUT.stat().st_size / 1024 / 1024:.2f} MB)')


if __name__ == '__main__':
    main()
