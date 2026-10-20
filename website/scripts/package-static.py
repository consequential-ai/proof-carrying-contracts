#!/usr/bin/env python3
"""Package the built site for file:// use, with index.html and data/ at ZIP root."""
import base64
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
from urllib.parse import unquote, urlsplit, urlunsplit
from zipfile import ZipFile, ZIP_DEFLATED

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'dist/client'
OUTPUT = ROOT / 'outputs/pc2-website-static.zip'
EXPORT = ROOT / 'outputs/pc2-website-static'


class References(HTMLParser):
    def __init__(self):
        super().__init__()
        self.refs = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        for name in ('src', 'href', 'poster', 'srcset'):
            if attrs.get(name):
                self.refs.append(attrs[name])


def parse_html(text):
    parser = References()
    parser.feed(text)
    return parser


def seconds(value):
    hours, minutes, secs = value.split(':')
    return int(hours) * 3600 + int(minutes) * 60 + float(secs)


def build_package(destination):
    data = destination / 'data'
    data.mkdir()
    copied = set()
    pages = {}
    routes = {}
    # The original hiring review document is superseded by styled role pages.
    for source in sorted(BUILD.rglob('*.html')):
        relative = source.relative_to(BUILD)
        if relative.parts[0] in ('404', '404.html', '_not-found', '_next', 'job-descriptions.html'):
            continue
        output = Path('index.html') if relative == Path('index.html') else Path('data') / relative
        if relative == Path('index.html'):
            route = '/'
        elif relative.name == 'index.html':
            route = '/' + relative.parent.as_posix()
        else:
            route = '/' + relative.with_suffix('').as_posix()
        routes[route] = output
        routes[route.rstrip('/') + '/'] = output
        routes[route.rstrip('/') or '/'] = output
        routes['/' + relative.as_posix()] = output
        pages[output] = source.read_text()
    assert Path('index.html') in pages and '/get-involved/' in routes and '/overview/' in routes

    def copy_asset(url):
        path = unquote(urlsplit(url).path).lstrip('/')
        source = (BUILD / path).resolve()
        assert source.is_relative_to(BUILD.resolve()) and source.is_file(), url
        target = data / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if path not in copied:
            shutil.copyfile(source, target)
            copied.add(path)
        return Path('data') / path

    css_links = []
    font_styles = []
    for page in pages.values():
        css_links.extend(re.findall(r'<link\b[^>]*rel="stylesheet"[^>]*href="([^"]+)"[^>]*>', page))
        font_styles.extend(re.findall(r'<style\b[^>]*>(.*?)</style\s*>', page, re.S | re.I))
    assert css_links and font_styles
    css = '\n'.join((BUILD / url.lstrip('/')).read_text() for url in dict.fromkeys(css_links))
    css += '\n' + '\n'.join(dict.fromkeys(font_styles))

    def embed_font(match):
        url = match.group(1).strip('\'" ')
        if url.startswith('data:font/woff2;base64,'): return match.group(0)
        assert url.endswith('.woff2') and url.startswith('/_next/'), url[:120]
        encoded = base64.b64encode((BUILD / url.lstrip('/')).read_bytes()).decode('ascii')
        return 'url("data:font/woff2;base64,' + encoded + '")'

    # Embedded fonts avoid restrictions on cross-origin font requests via file://.
    css = re.sub(r'url\(([^)]+)\)', embed_font, css)
    (data / 'styles.css').write_text(css)

    for output, page in pages.items():
        page = re.sub(r'<(?:script|style)\b[^>]*>.*?</(?:script|style)\s*>', '', page, flags=re.S | re.I)
        page = re.sub(r'<link\b(?=[^>]*rel="(?:stylesheet|modulepreload|preload)")[^>]*>', '', page, flags=re.I)
        page = re.sub(r'<!--.*?-->', '', page, flags=re.S)
        page = re.sub(r'\sdata-(?:nimg|rsc-css-href|precedence)="[^"]*"', '', page)

        def relative_to_page(target):
            return os.path.relpath(destination / target, (destination / output).parent)

        def rewrite_reference(match):
            name, url = match.group(1), urlsplit(html.unescape(match.group(2)))
            path = unquote(url.path)
            target = routes[path] if path in routes else copy_asset(url.path)
            rewritten = urlunsplit(('', '', relative_to_page(target), url.query, url.fragment))
            return name + '="' + html.escape(rewritten, quote=True) + '"'

        page = re.sub(r'\b(src|href|poster|srcset)="(/(?!/)[^"]*)"', rewrite_reference, page, flags=re.I)
        page = page.replace('</head>', f'<link rel="stylesheet" href="{relative_to_page(Path("data/styles.css"))}">\n</head>')
        scripts = [Path('data/site-v2.js')]
        if 'id="pc2-overview-video"' in page:
            assert output == Path('data/overview.html'), 'The film belongs on Overview.'
            scripts.append(Path('data/film.js'))
        tags = ''.join(f'<script src="{relative_to_page(script)}" defer></script>' for script in scripts)
        page = page.replace('</body>', tags + '\n</body>')
        target = destination / output
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(page)
        assert '_next/' not in page and 'localhost' not in page and 'type="module"' not in page

    timeline = json.loads((ROOT / 'lib/overview-film.json').read_text())
    for state in timeline['states']:
        copy_asset('/media/overview/' + state['id'] + '.jpg')
    for extension in ('mp3', 'vtt', 'txt'):
        copy_asset('/media/overview/pc2-overview.' + extension)
    vtt = (data / 'media/overview/pc2-overview.vtt').read_text()
    cues = []
    for block in re.split(r'\n\s*\n', vtt.strip()):
        lines = block.splitlines()
        for index, line in enumerate(lines):
            if ' --> ' in line:
                start, end = line.split(' --> ')
                cues.append({'start': seconds(start), 'end': seconds(end), 'text': '\n'.join(lines[index + 1:])})
    assert cues and all(cue['start'] < cue['end'] <= timeline['duration'] for cue in cues)
    shutil.copyfile(ROOT / 'public/film.js', data / 'film.js')
    shutil.copyfile(ROOT / 'public/site-v2.js', data / 'site-v2.js')
    copy_asset('/media/site/pc2-social-preview.png')
    shutil.copytree(ROOT / 'scripts/static-licenses', data / 'licenses')
    config = json.loads((ROOT / 'lib/site-config.json').read_text())
    if config['siteUrl']:
        base = config['siteUrl'].rstrip('/') + '/'
        public_pages = [path for path in pages if path.stem not in ('protocol', 'positions', 'identity')]
        entries = ''.join('<url><loc>' + html.escape(base + path.as_posix()) + '</loc></url>' for path in public_pages)
        (data / 'sitemap.xml').write_text('<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">' + entries + '</urlset>')

    (data / 'README.txt').write_text(
        'Proof-Carrying Contracts Protocol — website draft\n\n'
        'Extract the entire ZIP, then open index.html in a modern web browser.\n'
        'Keep index.html and its data folder together. No installation or server is needed.\n'
        'Public pages: Home, Overview, Get involved, and seven individual role descriptions.\n'
        'The narrated film is on Overview. Old protocol/positions links remain compatible.\n'
        'The unlinked identity study is for internal review only.\n'
        'The narrated video, captions, transcript, and fonts work offline.\n'
        'Institution and other external links require an internet connection.\n'
    )
    documents = {path.resolve(): parse_html(path.read_text()) for path in destination.rglob('*.html')}
    for path, document in documents.items():
        for reference in document.refs:
            url = urlsplit(reference)
            if url.scheme or url.netloc:
                continue
            assert not url.path.startswith('/'), (path, reference)
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            assert target.is_relative_to(destination.resolve()) and target.is_file(), (path, reference)
            if url.fragment and target in documents:
                assert unquote(url.fragment) in documents[target].ids, (path, reference)
    assert set(path.name for path in destination.iterdir()) == {'index.html', 'data'}
    return len(documents), len(cues), len(timeline['chapters'])


if __name__ == '__main__':
    OUTPUT.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='pc2-static-') as temporary:
        destination = Path(temporary)
        pages, cues, chapters = build_package(destination)
        if EXPORT.exists(): shutil.rmtree(EXPORT)
        shutil.copytree(destination, EXPORT)
        with ZipFile(OUTPUT, 'w', compression=ZIP_DEFLATED, compresslevel=9) as archive:
            for path in sorted(destination.rglob('*')):
                if path.is_file():
                    archive.write(path, path.relative_to(destination))
        with ZipFile(OUTPUT) as archive:
            assert archive.testzip() is None
            count = len(archive.namelist())
    print(f'Created {OUTPUT}\n{OUTPUT.stat().st_size / 1024**2:.2f} MiB · {count} files · {pages} pages · {chapters} chapters · {cues} caption cues')
