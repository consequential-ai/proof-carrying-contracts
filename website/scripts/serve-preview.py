"""Serve the static export locally, including single byte-range video requests."""
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import re
import argparse

ROOT = Path(__file__).resolve().parents[1]
PREVIEW = ROOT / 'outputs/pc2-website-static'

class PreviewHandler(SimpleHTTPRequestHandler):
    extensions_map = {**SimpleHTTPRequestHandler.extensions_map, '.rsc': 'text/x-component'}

    def translate_path(self, path):
        resolved = Path(super().translate_path(path))
        if resolved.exists():
            return str(resolved)
        # Keep old local preview URLs usable while serving the portable export.
        relative = resolved.relative_to(PREVIEW)
        candidate = PREVIEW / 'data' / relative
        if candidate.exists():
            return str(candidate)
        if not candidate.suffix and candidate.with_suffix('.html').is_file():
            return str(candidate.with_suffix('.html'))
        return str(resolved)

    def send_head(self):
        self.remaining = None
        header = self.headers.get('Range')
        path = Path(self.translate_path(self.path))
        if not header or not path.is_file():
            return super().send_head()
        match = re.fullmatch(r'bytes=(\d*)-(\d*)', header.strip())
        # Multiple or malformed ranges may be ignored with a full response.
        if not match or not any(match.groups()):
            return super().send_head()
        try:
            source = path.open('rb')
        except OSError:
            return super().send_head()
        size = path.stat().st_size
        first, last = match.groups()
        if first:
            start = int(first)
            end = min(int(last), size-1) if last else size-1
        else:
            start, end = max(size-int(last), 0), size-1
        if not size or start > end or start >= size:
            source.close()
            self.send_response(416)
            self.send_header('Content-Range', f'bytes */{size}')
            self.send_header('Content-Length', '0')
            self.end_headers()
            return None
        source.seek(start)
        self.remaining = end-start+1
        self.send_response(206)
        self.send_header('Content-Type', self.guess_type(str(path)))
        self.send_header('Content-Range', f'bytes {start}-{end}/{size}')
        self.send_header('Content-Length', str(self.remaining))
        self.send_header('Last-Modified', self.date_time_string(path.stat().st_mtime))
        self.end_headers()
        return source

    def end_headers(self):
        self.send_header('Accept-Ranges', 'bytes')
        self.send_header('Vary', 'RSC')
        super().end_headers()

    def copyfile(self, source, outputfile):
        if self.remaining is None:
            return super().copyfile(source, outputfile)
        while self.remaining:
            chunk = source.read(min(self.remaining, 64*1024))
            if not chunk:
                break
            outputfile.write(chunk)
            self.remaining -= len(chunk)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--port', type=int, default=3000)
    parser.add_argument('--directory', type=Path, default=PREVIEW)
    args = parser.parse_args()
    PREVIEW = args.directory.resolve()
    server = ThreadingHTTPServer(('127.0.0.1', args.port), partial(PreviewHandler, directory=str(PREVIEW)))
    print(f'Static preview: http://localhost:{args.port}/', flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
