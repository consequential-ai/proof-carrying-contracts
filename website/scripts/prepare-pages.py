#!/usr/bin/env python3
"""Stage the portable export as the GitHub Pages artifact."""
import html
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'outputs/pc2-website-static'
DESTINATION = ROOT / 'outputs/github-pages'
config = json.loads((ROOT / 'lib/site-config.json').read_text())

assert (SOURCE / 'index.html').is_file(), 'Run the static export first.'
assert config['siteUrl'], 'GitHub Pages requires a configured public site URL.'
if DESTINATION.exists():
    shutil.rmtree(DESTINATION)
shutil.copytree(SOURCE, DESTINATION)

# The logo study belongs to local design review, not the deployed website.
(DESTINATION / 'data/identity.html').unlink(missing_ok=True)
(DESTINATION / 'data/README.txt').unlink(missing_ok=True)
(DESTINATION / '.nojekyll').touch()

home = html.escape(config['siteUrl'].rstrip('/') + '/', quote=True)
(DESTINATION / '404.html').write_text(f'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="robots" content="noindex, nofollow">
  <title>Page not found | Proof Carrying Contracts</title>
  <style>
    body {{ max-width: 42rem; margin: 12vh auto; padding: 1.5rem;
      background: #faf9f6; color: #242820; font: 1.125rem/1.75 system-ui, sans-serif; }}
    a {{ color: #b63b29; }}
  </style>
</head>
<body>
  <main>
    <p>PC² · Proof Carrying Contracts</p>
    <h1>Page not found</h1>
    <p>The requested page could not be found.</p>
    <a href="{home}">Return to the homepage</a>
  </main>
</body>
</html>
''')
print(f'GitHub Pages artifact: {DESTINATION}')
