# PC2 website

This directory contains the source for the
[PC2 website](https://consequential-ai.github.io/proof-carrying-contracts/):
the project introduction, protocol overview and film, participation information,
and seven individual role descriptions.

## Development and deployment

Use Node.js 22.13 or newer and Python 3.10 or newer. From this directory, run:

```sh
npm ci
npm run export:pages
npm run check:v3
python3 scripts/serve-preview.py --directory outputs/github-pages
```

Open <http://localhost:3000/>. For source development, `npm run dev` is also
available.

The [Website workflow](../.github/workflows/deploy-pages.yml) builds and checks
changes on pull requests. Changes to `website/` on `main` are automatically
published through GitHub Actions to GitHub Pages. The workflow can also be run
manually from the repository's Actions tab. GitHub Pages must use **GitHub
Actions** as its build source.

Only the generated `outputs/github-pages/` directory is deployed.
Navigation and asset URLs are relative, so they work beneath the repository
prefix. The primary page URLs are:

- `/proof-carrying-contracts/`
- `/proof-carrying-contracts/data/overview.html`
- `/proof-carrying-contracts/data/get-involved.html`
- `/proof-carrying-contracts/data/positions/<role>.html`

The internal logo study is retained in the source and portable preview, but is
excluded from the Pages artifact. The film, captions, transcript, fonts and
illustrations are served as static files.

## Publication state

The deployed site is a publicly accessible draft. Its pages request
`noindex, nofollow`; this is a search-engine directive, not access control.

[`lib/site-config.json`](lib/site-config.json) sets the public URL, publication
mode, paper links, collaboration route and vacancy states. The foundations-paper
links open the [latest arXiv PDF](https://arxiv.org/pdf/2610.28484) directly. A
contact route is still forthcoming, and all seven roles are marked upcoming.

Before switching `mode` to `production`, add a collaboration URL or contact
email. The paper title, publication status and arXiv URLs are configured. The
build validates these requirements. An open vacancy also requires
its approved application URL. No dates or URLs are inferred.

## Editing

| Source | Purpose |
| --- | --- |
| `lib/site-copy.json` | Website text |
| `lib/site-config.json` | Publication and vacancy configuration |
| `app/` | Pages and styles |
| `components/` | Shared page components |
| `public/` | Retained media and logos |
| `scripts/` | Static packaging, diagram generation and checks |

`npm run check:v3` verifies rendered copy, approved job edits, film preservation,
local references, accessibility markup, specified text contrast combinations,
release states, chapter timing and TypeScript. It runs without a preview server
or access to the original local repository.

The repository's existing [license](../LICENSE) is retained. Bundled font licenses
are in `scripts/static-licenses/` and are included in the deployed files.
