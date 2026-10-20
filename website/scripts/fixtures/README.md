# Regression fixtures

`initial/` preserves the approved job descriptions, role data and film metadata
from local website checkpoint `10d2039`. The audio and video are represented by
their SHA-256 hashes to avoid duplicating large media files.

The export audit applies `docs/v3-job-prose-edits.json` to these descriptions and
checks the resulting content, structure and unchanged film against the current
source. These fixtures replace a dependency on the original local Git history,
so the checks also run in a fresh clone and in GitHub Actions.

`unreleased-site-config.json` is the original empty release configuration used
by the server-component tests. It keeps hypothetical publication and vacancy
states separate from the actual deployment configuration.
