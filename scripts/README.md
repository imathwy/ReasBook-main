# Repository Scripts

Reusable execution code lives in [`../sdk`](../sdk/README.md). This directory
contains only adapters that understand this checkout's source or artifact
layout.

| Directory | Responsibility |
| --- | --- |
| [`build/`](build/) | full/core/docs/Verso phases and repository paths |
| [`pages/`](pages/) | cross-version discovery, site assembly, verification, and README maintenance |
| [`config/`](config/) | repository metadata validation |
| [`preview/`](preview/) | local static-site preview server |

`build/project_docs.sh` is a checkout-layout adapter around the Build SDK's
bounded `project-docs` command. The SDK owns target normalization, doc-gen
mode selection, cache identity, locking, and atomic publication; the script
only supplies this repository's paths and immutable source revision.

Normal local entrypoints are:

```bash
./scripts/build/all.sh
./scripts/build/site.sh
./sdk/common/bin/python ./scripts/preview/serve.py 18000
```

For a packaged release, prefer the integrity-checking SDK entrypoint:

```bash
./sdk/deploy/bin/reasbook-deploy release preview RELEASE_ID --artifact pages
```

The preview server expects the generated GitHub Pages root (`/ReasBook/`). If
an authenticated workspace exposes the port below an additional path prefix,
pass the prefix that the proxy strips before forwarding the request:

```bash
REASBOOK_SITE_DIR=/path/to/verified/site \
./sdk/common/bin/python ./scripts/preview/serve.py 3000 \
  --host 0.0.0.0 \
  --site-root /ReasBook/ \
  --public-prefix /workspace/proxy/3000
```

Open the proxy URL printed by the workspace, followed by `/ReasBook/`. The
option rewrites responses in memory; it never modifies the verified release
tree.

Removed wrapper paths map directly to these maintained entrypoints:

| Previous path | Current entrypoint |
| --- | --- |
| `build.sh` | `scripts/build/all.sh` |
| `build-web.sh` | `scripts/build/site.sh` |
| `deploy.sh` | `sdk/deploy/bin/reasbook-deploy docker` |
| `serve.py` | `scripts/preview/serve.py` |
| `tools/theorem_map/*.py` | `sdk/theorem_graph/bin/theorem-graph` |

Selected-book and Docker deployments use the orchestration SDK directly:

```bash
./sdk/deploy/bin/reasbook-deploy --book BOOK_ID --no-build
./sdk/deploy/bin/reasbook-deploy docker --skip-build
```

CI runtime helpers are `reasbook-deploy ci ...` subcommands. Lake target
discovery is `reasbook-build targets ...`; theorem-map generation and catalog
rendering are `theorem-graph` and `theorem-graph catalog`. Do not add wrapper
files for these SDK commands.

The metadata validator has isolated optional dependencies:

```bash
python3.11 -m pip install -r scripts/config/requirements.txt
./scripts/config/validate_book.py ReasBook/Books/BOOK_ID/book.yml
```

## Cache policy

Generated Lean, Mathlib, XDG, documentation, and deployment logs must remain
outside the Git checkout. The deploy SDK and phase scripts default to
`/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/` and reject
cache/data roots inside a checkout. Set `REASBOOK_CACHE_ROOT` for another
volume explicitly.
