# Verso Build SDK

`verso-build-sdk` builds a Verso/Lake site through a small, explicit pipeline.
It contains no platform integration, so the same package can be used locally,
from CI, or as a stage inside an external build service.

The site generator itself is the upstream
[Lean Verso project](https://github.com/leanprover/verso). This package provides
the transport-neutral planning, execution, and cache boundaries around it; it
does not replace or fork the upstream generator.

The generic site pipeline has two optional stages:

1. run a caller-supplied generator (for example, section/route generation);
2. run `lake` with the requested target arguments.

The toolchain is read from `lean-toolchain` by default and executed through
`elan run --install`. Commands are argv arrays rather than shell strings, and
the runner is injectable for tests or another execution service.

Large ReasBook sites also use `verso-literate`, a separate cache capability in
this SDK. It consumes the generator's deterministic module manifest, builds
independent `+Module:literate` targets in bounded parallel batches, validates
the JSON/Lake trace artifacts, and atomically records a source-identity-bound
completion marker. A repeat run performs no Lake command when the exact marker
and artifact hashes still match. Successful batches are committed to a second,
identity-bound progress marker, so a retry schedules only unfinished modules.
Both local and remote callers are serialized by a cache-local lock.

## CLI

```bash
./sdk/verso/bin/verso-build /path/to/ReasBookWeb \
  --generator 'python3.11 scripts/gen_sections.py' \
  --target exe --target reasbook-site \
  --dry-run

./sdk/verso/bin/verso-literate \
  --lean-root /path/to/ReasBook \
  --module-manifest /path/to/ReasBookWeb/.literate-modules.json \
  --jobs 4 --chunk-size 32
```

Install the package in editable mode when using the console entry point:

```bash
python3.11 -m pip install -e sdk/common -e sdk/verso
verso-build /path/to/site --generator 'python3.11 scripts/gen_sections.py'
```

Useful environment settings use the `VERSO_` prefix: `VERSO_TOOLCHAIN`,
`VERSO_LAKE_BIN`, `VERSO_ELAN_BIN`, `VERSO_TARGETS`, `VERSO_GENERATOR`,
`VERSO_OUTPUT_DIR`, and `VERSO_VERIFY_OUTPUT`. `VERSO_ENV_<NAME>` adds an
explicit build environment variable. Credentials and platform-specific values
are intentionally outside this SDK.

`verso-literate` accepts `REASBOOK_BUILD_LAKE_BIN`,
`REASBOOK_LITERATE_JOBS`, `REASBOOK_LITERATE_CHUNK_SIZE`, and
`REASBOOK_LITERATE_BATCH_TIMEOUT_SECONDS`. Release finalizers additionally pin
the cache identity with `REASBOOK_GITHUB_BRANCH`, `REASBOOK_SOURCE_COMMIT`,
`REASBOOK_LAKE_MANIFEST_SHA256`, `VERSO_TOOLCHAIN`, and
`REASBOOK_CACHE_ARCHITECTURE`, plus the finalizer's
`REASBOOK_TOOLING_SHA256`; ordinary local runs derive missing identity fields
from the checked-out Lean project and helper implementation. The helper always
hashes the actual Lean source tree and checks supplied commit, manifest, and
toolchain claims against local files, then rechecks source/module digests
before every progress checkpoint and final completion.
`REASBOOK_LITERATE_ADOPT_EXISTING=1` is
reserved for an orchestrator that has independently locked and verified the
exact immutable cache key; the release orchestrator provides that gate.
It applies only when neither completion nor progress state has ever existed,
so stale or corrupt state can never be relabeled as a new identity.

`--jobs` controls the effective Lean worker pool through `LEAN_NUM_THREADS`.
Large generated JSON files are verified with an iterative mmap-backed grammar
parser, so validation does not build a Python object tree. Mapped pages may
still appear in RSS up to roughly the current artifact size and are validated
only after the Lake subprocess exits.

## Python API

```python
from pathlib import Path
from verso_build_sdk import VersoBuildConfig, VersoBuilder

config = VersoBuildConfig(
    web_root=Path("ReasBookWeb"),
    generator=("python3", "scripts/gen_sections.py"),
    targets=("exe", "reasbook-site"),
)
result = VersoBuilder(config).run(dry_run=True)
```

Use `VersoBuilder(..., runner=...)` to supply a fake or remote command runner.
