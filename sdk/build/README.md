# ReasBook Build SDK

`reasbook-build-sdk` provides a small, platform-independent API for planning
and running Lean Lake builds. It is intentionally split into layers so the
same plan can be executed locally, in a container, or by an external job
runner:

```text
project.py   discover and validate a Lake project
lake.py      turn project + options into immutable commands
command.py   command/result value objects and runner contract
executor.py  local subprocess runner and callable adapter
service.py   plan/execute orchestration and output verification
docs.py      bounded reachable project-module docs and dependency-link closure
cli.py       human and JSON command-line interface
targets.py   ReasBook aggregate/per-project target discovery
```

The package depends only on the sibling `reasbook-sdk-common` package and
Python 3.11+. Deployment, authentication, scheduling, and transport concerns
stay outside this package.

## Quick start

From this directory, without installing anything:

```bash
./bin/reasbook-build plan /path/to/project
./bin/reasbook-build build /path/to/project --target ReasBook:docs
./bin/reasbook-build cache /path/to/project
./bin/reasbook-build targets /path/to/project --mode project-docs
./bin/reasbook-build project-docs /path/to/project Books.Example.Book \
  --output /path/to/cache/docs/example
```

The project must contain `lakefile.lean` or `lakefile.toml` and a non-empty
`lean-toolchain`. A build runs `lake exe cache get` followed by `lake build` by
default. Use `--skip-cache-get` when a caller has already prepared the cache,
and `--no-verify-outputs` for a project whose build does not produce `.olean`
files. Extra Lake flags are explicit and are inserted before the subcommand;
documentation builds can use `--lake-arg=-R --lake-arg=-Kenv=dev`.

Release-oriented documentation should use `project-docs`. Starting from each
explicit entry root, it follows imports through project-owned Lean sources and
processes the reachable modules in batches of at most 128. Mathlib, Lean, and
other external libraries are excluded. Modern doc-gen writes and renders a
trimmed database; older doc-gen versions use a compatible bounded renderer.
The legacy renderer discovers the built native-library layouts of UnicodeBasic
and MD4Lean and loads providers before consumers: the UnicodeBasic aggregate,
the MD4Lean C provider, then the MD4Lean aggregate. The resolver accepts
the explicit v4.26 and v4.30 naming schemes without branching on version
strings, and rejects missing, ambiguous, empty, or symlinked libraries. Both paths
close referenced external HTML links with explicit lightweight
stubs and reject missing non-HTML assets. Local `.lean` links embedded in
project docstrings are rewritten only when they resolve uniquely to a source
in the selected reachable closure. The target is then pinned to
`<repository>/blob/<40-character-commit>/ReasBook/...`; an unknown or ambiguous
source path remains a hard error. This prevents absolute paths captured by an
older checkout from leaking into the static site without treating arbitrary
missing assets as source links. Local `file:` URLs, Windows drive paths,
protocol-relative URLs, unsafe path encodings, and unexpected schemes also fail
closed. The builder requires the generated stylesheet and rechecks closure in
no-write mode after creating dependency stubs. It rejects a symlink at the
output path or any existing parent component before resolving the destination.

Output is a content-addressed `project-modules-v2` cache; provide
`--repository` and `--revision` together when source links must be pinned to an
immutable commit. A cache produced before the source-link policy was recorded
is upgraded only through a validated copy and a same-filesystem writer
transaction under its lock. Individual renames are atomic and rollback keeps
the prior cache on failure; this is not a lock-free multi-rename snapshot for
concurrent readers. Modern doc-gen analysis is also checkpointed separately
under the output parent's hidden
`.project-docs-analysis-v1/` directory. Its identity binds the toolchain,
commit, Lake manifest, reachable source hashes and compiled `.olean` files,
project native libraries, doc-gen/leansqlite support, doc-gen executable, and
adapter. Its SQLite database is accepted only after digest, integrity, exact
module-set, required-table, `schema_meta`, and schema-fingerprint checks.
Restoring an incompatible checkpoint permits one fresh-analysis fallback; the
old checkpoint is replaced only after fresh rendering and link closure succeed.
Rendering or link-closure failure therefore cannot publish a partial
documentation cache. The checkpoint directory is derived cache only: it is
never served or copied into a release and may be removed to force a fresh
analysis.

Managed branch caches are an explicit immutable trust boundary. A metadata file
in a normal `.lake` directory is ignored for this purpose; `.lake` must be an
explicit symlink to an exact `lake/branch-...` namespace. Its directory key and
exact metadata fields must agree with the branch, commit, manifest, checked-out
toolchain, and current host architecture. The exact schema-1 field set plus the
`branch-` namespace establishes branch-build purpose and excludes web-cache
metadata. Those values and the metadata digest stand in for rehashing the full
dependency tree on every lookup. Never edit such a cache in place; publish a
replacement cache as a unit. The selected project artifacts and analyzer
support binaries are still hashed from their bytes. Without a valid structural
opt-in, the builder hashes all dependency `.olean`, `.so`, and `.a` files
instead.
The repository adapter `scripts/build/project_docs.sh` uses exactly
`REASBOOK_LAKE_TARGETS` when a release/deployment supplies it, ahead of any
ambient `PROJECT_DOC_MODULES` operator override. Automatic Lake library
discovery is only used when neither selection variable is present; an explicit
but empty release selection is rejected instead of expanding to every
registered project.

For automation, use the typed API:

```python
from reasbook_build_sdk import BuildOptions, BuildService

options = BuildOptions.from_values(
    targets=("ReasBook:docs",),
    verify_outputs=False,
)
result = BuildService().run("/path/to/project", options)
if not result.succeeded:
    raise RuntimeError(result.summary())
```

Every build is represented by a `BuildPlan`. A custom executor can consume the
plan without changing the planner:

```python
from reasbook_build_sdk import BuildResult, BuildService

class QueueExecutor:
    def execute(self, plan):
        # Serialize plan.commands for the execution environment and return a
        # BuildResult with the command snapshots.
        ...

service = BuildService(executor=QueueExecutor())
```

Install the shared primitives before the capability package:

```bash
python3.11 -m pip install -e sdk/common -e sdk/build
```

`Command.argv` is always an argument vector. `shell_preview(plan)` is provided
only for display; an executor should use the vector and the explicit working
directory instead of parsing a shell string.

## Configuration

CLI flags take precedence over these optional variables:

| Variable | Meaning | Default |
| --- | --- | --- |
| `REASBOOK_BUILD_LAKE_BIN` | Lake executable | `lake` |
| `REASBOOK_BUILD_CACHE_GET` | Run cache preflight (`true`/`false`) | `true` |
| `REASBOOK_BUILD_CACHE_TIMEOUT` | Cache command timeout in seconds | `1800` |
| `REASBOOK_BUILD_TIMEOUT` | Build command timeout in seconds | unset |
| `REASBOOK_BUILD_TARGETS` | Comma/newline-separated targets | default target |
| `REASBOOK_BUILD_LAKE_ARGS` | Comma/newline-separated flags before `build` | unset |
| `REASBOOK_BUILD_ENV` | Comma/newline-separated `KEY=VALUE` overrides | unset |
| `REASBOOK_BUILD_VERIFY_OUTPUTS` | Require an expected artifact | `true` |
| `REASBOOK_BUILD_ARTIFACT_EXTENSIONS` | Comma-separated extensions | `.olean` |

`--json` emits a stable, credential-free plan or result suitable for a
controller. Environment values are intentionally omitted from JSON output.

## Tests

```bash
python3.11 -m unittest discover -s tests -v
```
