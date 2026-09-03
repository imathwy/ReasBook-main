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
Both paths close referenced external HTML links with explicit lightweight
stubs and reject missing non-HTML assets. Output is an atomic,
content-addressed `project-modules-v2` cache; provide `--repository` and
`--revision` together when source links must be pinned to an immutable commit.

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
