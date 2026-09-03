# Verso Build SDK

`verso-build-sdk` builds a Verso/Lake site through a small, explicit pipeline.
It contains no platform integration, so the same package can be used locally,
from CI, or as a stage inside an external build service.

The pipeline has two optional stages:

1. run a caller-supplied generator (for example, section/route generation);
2. run `lake` with the requested target arguments.

The toolchain is read from `lean-toolchain` by default and executed through
`elan run --install`. Commands are argv arrays rather than shell strings, and
the runner is injectable for tests or another execution service.

## CLI

```bash
./sdk/verso/bin/verso-build /path/to/ReasBookWeb \
  --generator 'python3.11 scripts/gen_sections.py' \
  --target exe --target reasbook-site \
  --dry-run
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
