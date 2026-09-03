# ReasBook SDK Common

This package contains the small primitives shared by the ReasBook capability
SDKs:

- immutable argv-based commands and structured process results;
- an injectable subprocess runner with timeout handling and process-group cleanup;
- path validation and atomic text/JSON publication.
- a shared Python 3.11+ launcher for capability wrappers.

The package has no domain or deployment policy. Install it before one or more
capability packages:

```bash
python3.11 -m pip install -e sdk/common
```

Use `CommandRunner(output_file=Path("run.log"))` when a long-running adapter
needs bounded memory and a persistent log. Commands are still passed as argv
vectors; no shell string is evaluated by the runner.
