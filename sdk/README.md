# ReasBook SDKs

The SDKs are maintained as small, independently testable capability packages.
They share only the platform-neutral primitives in `common`:

```text
common         argv commands, process results, paths, atomic files
build          Lake project planning and build execution
verso          generator + Verso/Lake site pipeline
theorem_graph  declaration extraction, dependency analysis, rendering
comparator     local Challenge/Solution comparison
deploy         selected-book/site deployment orchestration and CI adapters
```

The dependency direction is one-way:

```text
common -> build
common -> verso
common -> theorem_graph
common -> comparator
build -> deploy
verso -> deploy
theorem_graph -> deploy
comparator -> deploy
```

Every capability follows the same flow:

```text
validated inputs -> immutable plan -> injected executor -> typed result
```

Planning modules do not start processes or write published output. Execution
and publication are isolated behind runners/generators, which keeps dry-runs,
unit tests, and future worker integrations on the same code path.
The SDKs never rewrite Lean source files; generated artifacts are directed to
the caller's build or site output directory.

Each capability exposes a typed Python API, an executable module, a console
entry point, a README, and offline tests. Commands are argument vectors and
executors are injectable, so a caller can provide its own container, queue, or
job runner without changing planning code.

## Install

For an editable checkout, install the capability packages together:

```bash
python3.11 -m pip install -e sdk/common
python3.11 -m pip install -e sdk/build -e sdk/verso \
  -e sdk/theorem_graph -e sdk/comparator -e sdk/deploy
```

`deploy` is the total orchestration layer and therefore declares all four
capability SDKs plus `common` as runtime dependencies. When installing wheels
on another machine, put the sibling SDK wheels in the same wheel directory and
install `reasbook-deploy-sdk` with that directory supplied via `--find-links`;
pip must also be able to resolve the declared PyYAML dependency.

The capability packages have no third-party runtime dependencies beyond the
sibling common package. `deploy` composes those packages and uses PyYAML for
strict human-maintained release profiles. Their CLIs support JSON/dry-run
output where a controller needs a stable machine-readable plan.

## Test

Run all SDK tests from the repository root:

```bash
./sdk/test.sh
```

The theorem graph SDK owns its extractor and frontend resources. CI helpers,
selected-book orchestration, and Docker publication are deploy SDK commands,
without intermediary wrapper scripts. The grouped adapters under `scripts/`
retain only repository-specific source and artifact layout policy.
