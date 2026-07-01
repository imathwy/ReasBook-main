# Phase 0 Final Report

Date: 2026-06-29

Decision: **GO**

Phase 0 is complete. The selected read-only corpus and isolated experiment
project are ready for Phase 1 declaration indexing.

## Library and environment

- `OptimizationResearch/` is an independent Lean 4.30.0 Lake project.
- Mathlib and all inherited dependencies use the root shared path cache.
- The final `lake build` passed without warnings or placeholders.
- The local `.lake` is 12 MB after removing interrupted, unused package clones.
- The Python Harness uses a `src/` layout and has 16 passing tests.

## Source isolation

- All four candidate source digests match their pre-audit values.
- Git reports no candidate-source changes.
- Resolved-path policy tests cover direct writes, parent traversal, and symlink escape.
- Bubblewrap mounts the repository read-only and rebinds only
  `OptimizationResearch/` writable.
- An integration probe wrote successfully under `OptimizationResearch/Runs/`;
  a write probe under `Nesterov/` failed with a read-only-filesystem error.
- Network is unshared by default in the guarded command.

## Corpus decision

Selected:

1. `FirstOrderMethodsinOptimization`;
2. `Nesterov`;
3. `SmoothMinimization_Nesterov_2004`.

Deferred:

- `ConvexAnalysis_Rockafellar_1970`, because its broad scope and review cost are
  unnecessary for the first optimization loop.

All four default Lake targets passed. This is explicitly a bounded baseline:
some root modules import only `Basic` or selected aggregates, so later indexing
must not treat default-target success as per-file verification.

## Harness artifacts

- 16 versioned JSON Schema documents;
- machine-readable project state and WP0–WP9 registry;
- example task and complete example run;
- permission, context, and artifact policies;
- five v0 Skills;
- source guard, artifact validation, placeholder scanning, and sandbox controls;
- immutable next actions with evidence and approval status.

All 37 Phase 0 JSON artifacts parsed successfully. Core example records passed
the deterministic record validator.

## Benchmark and research design

- Benchmark v0 defines task types, relation labels, unknown handling, split
  isolation, and version policy.
- Exactly 30 definition-alignment candidates were created.
- Candidate IDs are unique and every cited source file exists.
- H1 is split into C0→C1 retrieval and C1→C2 verifier comparisons, one active
  Harness variable per comparison.
- H2 compares C2 with C3, adding only an isolated mathematical Reviewer.
- The deterministic protocol audit passed all three protocols.
- Negative and invalid runs must be retained.

## Exit criteria

- [x] Isolated Lean project builds with Lean 4.30.0.
- [x] Shared dependency manifest is fixed.
- [x] Source projects remain unchanged.
- [x] Three optimization sources are selected with evidence.
- [x] Corpus manifest and bounded build baseline are frozen.
- [x] Policy, threat model, allow/deny/approval/dry-run decisions, and bypass tests exist.
- [x] Execution-layer read-only isolation is verified.
- [x] Registry, Schema, Skill, Hook, context, and artifact versions exist.
- [x] Example run contains Preflight, Execute, Review, Verify, Measure, and Decide evidence.
- [x] Benchmark rules and 30 candidates exist.
- [x] H1 and H2 are falsifiable, incremental, and audited.
- [x] Build and publication limitations are explicit.
- [x] Stage decision and evidence-backed next actions exist.

## Non-blocking limitations

1. Source-derived benchmark material cannot be published before license review.
2. Gold labels and train/dev/test assignment are Phase 1 inputs, not Phase 0 outputs.
3. The exact model, prompt, numeric budget, and timeout must be frozen before
   formal H1/H2 runs.
4. The H2 net-review-value weighting must be fixed before results are analyzed.

These limitations do not block read-only declaration indexing.

## Phase 1 input

- corpus `optimization-pilot-v0`;
- read-only source list and safe digests;
- build baseline v0;
- schemas, registry, Skills, Hooks, and sandbox command;
- benchmark candidate set v0;
- H1/H2 protocols and audit;
- approved next action `phase1-build-declaration-index`.
