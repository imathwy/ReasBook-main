# Corpus Audit and Build Baseline

## Selection

Selected:

1. `FirstOrderMethodsinOptimization`;
2. `Nesterov`;
3. `SmoothMinimization_Nesterov_2004`.

Deferred:

- `ConvexAnalysis_Rockafellar_1970`.

The selected projects overlap directly on smoothness, strong convexity,
gradient/subgradient constructions, first-order methods, and convergence
bounds. The deferred project is highly relevant but much broader and has a
higher first-round review cost.

## Build evidence

All four candidates passed their current default `lake build` target with Lean
4.30.0. Before/after safe source digests were identical.

Default-target success is a bounded result: several root modules import only a
`Basic` or aggregate module, so it does not establish that every standalone
Lean file is compiled. Later task manifests must distinguish project build from
per-file verification.

## Publication boundary

No project-local license file was found in the candidate roots during the
bounded audit. Internal read-only research can proceed, but public release of
source-derived benchmark content requires separate license review.

