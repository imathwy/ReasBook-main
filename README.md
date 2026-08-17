# ReasBook — Lean/mathlib v4.32.0

**Toolchain:** `leanprover/lean4:v4.32.0`
**Mathlib:** v4.32.0
**Status:** Active
**Last build:** pending

This branch aggregates books and papers that use exactly Lean/mathlib
`v4.32.0`. Dependency locks, shared declarations, and namespaces must stay
compatible within the branch.

- Manifest: [`ReasBook/lake-manifest.json`](ReasBook/lake-manifest.json)
- Aggregate entry: [`ReasBook/ReasBook.lean`](ReasBook/ReasBook.lean)

## Books

| Book | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| Computational Methods for Inverse Problems — Curtis R. Vogel (2002) | Yifan Bai, Wanli Ma, Zichen Wang | — | [source](./ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/) | — |

## Papers

| Paper | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| — | — | — | — | — |

## Build

```bash
cd ReasBook
lake update
lake build
```

Full Lean and web builds run on the self-hosted runner. Locally,
`./build.sh` and `./build-web.sh` replicate the same phases when those scripts
are available.
