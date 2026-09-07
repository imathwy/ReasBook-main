# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Venue:** arXiv:2608.21708v1 (`math.OC`), 2026
- **Paper ID:** `DFP_wolfe_local`
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1)
- **Source development:** [imathwy/DFP_wolfe_local](https://github.com/imathwy/DFP_wolfe_local)
- **Source snapshot:** `e308927f5b7930bdd002f0c0e42b9d112ad821cb`

## Contributor

- Zichen Wang ([@imathwy](https://github.com/imathwy))

## Coverage

This paper formalization develops a uniformly convex, globally Hessian-bounded
counterexample for the classical inverse-form Davidon-Fletcher-Powell (DFP)
method. The public `DFPWolfe` surface covers:

- the planar and all-dimensional counterexamples;
- the standard weak-Wolfe and paper-range strong-Wolfe interfaces;
- the global and level-set formulations of the convergence predicate;
- the two-phase orbit, limiting-circle, separation, and bump-extension
  constructions; and
- the identity-initialized operator and matrix `liminf` certificates.

The development also includes the reusable `ReasLib` analysis, topology,
calculus, and DFP infrastructure needed by these statements. Numerical
experiments and manuscript presentation files are maintained in the source
development repository and are not part of this ReasBook Lean contribution.
The implementation roots remain under this project directory while dedicated
Lake libraries preserve their public `DFPWolfe` and `ReasLib` module names.

## Statistics

The counts below cover the project's tracked Lean source files, including the
`DFPWolfe` and `ReasLib` implementation roots, their aggregate roots, and the
`Paper.lean` wrapper.

- **Lean code:** 824 `.lean` files, 153,166 physical lines, 142,948 nonblank lines
- **Declarations:** 3,694 (theorem/lemma/example: 3,181; other: 513)
- **Declaration breakdown:** 2,996 theorems, 185 lemmas, 408 definitions,
  13 abbreviations, 86 structures, and 6 instances
- **Module split:** 205 `DFPWolfe` files and 616 `ReasLib` files
- **Proof-bearing declarations:** 3,181 / 3,181 theorems and lemmas
- **Remaining placeholders:** `sorry`: 0; `admit`: 0
- **Project-defined axioms:** 0

The declaration count is a reproducible source-level count of declaration
heads; it is not a count of the imported mathlib environment.

## Main declarations

- `DFP.existsStrongWolfeCounterexample_of_parameterRange`
- `DFP.main_not_globalWeakWolfeConvergence_of_parameterRange`
- `DFP.main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange`
- `DFP.not_PaperRangeGlobalWeakWolfeConvergence`
- `DFP.not_PaperRangeLevelSetGlobalWeakWolfeConvergence`
- `DFP.existsMatrixIdentityLiminfStrongWolfe_of_parameterRange`

## Build and verification

From the `ReasBook` directory on branch `v4.32.0`:

```bash
lake env lean Papers/DFP_wolfe_local/Paper.lean
lake build DFP_wolfe_local
```

`Paper.lean` imports the complete public `DFPWolfe` surface. The project uses
the Apache License, Version 2.0, consistent with the source development
repository.
