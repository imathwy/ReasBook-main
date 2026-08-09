# A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates

- Links: [Repository](https://github.com/optpku/ReasBook) | [Lean source](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | [Paper module](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Paper.lean)
- Contributor: Zichen Wang ([@imathwy](https://github.com/imathwy))
- Lean toolchain: `leanprover/lean4:v4.32.2`; mathlib: `v4.32.2`

- Formalization modules are organized by labeled theorems and supporting proof interfaces.
- Coverage: regularity and parameter assumptions, the NR-LALM iteration model,
  deterministic and stochastic complexity, stopping and restart semantics, the
  SPIDER estimator, finite-length KL convergence, and the optional minimum-norm
  correction comparison.
- Formalization size: 141 Lean files and 75,687 physical source lines
  (71,408 nonblank; the `Paper.lean` presentation wrapper is excluded).
- The project contains 2,853 top-level declarations, with no `sorry`, `admit`, or
  project-defined `axiom` declarations.
- Proof completion: 2,853 / 2,853 declarations; `sorry`: 0; `admit`: 0.
- Primary module names follow the article numbering, including `Lemma_2_6`,
  `Theorem_2_9`, `Theorem_2_13`, `Theorem_3_7`, and `Corollary_3_8`.
- All 24 linked article declarations have been audited for matching assumptions,
  constants, quantifiers, stopping semantics, and complexity accounting. Compound
  article statements are represented by families of focused Lean theorems imported by
  `TR_LALM_theory.Current`.
