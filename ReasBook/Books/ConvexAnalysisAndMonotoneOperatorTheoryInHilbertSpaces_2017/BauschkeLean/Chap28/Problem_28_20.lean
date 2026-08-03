import Mathlib.Tactic.Recall
import BauschkeLean.Chap19.Example_19_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Problem 28.20 records the finite-family primal/dual pair
  `x ↦ h(x) - ⟪x, z⟫ + ∑ i, gᵢ(Lᵢ x - rᵢ)` and
  `v ↦ h^*(z - ∑ i Lᵢ^* vᵢ) + ∑ i (gᵢ^*(vᵢ) + ⟪vᵢ, rᵢ⟫)`.
- `core/canonical`: the owner abstractions are Chapter 19's
  `perturbationPrimalObjective` and `perturbationDualObjective`, with the finite family
  `(Lᵢ)` canonically packaged by `ContinuousLinearMap.toLpOperator`.
- `bridge/view`: `Chap19/Example_19_3.lean` already specializes those owners to the exact
  finite-sum formulas above, so this file should stay a pure recall rather than reintroducing a
  parallel local statement.

Primitive data: the source family `(rᵢ)` already lives in the canonical owner `r : lp K 2`, and
the family `(Lᵢ)` is already bridged to the Hilbert-sum ambient space by
`ContinuousLinearMap.toLpOperator`.
Derived API: none; direct downstream use should go through the recalled Chapter 19 theorems. -/
-- Semantic recall: the verified project-local owners are
-- `ERealFunction.perturbationPrimalObjective_linearTilt_shiftedHilbertSum_family_eq_sum` and
-- `ERealFunction.perturbationDualObjective_linearTilt_shiftedHilbertSum_family_eq_sum` from
-- `Chap19/Example_19_3.lean`.

/- Problem 28.20: the source-facing finite-family primal/dual formulas are already formalized in
Chapter 19, so this item is a direct recall. -/
recall ERealFunction.perturbationPrimalObjective_linearTilt_shiftedHilbertSum_family_eq_sum
recall ERealFunction.perturbationDualObjective_linearTilt_shiftedHilbertSum_family_eq_sum
