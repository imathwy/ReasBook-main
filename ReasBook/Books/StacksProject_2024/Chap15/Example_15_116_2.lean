import Mathlib
import StacksProject_2024.Chap10.Definition_10_119_8
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_115_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open IsLocalRing PowerSeries
open scoped UniformizerRoot

/-
Domain-style sampling for Example `15.116.2`.

- primary domain: finite base change of extensions of discrete valuation rings, specialized to the
  canonical radical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `uniformizerRootExtensionRing`,
  `uniformizerRootExtensionField`;
- best owner abstraction: the source-facing example should reuse the chapter owners
  `IsWeakSolutionFor` / `IsSolutionFor` from `Definition_15_116_1` and the radical-extension owner
  API from `Lemma_15_115_2`, rather than rebuilding parallel local algebra/module wrappers;
- primitive-vs-derived split: the primitive data here are the power-series DVR `A = k[[x]]`, the
  canonical radical extension ring/field `A[π^(1/p)]` and `K[π^(1/p)]`, and the base-change field
  `K₁`; field, module, finite-dimensionality, DVR, fraction-field, and extension-of-DVR structure
  on `A[π^(1/p)]` and `K[π^(1/p)]` are derived API from the upstream owners.

Source/core/bridge triage:
- `source-facing`: the two example theorems about weak solutions and solutions for
  `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `uniformizerRootExtensionRing`,
  `uniformizerRootExtensionField`;
- `bridge/view`: the owner-provided radical-extension tower, fraction-field, and
  `IsExtensionOfDiscreteValuationRings` bridges, specialized here to `π = X`.
-/

section

variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]

local notation "A" => PowerSeries k
local notation "K" => FractionRing A
local notation "π" => (X : A)

private lemma hp : 2 ≤ p :=
  Nat.Prime.two_le (Fact.out : Nat.Prime p)

omit [PerfectField k] in
private lemma hπ : Irreducible π :=
  (maximalIdeal_eq_span_singleton_iff_irreducible π).mp PowerSeries.maximalIdeal_eq_span_X

section BaseChange

variable (K₁ : Type v) [Field K₁] [Algebra (PowerSeries k) K₁]
variable [Algebra (FractionRing (PowerSeries k)) K₁]
variable [IsScalarTower (PowerSeries k) (FractionRing (PowerSeries k)) K₁]
variable [FiniteDimensional (FractionRing (PowerSeries k)) K₁]

local notation "B" => uniformizerRootExtensionRing π p
local notation "L" => uniformizerRootExtensionField π p

local instance : Fact (Irreducible π) := ⟨hπ k⟩

local instance : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : Nat.Prime p)⟩

local instance : Field L :=
  uniformizerRootExtensionField_field (hπ k)

local instance : Algebra K L :=
  uniformizerRootExtensionField_algebra

local instance : Algebra A L :=
  uniformizerRootExtensionField_baseAlgebra

local instance : IsScalarTower A K L :=
  uniformizerRootExtensionField_isScalarTower

local instance : FiniteDimensional (FractionRing A) (uniformizerRootExtensionField π p) :=
  uniformizerRootExtensionField_finiteDimensional
    (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

local instance : IsDomain B :=
  uniformizerRootExtensionRing_isDomain

local instance : IsDiscreteValuationRing B :=
  uniformizerRootExtensionRing_isDiscreteValuationRing

local instance : Algebra B L :=
  uniformizerRootExtensionRingToField_algebra

local instance : IsScalarTower A B L :=
  uniformizerRootExtensionRingToField_isScalarTower

local instance : IsIntegralClosure B A L :=
  uniformizerRootExtensionRing_isIntegralClosure (hπ k) (hp p)

local instance : IsFractionRing B L :=
  uniformizerRootExtensionRing_isFractionRing

local instance : IsExtensionOfDiscreteValuationRings A B :=
  uniformizerRootExtensionRing_isExtensionOfDiscreteValuationRings
    (hπ k) (hp p)

-- Proof sketch: if `K₁ / k((x))` were separable, then the canonical radical extension
-- `k[[x]] ⊂ k[[x]][x^{1/p}]` would remain outside the weak-solution range from
-- Definition `15.116.1`: after base change, every local branch still has ramification index
-- divisible by `p`, so no weak solution exists.
/-- Example 15.116.2 (1): for a perfect field `k` of characteristic `p > 0`, any weak solution for
the canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]` is inseparable over `k((x))`. -/
theorem not_isSeparable_of_weakSolutionForPowerSeriesPthRoot
    (hWeak : IsWeakSolutionFor A A[π^(1/p)] K K[π^(1/p)] K₁) :
    ¬ Algebra.IsSeparable K K₁ := sorry

-- Proof sketch: for a finite inseparable extension `K₁ / k((x))`, the canonical pth-root
-- extension `k[[x]] ⊂ k[[x]][x^{1/p}]` becomes a solution in the sense of
-- Definition `15.116.1`: the inseparability forces the local branches after base change to be
-- formally smooth over the localized normalization.
/-- Example 15.116.2 (2): every finite inseparable extension of `k((x))` is a solution for the
canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`. -/
theorem isSolutionForPowerSeriesPthRoot_of_not_isSeparable
    (hK₁ : ¬ Algebra.IsSeparable K K₁) :
    IsSolutionFor A A[π^(1/p)] K K[π^(1/p)] K₁ := sorry

end BaseChange
end
