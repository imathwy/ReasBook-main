import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_19

noncomputable section

open scoped Rockafellar
open Function

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.1 has three atomic clauses about a convex bifunction `F`: the
  perturbation function `inf F`, together with the Kuhn--Tucker vector characterization for the
  associated generalized convex program. The domain equality is reused below as an unlabeled
  companion recall.
- `core/canonical`: the existing owner layer is already present as
  `Bifunction.perturbationFunction`, `Bifunction.dom`, and `Bifunction.IsKuhnTuckerVector`.
- `bridge/view`: convexity of `inf F` is the partial-infimum theorem applied to `uncurry F`; the
  effective-domain clause is exactly the existing theorem
  `Bifunction.dom_perturbationFunction_eq_dom`; the Kuhn--Tucker characterization is the
  source-facing sign-correct translation of the Chapter 23 subdifferential owner at `u = 0`.

Domain-style sampling used here:
- `IsConvex.partialInfimum` from `Chap01.Text_5_7_2`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.dom_perturbationFunction_eq_dom` from `Definition_6_29_8`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `_root_.subdifferentialAt` / `∂[Y]f(x)` from `Chap05.Definition_23_0_6`.

Layer target:
- clause `(1)` is a thin source-facing theorem on the canonical perturbation-function owner;
- the domain equality is exact-interface reuse of an existing owner theorem, so it is recalled
  directly as an unlabeled companion;
- clause `(2)` is a source-facing bridge from the Kuhn--Tucker owner to the Chapter 23
  subdifferential owner.
-/

section Convexity

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: `perturbationFunction F` is `partialInfimum (uncurry F)`.
-- Apply the canonical partial-infimum convexity theorem to the convex graph function
-- `uncurry F` and rewrite through the owner definition of `perturbationFunction`.
/-- Theorem 6.29.1 (1): if the graph function `uncurry F` is convex, then the
perturbation function `perturbationFunction F` is convex on the perturbation space. -/
theorem perturbationFunction_isConvex
    {F : U → X → WithBotTop 𝕜} (hF : (uncurry F).IsConvex 𝕜) :
    (perturbationFunction F).IsConvex 𝕜 := sorry

end Convexity

section Domain

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

/- Companion recall: the effective domain of the perturbation function is exactly the
source-facing bifunction domain `dom F`, already owned by
`Bifunction.dom_perturbationFunction_eq_dom`. -/
recall dom_perturbationFunction_eq_dom

end Domain

section KuhnTucker

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: if `uStar` is Kuhn--Tucker, rewrite `optimalValue F` as `p 0` and use the
-- defining inequality `optimalValue F ≤ p u + ⟪u, uStar⟫ₚ` to obtain
-- `p u ≥ p 0 + ⟪u, -uStar⟫ₚ`, hence `-uStar ∈ ∂[UStar]p(0)`. Conversely, if
-- `-uStar ∈ ∂[UStar]p(0)`, the subgradient inequality yields
-- `p 0 ≤ p u + ⟪u, uStar⟫ₚ` for every `u`, while equality at `u = 0` forces the defining
-- shifted infimum to equal `p 0 = optimalValue F`; the hypothesis that `optimalValue F` is
-- finite supplies the two-sided finiteness fields of `IsKuhnTuckerVector`.
/-- Theorem 6.29.1 (2): when the optimal value is finite, a dual vector `u⋆` is a Kuhn--Tucker
vector for `F` exactly when `-u⋆` is a subgradient of the perturbation function at `0`. -/
theorem
    isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) (uStar : UStar) :
    IsKuhnTuckerVector F uStar ↔ -uStar ∈ (∂[UStar]p(0)) := sorry

end KuhnTucker

end Bifunction
