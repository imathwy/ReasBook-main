import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.1 takes a convex bifunction `F`, assumes that the optimal value
  of the associated generalized convex program is finite, and draws six source-facing
  consequences: existence of the directional derivative of `inf F` at `0`, convexity and positive
  homogeneity of that derivative profile, closedness and convexity of the Kuhn--Tucker vector set
  in the canonical dual, and the support-function / lower-semicontinuous-hull identification for
  that dual-side set.
- `core/canonical`: the relevant owners are already present as `perturbationFunction F`,
  `optimalValue F`, `kuhnTuckerVectorSet F`, the dual-valued subdifferential owner
  `∂[StrongDual ℝ U] (perturbationFunction F) (0)`, `HasDirectionalDerivativeAt`,
  `directionalDerivativeAt`, `δᵛ(· | ·)`, and `cl(·)`.
- `bridge/view`: the source phrase `(inf F)(0; u)` is rendered by the canonical owner
  `directionalDerivativeAt (perturbationFunction F) 0 u`; the Kuhn--Tucker vectors are surfaced
  through the existing owner `kuhnTuckerVectorSet F` rather than by repeating a raw set literal,
  and the Fréchet-Riesz self-dual specialization is deliberately not taken as the main public
  layer here.

Domain-style sampling used here:

- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.kuhnTuckerVectorSet` from `Definition_6_29_19`;
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`
  from `Theorem_6_29_1`;
- `HasDirectionalDerivativeAt`, `isConvex_directionalDerivativeAt_of_finite_point`, and
  `positivelyHomogeneous_directionalDerivativeAt_of_finite_point` from `Chap05.Theorem_23_1`;
- `_root_.subdifferentialAt_isClosed` and `_root_.subdifferentialAt_convex` from
  `Chap05.Definition_23_0_6`;
- `δᵛ(· | ·)` and `cl(·)` from Chapters 1 and 2.
-/

section DirectionalDerivative

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: use `perturbationFunction_isConvex` to show that `perturbationFunction F` is
-- convex, read the finiteness hypothesis as finiteness of `perturbationFunction F` at `0`, and
-- then apply `hasDirectionalDerivativeAt_sInf_directionalDifferenceQuotientAt` at the base
-- point `0`.
/-- Corollary 6.29.1 (1): if the optimal value of the generalized convex program attached to a
convex bifunction `F` is finite, then the one-sided directional derivative of
`perturbationFunction F` at `0` exists in every direction. -/
theorem hasDirectionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (u : U) :
    HasDirectionalDerivativeAt p (0 : U) u (directionalDerivativeAt p (0 : U) u) := sorry

-- Proof sketch: first obtain convexity of `perturbationFunction F` from
-- `perturbationFunction_isConvex`; then apply `isConvex_directionalDerivativeAt_of_finite_point`
-- at `0`, using finiteness of `optimalValue F = perturbationFunction F 0`.
/-- Corollary 6.29.1 (2): when the optimal value is finite, the directional-derivative profile
`u ↦ directionalDerivativeAt (perturbationFunction F) 0 u` is convex. -/
theorem isConvex_directionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (directionalDerivativeAt p (0 : U)).IsConvex 𝕜 := sorry

-- Proof sketch: the same convexity and finiteness input at `0` lets
-- `positivelyHomogeneous_directionalDerivativeAt_of_finite_point` apply to
-- `perturbationFunction F`.
/-- Corollary 6.29.1 (3): when the optimal value is finite, the directional-derivative
profile `u ↦ directionalDerivativeAt (perturbationFunction F) 0 u` is positively homogeneous. -/
theorem
    positivelyHomogeneous_directionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (directionalDerivativeAt p (0 : U)).PositivelyHomogeneous 𝕜 := sorry

end DirectionalDerivative

section KuhnTuckerClosedConvex

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set UStar)

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- dual-valued subdifferential of `perturbationFunction F` at `0`; closedness of that canonical
-- subdifferential then transfers to the reflected set.
/-- Corollary 6.29.1 (4): under finiteness of the optimal value, the Kuhn--Tucker vectors of `F`
form a closed subset of the paired dual perturbation space. -/
theorem isClosed_kuhnTuckerVectorSet_of_optimalValue_finite
    [TopologicalSpace UStar]
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    IsClosed (KT(F)) := sorry

-- Proof sketch: use the same subdifferential characterization of Kuhn--Tucker vectors and
-- transfer convexity from `_root_.subdifferentialAt (perturbationFunction F) 0` through negation
-- on the canonical dual.
/-- Corollary 6.29.1 (5): under finiteness of the optimal value, the Kuhn--Tucker vectors of `F`
form a convex subset of the paired dual perturbation space. -/
theorem convex_kuhnTuckerVectorSet_of_optimalValue_finite
    [AddCommMonoid UStar] [Module 𝕜 UStar]
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    Convex 𝕜 (KT(F)) := sorry

end KuhnTuckerClosedConvex

section KuhnTuckerSupportIdentity

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set UStar)
local notation "p" => perturbationFunction F

-- Proof sketch: identify the Kuhn--Tucker set with the negated subdifferential at `0`, rewrite
-- the support function of that reflected set in terms of the support function of the
-- subdifferential, and then use the Chapter 23 directional-derivative/support-function bridge at
-- the finite point `0` to express that support function as the lower-semicontinuous hull of the
-- reflected directional-derivative profile.
/-- Corollary 6.29.1 (6): under finiteness of the optimal value, the support function of the
dual-side Kuhn--Tucker vector set equals the lower-semicontinuous hull of the reflected
directional derivative `u ↦ directionalDerivativeAt (perturbationFunction F) 0 (-u)`. -/
theorem
    supportFunction_kuhnTuckerVectorSet_eq_cl_reflectedDirectionalDerivative_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (δᵛ(· | KT(F)) : U → WithBotTop 𝕜) =
      cl(fun u ↦ directionalDerivativeAt p 0 (-u)) := sorry

end KuhnTuckerSupportIdentity

end Bifunction
