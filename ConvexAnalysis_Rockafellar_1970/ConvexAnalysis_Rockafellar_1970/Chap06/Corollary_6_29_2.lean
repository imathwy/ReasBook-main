import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_19

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.2 says that for a convex bifunction `F`, once the optimal value
  of the associated generalized convex program is finite, failure of Kuhn--Tucker vectors is
  equivalent to the existence of a direction along which the two-sided directional derivative of
  `inf F` at `0` exists and equals `-∞`.
- `core/canonical`: the existing owners are `perturbationFunction F` for `inf F`,
  `kuhnTuckerVectorSet F` (notation `KT(F)`) for Kuhn--Tucker vectors, and
  `Function.HasBilateralDirectionalDerivativeAt` for the two-sided directional derivative.
- `bridge/view`: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of subgradients of
  `perturbationFunction F` at `0`, while Theorem 23.3 identifies emptiness of the subdifferential
  of a finite convex function with existence of a bilateral directional derivative equal to `⊥`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.optimalValue`;
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`;
- `Function.HasBilateralDirectionalDerivativeAt`;
- `Function.exists_hasBilateralDirectionalDerivativeAt_eq_bot_of_subdifferentialAt_eq_empty`.

Layer target:
- `source-facing`, stated directly on the canonical bifunction and bilateral-directional-derivative
  owners without adding a separate program wrapper or a limit-expression surrogate.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- subgradients of `perturbationFunction F` at `0`, so nonexistence of Kuhn--Tucker vectors is
-- equivalent to emptiness of that subdifferential. The finiteness hypothesis rewrites as
-- finiteness of `perturbationFunction F` at `0`, and Theorem 23.3 then turns empty
-- subdifferential for the convex function `perturbationFunction F` into the existence of a
-- direction with bilateral directional derivative `⊥`.
/-- Corollary 6.29.2: if `F` is a convex bifunction and the optimal value of the associated
generalized convex program is finite, then the canonical Kuhn--Tucker set `KT(F)` is empty if and
only if there exists a direction `u` for which the two-sided directional derivative of
`perturbationFunction F` at `0` exists and equals `-∞`, expressed by the canonical owner
`Function.HasBilateralDirectionalDerivativeAt (perturbationFunction F) 0 u ⊥`. -/
theorem not_exists_isKuhnTuckerVector_iff_exists_hasBilateralDirectionalDerivativeAt_perturbationFunction_zero_eq_bot
    (hF_convex : convᵇ[𝕜](F))
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (¬ (KT(F) : Set UStar).Nonempty) ↔
      ∃ u : U,
        Function.HasBilateralDirectionalDerivativeAt (perturbationFunction F) (0 : U) u ⊥ := sorry

end

end Bifunction
