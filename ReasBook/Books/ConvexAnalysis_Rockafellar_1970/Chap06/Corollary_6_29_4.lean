import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_21
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

noncomputable section

open Function
open scoped Rockafellar

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.4 concludes, under finite optimal value and strong or strict
  consistency, that the Kuhn--Tucker vector set is nonempty and that the directional derivative of
  the perturbation function at `0` is the negative infimum of the pairing over all Kuhn--Tucker
  vectors. Since strict consistency already implies strong consistency in the chapter owner API,
  the main declarations below are refined to the canonical hypothesis `IsStronglyConsistent 𝕜 F`.
- `core/canonical`: the ambient owner declarations are already present as
  `Bifunction.perturbationFunction`, `Bifunction.kuhnTuckerVectorSet`,
  `Function.directionalDerivativeAt`, and the support function `δᵛ(· | ·)` over `WithBotTop 𝕜`.
- `bridge/view`: the displayed `-sInf` image formula is the pointwise spelling of the support
  function of
  the reflected Kuhn--Tucker set `Neg.neg '' kuhnTuckerVectorSet F`; this reflected support owner
  is the canonical abstraction, while the explicit infimum is derived API via
  `HasPairingNegRight.pairing_neg_right`.

Domain-style sampling used here:
- `Bifunction.isStronglyConsistent_iff_mem_riDom_perturbationFunction` from
  `Definition_6_29_10`;
- `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite` from
  `Theorem_6_29_1`;
- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom` from
  `Chap05.Theorem_23_4`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive source data: the perturbation function `perturbationFunction F` and the canonical set
  `kuhnTuckerVectorSet F`;
- derived API: the reflected support-function identity and the explicit negative-infimum pairing
  formula.

Layer target:
- the nonemptiness statement remains `source-facing`;
- the directional-derivative identity is refined first to the canonical reflected-support owner,
  with the displayed `-sInf` formula retained as a thin `bridge/view` companion.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜]
variable [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: let `p := perturbationFunction F`. Theorem 6.29.1 makes `p` convex and identifies
-- Kuhn--Tucker vectors with negatives of subgradients at `0`. Strong consistency gives
-- `0 ∈ riDom[𝕜](p)` directly; strict consistency is already absorbed by the upstream implication
-- `IsStrictlyConsistent.isStronglyConsistent`. Since `p 0 = optimalValue F` is finite, Theorem
-- 7.2 forces `p` to be proper; then Theorem 23.4 gives a nonempty subdifferential at `0`, and
-- Theorem 6.29.1 transports that witness back to a Kuhn--Tucker vector.
/-- The Kuhn--Tucker set is nonempty when the optimal value is finite and the program is strongly
consistent. Strict consistency is a sufficient special case via
`IsStrictlyConsistent.isStronglyConsistent`. -/
theorem kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    (kuhnTuckerVectorSet F : Set UStar).Nonempty := sorry

-- Proof sketch: first obtain the nonempty subdifferential of `p` at `0` from Theorem 23.4 and
-- rewrite the owner equality `directionalDerivativeAt p 0 = δᵛ(· | ∂[UStar]p(0))`. Then use
-- Theorem 6.29.1 to identify `∂[UStar]p(0)` with the reflected Kuhn--Tucker set
-- `Neg.neg '' kuhnTuckerVectorSet F`.
/-- Corollary 6.29.4, owner form: if the optimal value of the convex program attached to `F` is
finite and the program is strongly consistent, then the directional derivative of the perturbation
function `inf F` at `0` is the support function of the reflected Kuhn--Tucker vector set. Strict
consistency is a sufficient special case via `IsStrictlyConsistent.isStronglyConsistent`. -/
theorem
    directionalDerivativeAt_perturbationFunction_zero_eq_supportFunction_reflected_kuhnTucker
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    directionalDerivativeAt p (0 : U) =
      (fun u : U ↦
        δᵛ[WithBotTop 𝕜](u | Neg.neg '' (kuhnTuckerVectorSet F : Set UStar))) := sorry

-- Proof sketch: apply the owner theorem above and expand the support function of the reflected set
-- `Neg.neg '' kuhnTuckerVectorSet F`. Reindex that supremum by
-- `u⋆ ∈ kuhnTuckerVectorSet F` and use
-- `⟪u, -uStar⟫ₚ = -⟪u, uStar⟫ₚ` to rewrite the resulting supremum as the displayed negative
-- infimum.
/-- Corollary 6.29.4: if the optimal value of the convex program attached to `F` is finite and
the program is strongly consistent, then the directional derivative of the perturbation function
`inf F` at `0` is the negative infimum of the pairing over all Kuhn--Tucker vectors. Strict
consistency is a sufficient special case via `IsStrictlyConsistent.isStronglyConsistent`. -/
theorem
    directionalDerivativeAt_perturbationFunction_zero_eq_neg_sInf_image_pairing_kuhnTuckerVectorSet
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F)
    (u : U) :
    directionalDerivativeAt p (0 : U) u =
      -sInf ((fun uStar : UStar ↦ (⟪u, uStar⟫ₚ : WithBotTop 𝕜)) ''
        (kuhnTuckerVectorSet F : Set UStar)) := sorry

end

end Bifunction
