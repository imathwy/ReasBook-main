import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_16_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_31_4_2

open scoped BigOperators PolarCone Rockafellar

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]
variable {f : ι → 𝕜 → WithBotTop 𝕜}
variable {L : Submodule 𝕜 (ι → 𝕜)}
local notation "IsClosedProperConvex[𝕜]" => @Function.IsClosedProperConvex 𝕜
local notation "separableObjective" =>
  (separableCoordinateSum f : (ι → 𝕜) → WithBotTop 𝕜)
local notation "separableDualObjective" =>
  ((separableObjective)⋆ : (ι → 𝕜) → WithBotTop 𝕜)
local notation "Ldual" => (Lᗮₚ : Submodule 𝕜 (ι → 𝕜))

/- Domain-style sampling:
- `separableCoordinateSum` and
  `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate` from `Text_16_0_4`;
- `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification` and
  `optimalValue_pair_iff_mem_subdifferential_on_subspace` from `Corollary_31_4_2`;
- the pairing-level subspace-duality surfaces `Lᗮₚ` and
  `∂[(ι → 𝕜)]` from the existing owner layer.

Layer target: `bridge/view`.
-/

/-- The subspace-duality value formula for a separable closed proper convex objective, written in
the source coordinatewise form `x ↦ ∑ i, fᵢ(xᵢ)`, with dual value owned intrinsically by
`(separableObjective)⋆`. -/
theorem iInf_on_subspace_eq_neg_iInf_on_orthogonal_of_separable_qualification
    (hf : IsClosedProperConvex[𝕜] separableObjective)
    (hqual :
      ((L : Set (ι → 𝕜)) ∩ riDom[𝕜](separableObjective)).Nonempty ∨
        ((Ldual : Set (ι → 𝕜)) ∩ riDom[𝕜](separableDualObjective)).Nonempty) :
    (⨅ x : L, separableObjective x) =
      -(⨅ xStar : Ldual, separableDualObjective xStar) := by
  exact iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification
      (𝕜 := 𝕜) (E := (ι → 𝕜)) (EStar := (ι → 𝕜))
      (f := separableObjective) (L := L) hf hqual

/-- The Kuhn--Tucker criterion for the separable subspace problem. Primal and dual optimality are
equivalent to primal feasibility, dual feasibility, and intrinsic subdifferential membership of the
separable objective. -/
theorem optimalValue_pair_iff_mem_subdifferential_on_subspace_for_separableObjective
    (hf : IsClosedProperConvex[𝕜] separableObjective)
    (x xStar : ι → 𝕜) :
    IsMinOn separableObjective (L : Set (ι → 𝕜)) x ∧
      IsMinOn separableDualObjective (Ldual : Set (ι → 𝕜)) xStar ∧
      separableObjective x = -separableDualObjective xStar ↔
        x ∈ L ∧
          xStar ∈ Ldual ∧
            xStar ∈ ∂[(ι → 𝕜)]separableObjective(x) := by
  exact optimalValue_pair_iff_mem_subdifferential_on_subspace
      (𝕜 := 𝕜) (E := (ι → 𝕜)) (EStar := (ι → 𝕜))
      (f := separableObjective) (L := L) hf x xStar

/- Lemma 31.4.5, clause (1): the coordinatewise conjugacy statement is already the canonical owner
theorem `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate`. -/
#check convexConjugate_separableCoordinateSum_eq_sum_convexConjugate

end
