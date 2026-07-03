import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 4.14: if `T : H → H` is firmly nonexpansive, then for every closed linear subspace
`V` the compressed operator `P_V ∘ T ∘ P_V` is firmly nonexpansive. -/
theorem orthogonal_projection_compression_firmly_nonexpansive
    (V : ClosedSubmodule ℝ H) {T : H → H} (hT : FirmlyNonexpansiveOn Set.univ T) :
    FirmlyNonexpansiveOn Set.univ (V.starProjection ∘ T ∘ V.starProjection) := by
  have hV : IsSelfAdjoint V.starProjection := isSelfAdjoint_starProjection (V : Submodule ℝ H)
  have h :=
    adjoint_comp_firmlyNonexpansive_of_norm_le_one T hT V.starProjection
      V.starProjection_norm_le
  simpa [Function.comp, hV.adjoint_eq] using h

end
