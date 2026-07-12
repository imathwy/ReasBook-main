import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Definition_8_60_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Notation_8_60_extra_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Bundle
open VectorField

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section

variable [LieGroup I (minSmoothness 𝕜 3) G]

-- Source/core/bridge split for this corollary:
-- * source-facing owner: `VectorField.IsLeftInvariant`
-- * core owner: `mulInvariantVectorField`
-- * notation surface: `vᴸ`

/-- A left-invariant rough vector field is the invariant vector field determined by its value at
the identity. -/
theorem left_invariant_rough_vector_field_eq_mulInvariantVectorField
    (X : Π g : G, TangentSpace I g)
    (hX : VectorField.IsLeftInvariant X) :
    X = (X 1)ᴸ := by
  ext g
  have hmul : (X 1)ᴸ g = mpullback I I (g⁻¹ * ·) X g := by
    simpa using mulInvariantVectorField_eq_mpullback g X
  rw [hmul]
  exact (congrFun (hX g⁻¹) g).symm

end

section

variable [LieGroup I ∞ G]

/-- Corollary 8.38: Every left-invariant rough vector field on a Lie group is smooth. -/
theorem left_invariant_rough_vector_field_smooth
    [IsRCLikeNormedField 𝕜]
    (X : Π g : G, TangentSpace I g)
    (hX : VectorField.IsLeftInvariant X) :
    ContMDiff I I.tangent ∞ (T% X) := sorry

end
