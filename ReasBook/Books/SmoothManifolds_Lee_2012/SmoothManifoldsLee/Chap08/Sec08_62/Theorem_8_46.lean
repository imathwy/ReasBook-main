import Mathlib.Algebra.Lie.Subalgebra
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_61.Definition_8_61_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff ContMDiffMonoidMorphism

-- Domain sampling pass:
-- * source-facing owner: `LieSubgroup I`;
-- * core/canonical owner: `GroupLieAlgebra`;
-- * bridge/view: `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`.
-- The statements below therefore refine Theorem 8.46 around the existing Lie-subgroup owner
-- instead of restating subgroup, topology, chart, Lie-group, and immersion data separately.

universe u𝕜 uE uH uG

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ∞ G]

namespace LieSubgroup

variable (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]

local instance : LieGroup I (minSmoothness 𝕜 3) G := LieGroup.of_le le_top

local instance : LieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) (minSmoothness 𝕜 3) S.carrier :=
  LieGroup.of_le le_top

/-- A Lie subgroup inclusion is a smooth map. -/
theorem contMDiff_subtype_val :
    ContMDiff (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞ (Subtype.val : S.carrier → G) := sorry

/-- The subgroup inclusion, viewed as a smooth group homomorphism into the ambient Lie group. -/
def inclusion :
    ContMDiffMonoidMorphism (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞ S.carrier G where
  toMonoidHom := S.carrier.subtype
  contMDiff_toFun := contMDiff_subtype_val S

/-- The induced Lie algebra homomorphism of the subgroup inclusion is injective. -/
theorem inclusion_inducedLieAlgebraHomomorphism_injective :
    Function.Injective ((inclusion S)_*) := sorry

/-- Theorem 8.46 (The Lie Algebra of a Lie Subgroup): the Lie algebra of a Lie subgroup is
canonically realized as the Lie subalgebra of `GroupLieAlgebra I G` given by the image of the
derivative at the identity of the subgroup inclusion. -/
def groupLieSubalgebra : LieSubalgebra 𝕜 (GroupLieAlgebra I G) :=
  LieHom.range ((inclusion S)_*)

/-- The inclusion of a Lie subgroup identifies its group Lie algebra with the ambient Lie
subalgebra defined above. -/
noncomputable def groupLieSubalgebraEquiv :
    GroupLieAlgebra (modelWithCornersSelf 𝕜 S.ModelSpace) S.carrier ≃ₗ⁅𝕜⁆
      groupLieSubalgebra S :=
  LieEquiv.ofInjective
    ((inclusion S)_*) (inclusion_inducedLieAlgebraHomomorphism_injective S)

/-- The Lie subalgebra attached to a Lie subgroup is the image of the derivative at the identity
of the inclusion map. -/
theorem groupLieSubalgebra_eq_range :
    groupLieSubalgebra S = LieHom.range ((inclusion S)_*) := rfl

/-- Membership in the Lie algebra of a Lie subgroup means belonging to the image of the tangent
map of the inclusion at the identity. Since `GroupLieAlgebra I G = TₑG`, this is the Lean form of
the textbook condition `Xₑ ∈ TₑH`. -/
theorem mem_groupLieSubalgebra_iff (X : GroupLieAlgebra I G) :
    X ∈ groupLieSubalgebra S ↔
      ∃ Y : GroupLieAlgebra (modelWithCornersSelf 𝕜 S.ModelSpace) S.carrier,
        ((inclusion S)_*) Y = X := by
  rfl

end LieSubgroup

end
