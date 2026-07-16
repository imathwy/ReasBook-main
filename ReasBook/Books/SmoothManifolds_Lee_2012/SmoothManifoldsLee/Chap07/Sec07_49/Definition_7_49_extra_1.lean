import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold

universe u𝕜 uE uH uG uE'

-- Semantic recall tool unavailable in this session; verified owners:
-- `LieGroup`, `Manifold.IsImmersion`, and `Manifold.ImmersedSubmanifold`.

section LieSubgroups

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable (I : ModelWithCorners 𝕜 E H) [LieGroup I (⊤ : WithTop ℕ∞) G]

/-- Definition 7.49-extra-1: A Lie subgroup of a Lie group `G` is a subgroup of `G` together with
a topology and smooth structure making it into a Lie group such that the subgroup inclusion into
`G` is a smooth immersion, hence an immersed submanifold of `G`. -/
structure LieSubgroup where
  /-- The underlying subgroup of the ambient Lie group. -/
  carrier : Subgroup G
  /-- The model vector space for the chosen smooth structure on the subgroup. -/
  ModelSpace : Type uE'
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The chosen topology on the subgroup carrier. -/
  instTopologicalSpaceCarrier : TopologicalSpace carrier
  /-- The chosen atlas on the subgroup carrier. -/
  instChartedSpaceCarrier : ChartedSpace ModelSpace carrier
  /-- The chosen smooth structure makes the subgroup carrier into a Lie group. -/
  instLieGroupCarrier :
    LieGroup (modelWithCornersSelf 𝕜 ModelSpace) (⊤ : WithTop ℕ∞) carrier
  /-- The subgroup inclusion into the ambient Lie group is a smooth immersion. -/
  subtype_val_isImmersion :
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) I (⊤ : WithTop ℕ∞)
      (Subtype.val : carrier → G)

attribute [instance] LieSubgroup.instNormedAddCommGroupModelSpace
attribute [instance] LieSubgroup.instNormedSpaceModelSpace
attribute [instance] LieSubgroup.instTopologicalSpaceCarrier
attribute [instance] LieSubgroup.instChartedSpaceCarrier
attribute [instance] LieSubgroup.instLieGroupCarrier

namespace LieSubgroup

variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I (⊤ : WithTop ℕ∞) G]

local notation "LieSubgroupI" => @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I

/-- A Lie subgroup coerces to the type underlying its chosen subgroup carrier. -/
instance : CoeSort LieSubgroupI (Type uG) where
  coe S := S.carrier

/-- The carrier of a Lie subgroup carries its chosen topology. -/
instance (S : LieSubgroupI) : TopologicalSpace S.carrier :=
  S.instTopologicalSpaceCarrier

/-- The carrier of a Lie subgroup carries its chosen atlas. -/
instance (S : LieSubgroupI) : ChartedSpace S.ModelSpace S.carrier :=
  S.instChartedSpaceCarrier

/-- The carrier of a Lie subgroup carries its chosen Lie-group structure. -/
instance (S : LieSubgroupI) :
    LieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) (⊤ : WithTop ℕ∞) S.carrier :=
  S.instLieGroupCarrier

/-- The chosen Lie-group and immersion data determine the corresponding immersed submanifold of the
ambient Lie group. -/
def toImmersedSubmanifold (S : LieSubgroupI) :
    Manifold.ImmersedSubmanifold I G where
  ModelSpace := S.ModelSpace
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := S.carrier
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := (Subtype.val : S.carrier → G)
  inclusion_injective := Subtype.val_injective
  inclusion_isImmersion := S.subtype_val_isImmersion

instance instFiniteDimensionalToImmersedSubmanifoldModelSpace (S : LieSubgroupI)
    [FiniteDimensional 𝕜 S.ModelSpace] :
    FiniteDimensional 𝕜 S.toImmersedSubmanifold.ModelSpace := by
  simpa [toImmersedSubmanifold] using (inferInstance : FiniteDimensional 𝕜 S.ModelSpace)

end LieSubgroup

end LieSubgroups
