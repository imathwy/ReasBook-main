import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.UnitInterval

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: the current environment exposes cylinder objects for
-- abstract model categories, while the textbook topological mapping cylinder here is naturally
-- modeled by the pushout API in `TopCat`.

namespace ContinuousMap

/-- The time-`0` inclusion `A ⟶ A × I` used in the mapping cylinder construction. -/
def mappingCylinderTimeZeroInclusion (A : Type u) [TopologicalSpace A] : C(A, A × I) :=
  (ContinuousMap.id A).prodMk (ContinuousMap.const A (0 : I))

/-- Definition 6.2.1. For a map `i : A → X`, the mapping cylinder `M_i` is the pushout
`X ∪_i (A × I)` of `i` and the time-`0` inclusion `A ⟶ A × I`. -/
def mappingCylinder (i : C(A, X)) : TopCat :=
  pushout (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A))

/-- The canonical inclusion `X ⟶ M_i` of the target into the mapping cylinder of `i : A ⟶ X`. -/
def mappingCylinderTargetInclusion (i : C(A, X)) : C(X, i.mappingCylinder) :=
  (pushout.inl (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A))).hom

/-- The canonical inclusion `A × I ⟶ M_i` of the cylinder side into the mapping cylinder of
`i : A ⟶ X`. -/
def mappingCylinderCylinderInclusion (i : C(A, X)) : C(A × I, i.mappingCylinder) :=
  (pushout.inr (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A))).hom

/-- The canonical inclusions into `M_i` form a commuting square with `i` and the time-`0`
inclusion `A ⟶ A × I`. -/
theorem mappingCylinderInclusion_commSq (i : C(A, X)) :
    CommSq (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A))
      (TopCat.ofHom (mappingCylinderTargetInclusion i))
      (TopCat.ofHom (mappingCylinderCylinderInclusion i)) := by
  refine ⟨?_⟩
  simpa [mappingCylinderTargetInclusion, mappingCylinderCylinderInclusion] using
    (pushout.condition :
      TopCat.ofHom i ≫
          pushout.inl (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A)) =
        TopCat.ofHom (mappingCylinderTimeZeroInclusion A) ≫
          pushout.inr (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A)))

/-- The canonical inclusions into `M_i` agree on `A` along `i` and the time-`0` inclusion. -/
theorem mappingCylinderTargetInclusion_comp (i : C(A, X)) :
    (mappingCylinderTargetInclusion i).comp i =
      (mappingCylinderCylinderInclusion i).comp (mappingCylinderTimeZeroInclusion A) := by
  simpa using congrArg TopCat.Hom.hom (mappingCylinderInclusion_commSq i).w

/-- Unfolding `mappingCylinder` identifies it with the pushout of `i` and the time-`0`
inclusion `A ⟶ A × I`. -/
theorem mappingCylinder_def (i : C(A, X)) :
    i.mappingCylinder =
      pushout (TopCat.ofHom i) (TopCat.ofHom (mappingCylinderTimeZeroInclusion A)) :=
  rfl

end ContinuousMap
