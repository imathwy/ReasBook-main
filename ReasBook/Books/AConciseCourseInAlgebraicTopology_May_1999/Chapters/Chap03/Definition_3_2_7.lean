import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FundamentalGroup

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

/-- Definition 3.2.7: a covering map in the sense of Definition 3.1.5 is universal when its total
space `E` is simply connected. -/
class IsUniversalCoveringMap (p : E → X) : Prop
    extends IsPathConnectedCoveringMap p, SimplyConnectedSpace E

namespace IsUniversalCoveringMap

variable {p : E → X}

/-- A universal covering map is, in particular, a path-connected covering map in the sense of
Definition 3.1.5. -/
theorem isPathConnectedCoveringMap (hp : IsUniversalCoveringMap p) :
    IsPathConnectedCoveringMap p :=
  hp.1

/-- A universal covering map is surjective. -/
theorem surjective (hp : IsUniversalCoveringMap p) : Function.Surjective p :=
  IsPathConnectedCoveringMap.surjective hp.1

/-- A universal covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsUniversalCoveringMap p) : IsCoveringMap p :=
  IsPathConnectedCoveringMap.isCoveringMap hp.1

/-- A universal covering map has path-connected total space. -/
theorem pathConnectedSpace (hp : IsUniversalCoveringMap p) : PathConnectedSpace E := by
  letI : IsUniversalCoveringMap p := hp
  infer_instance

section FundamentalGroup

variable {p : C(E, X)}

/-- For a universal covering, the image subgroup of `π₁(E, e.1) → π₁(X, x)` is trivial at every
chosen fiber point `e : p ⁻¹' {x}`. -/
theorem fundamentalGroup_mapOfEq_range_eq_bot (hp : IsUniversalCoveringMap p) {x : X}
    (e : p ⁻¹' {x}) :
    (FundamentalGroup.mapOfEq p e.2).range = ⊥ := by
  letI : IsUniversalCoveringMap p := hp
  have hsub : Subsingleton (FundamentalGroup E e.1) := by
    change Subsingleton (Path.Homotopic.Quotient e.1 e.1)
    infer_instance
  letI := hsub
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact Subsingleton.elim _ _
  rw [hγ, map_one, MonoidHom.one_apply]

/-- For a universal covering, the induced map `p_* : π₁(E, e) → π₁(X, p e)` has trivial image. -/
theorem fundamentalGroup_map_range_eq_bot (hp : IsUniversalCoveringMap p) (e : E) :
    (FundamentalGroup.map p e).range = ⊥ := by
  letI : IsUniversalCoveringMap p := hp
  have hsub : Subsingleton (FundamentalGroup E e) := by
    change Subsingleton (Path.Homotopic.Quotient e e)
    infer_instance
  letI := hsub
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact Subsingleton.elim _ _
  rw [hγ, map_one, MonoidHom.one_apply]

end FundamentalGroup

end IsUniversalCoveringMap
