import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Orientation_7_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_2_2

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Semantic recall via `lean_leansearch`: mathlib exposes the covering-space path-lifting API
-- through `IsCoveringMap.liftPath`, `IsCoveringMap.liftPath_zero`,
-- `IsCoveringMap.liftPath_lifts`, and `IsCoveringMap.eq_liftPath_iff'`.

namespace IsCoveringMap

variable {p : C(E, B)}

/-
Lemma 7.2.4 (1): every covering `p : C(E, B)` is a fibration.

Canonical recall: this is `IsCoveringMap.isFibration` from `Orientation_7_1_1`.
In the local chapter API, this uses the explicit surjectivity hypothesis corresponding
to the textbook covering condition.
-/
#check (IsCoveringMap.isFibration : IsCoveringMap p → Function.Surjective p → IsFibration p)

/-- The canonical path lifting function attached to a covering map `p : C(E, B)`. -/
noncomputable def pathLiftingFunction (cov : IsCoveringMap p) : PathLiftingFunction p where
  toFun x := cov.liftPath x.path x.point x.path_zero_eq
  source_eq x := by
    simpa using cov.liftPath_zero x.path x.point x.path_zero_eq
  proj_comp_eq x := by
    simpa using cov.liftPath_lifts x.path x.point x.path_zero_eq

#print axioms IsCoveringMap.pathLiftingFunction

/--
Lemma 7.2.4 (2): the second assertion says the path lifting function of a covering
`p : C(E, B)` is unique.
-/
theorem eq_pathLiftingFunction (cov : IsCoveringMap p) (s : PathLiftingFunction p) :
    s = cov.pathLiftingFunction := by
  cases s with
  | mk toFun source_eq proj_comp_eq =>
      have htoFun : toFun = fun x ↦ cov.liftPath x.path x.point x.path_zero_eq := by
        funext x
        exact (cov.eq_liftPath_iff' x.path_zero_eq).2 ⟨proj_comp_eq x, source_eq x⟩
      cases htoFun
      rfl

end IsCoveringMap
