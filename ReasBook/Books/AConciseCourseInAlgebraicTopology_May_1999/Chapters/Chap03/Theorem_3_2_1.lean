import Mathlib.Topology.Homotopy.Lifting
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- Theorem 3.2.1: a path in the base of a covering map and a chosen point of the fiber over its
initial value determine a unique lifted path. -/
-- Proof sketch: convert `hp` to a mathlib covering map using
-- `IsPathConnectedCoveringMap.isCoveringMap`. Use `IsCoveringMap.exists_path_lifts` for existence,
-- and compare any other lift with the canonical one via `IsCoveringMap.eq_liftPath_iff'`.
theorem existsUnique_pathLift (hp : IsPathConnectedCoveringMap p) (gamma : C(I, B))
    (e : p ⁻¹' {gamma 0}) :
    ∃! Gamma : C(I, E), p ∘ Gamma = gamma ∧ Gamma 0 = e := by
  refine ⟨hp.isCoveringMap.liftPath gamma e.1 e.2.symm, ?_, ?_⟩
  · exact ⟨hp.isCoveringMap.liftPath_lifts gamma e.1 e.2.symm,
      hp.isCoveringMap.liftPath_zero gamma e.1 e.2.symm⟩
  · intro Gamma hGamma
    exact (hp.isCoveringMap.eq_liftPath_iff' e.2.symm).2 hGamma

/-- The starting point may equivalently be given by an element `e : E` together with the equality
`gamma 0 = p e`. -/
theorem existsUnique_pathLift_of_eq (hp : IsPathConnectedCoveringMap p) (gamma : C(I, B)) (e : E)
    (h0 : gamma 0 = p e) :
    ∃! Gamma : C(I, E), p ∘ Gamma = gamma ∧ Gamma 0 = e := by
  simpa [Set.mem_singleton_iff] using
    hp.existsUnique_pathLift gamma ⟨e, by simpa [Set.mem_singleton_iff] using h0.symm⟩

end IsPathConnectedCoveringMap
