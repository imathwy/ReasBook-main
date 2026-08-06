import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

-- Analogy: mathlib provides `T2Space.t1Space`; this remark adds the intermediate
-- implication `WeaklyHausdorffSpace → T1Space`.
/-- Remark 5.1.6. A weak Hausdorff space is a `T1Space`, so the weak Hausdorff condition
lies between the `T1Space` and `T2Space` conditions. -/
instance WeaklyHausdorffSpace.toT1Space (X : Type u) [TopologicalSpace X]
    [WeaklyHausdorffSpace.{u, v} X] : T1Space X where
  t1 x := by
    simpa [Set.range_const] using
      (show IsClosed (Set.range (fun _ : ULift.{v} Unit ↦ x)) from
        (show Continuous (fun _ : ULift.{v} Unit ↦ x) from continuous_const).isClosed_range)
