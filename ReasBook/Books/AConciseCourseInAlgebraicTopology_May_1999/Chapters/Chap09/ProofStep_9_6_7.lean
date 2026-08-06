import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6

open scoped Topology Topology.Homotopy

universe u v

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

/-- ProofStep 9.6.7: the special case of the technical lifting lemma gives injectivity of the
induced map on `π_ n`; if `e ∘ g` is null-homotopic, the lifted null homotopy shows that `g`
itself represents the trivial class. -/
theorem HasSphereConeHelp.injective_homotopyGroupMap
    {n : ℕ} {e : C(Y, Z)} (h : HasSphereConeHelp n e) (y : Y) :
    Function.Injective (e.eStar n y) := by
  exact (h.hasPiInjectiveSurjectiveSucc).injective y
