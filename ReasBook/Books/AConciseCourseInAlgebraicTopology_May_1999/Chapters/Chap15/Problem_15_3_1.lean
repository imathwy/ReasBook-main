import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.KPiOne
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Result_16_5_3

open scoped Topology

universe u

noncomputable section

/-- Helper for Problem 15.3.1: once the discrete classifying-space model `BG` is equipped with a
pointed `K(π, 1)` witness, the textbook existential statement follows immediately. -/
theorem existsConnectedCWComplexKPiOneOfDiscreteClassifyingWitness (π : Type u) [Group π]
    (h : ∃ x : Bπ π, IsKPiOne π (Bπ π) x) :
    ∃ (X : TopCat.{u}) (x : X), IsKPiOne π X x := by
  rcases h with ⟨x, hx⟩
  -- Repackage the chosen classifying-space basepoint into the requested existential statement.
  exact existsConnectedCWComplexKPiOneOfWitness hx

/-- Problem 15.3.1: for any group `π`, there exists a connected CW complex `X` with a basepoint
`x : X` such that `π₁(X, x) ≃* π` and every higher homotopy group `π_ n X x` with `1 < n` is
trivial. -/
theorem existsConnectedCWComplexKPiOne (π : Type u) [Group π] :
    ∃ (X : TopCat.{u}) (x : X), IsKPiOne π X x := by
  -- Route correction: now that the Chapter 16 classifying-space witness is importable without a
  -- cycle, the textbook existence statement follows by repackaging that pointed witness.
  rcases Bπ.exists_isKPiOne π with ⟨x, hx⟩
  -- Convert the chosen `Bπ` basepoint into the requested existential statement.
  exact existsConnectedCWComplexKPiOneOfWitness hx

end
