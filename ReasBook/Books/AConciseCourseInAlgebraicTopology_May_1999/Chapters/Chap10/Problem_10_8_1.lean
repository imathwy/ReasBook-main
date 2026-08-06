import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_12

noncomputable section

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex` is the canonical owner for CW
-- structures, while `Example_10_1_12` already packages the standard cell decomposition of `CP^n`
-- with its stronger attaching-map data.

namespace ComplexProjectiveSpace

/-- The cell-count pattern required in Problem 10.8.1 for a CW structure on `CP^n`. -/
def HasEvenCellPattern (n : ℕ)
    (cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n))) : Prop :=
  letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := cw
  (∀ m : ℕ,
    m ≤ n →
      Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) =
        1) ∧
  (∀ m : ℕ,
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m + 1))) ∧
  (∀ k : ℕ,
    2 * n < k →
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) k))

end ComplexProjectiveSpace

namespace ComplexProjectiveCWStructure

variable {n : ℕ}

/-- A chosen standard CW structure on `CP^n` satisfies the even-cell pattern from Problem 10.8.1.
-/
theorem hasEvenCellPattern (S : ComplexProjectiveCWStructure n) :
    ComplexProjectiveSpace.HasEvenCellPattern n S.cwComplex := by
  letI := S.cwComplex
  rcases S.spec with ⟨heven, hodd, hhigh, -, -⟩
  exact ⟨heven, hodd, hhigh⟩

end ComplexProjectiveCWStructure

/-- Problem 10.8.1: `CP^n` admits a CW structure with exactly one cell in each even dimension
`2m ≤ 2n`, no odd-dimensional cells, and no cells above dimension `2n`. -/
theorem complexProjectiveSpace_hasCWComplexWithEvenCells (n : ℕ) :
    ∃ cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)),
      ComplexProjectiveSpace.HasEvenCellPattern n cw := by
  -- Reuse the standard CW structure imported from Example 10.1.12 as the existential witness.
  obtain ⟨S⟩ := complexProjectiveSpaceHasStandardCWStructure n
  -- The local bridge theorem packages the structure witness into the exact cell-count predicate.
  exact ⟨S.cwComplex, S.hasEvenCellPattern⟩
