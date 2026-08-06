import Mathlib.Topology.UnitInterval
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_6

open Topology
open scoped unitInterval

universe u

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex` and
-- `Topology.CWComplex.Subcomplex` are the canonical owners for classical CW structures and their
-- subcomplexes in the current mathlib snapshot. Local precedent from `Lemma_10_2_6` uses an
-- explicit cell-indexing equivalence when the source specifies the cell count.

/-- The boundary copy `X × ∂I` inside the cylinder `X × I`, written concretely as the subset of
pairs whose interval coordinate is one of the endpoints `0` or `1`. -/
def cylinderBoundary (X : Type u) [TopologicalSpace X] : Set (X × I) :=
  { xt | xt.2 = 0 ∨ xt.2 = 1 }

/-- A chosen CW structure on `X × I` has the cylinder shape from Lemma 10.2.7 when the boundary
copy `X × ∂I` is a subcomplex containing every `0`-cell and its complementary `(n + 1)`-cells are
indexed by the `n`-cells of `X`. -/
inductive IsCylinderCWStructure
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (cw : CWComplex (Set.univ : Set (X × I))) : Prop where
  | mk
      (boundarySubcomplex : CWComplex.Subcomplex (Set.univ : Set (X × I)))
      (relativeCellEquiv :
        ∀ n : ℕ,
          { j : cw.cell (n + 1) // j ∉ boundarySubcomplex.I (n + 1) } ≃
            Topology.CWComplex.cell (Set.univ : Set X) n)
      (boundarySubcomplex_eq :
        (boundarySubcomplex : Set (X × I)) = cylinderBoundary X)
      (zeroCell_compl_isEmpty :
        IsEmpty { j : cw.cell 0 // j ∉ boundarySubcomplex.I 0 }) :
      IsCylinderCWStructure X cw

namespace IsCylinderCWStructure

variable {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
variable {cw : CWComplex (Set.univ : Set (X × I))}

/-- The source-facing specification of a cylinder CW structure: the boundary subcomplex is
`X × ∂I`, it contains all `0`-cells, and its complementary `(n + 1)`-cells are indexed by the
`n`-cells of `X`. -/
theorem spec (h : IsCylinderCWStructure X cw) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set (X × I)),
      ∃ _ :
        ∀ n : ℕ,
          { j : cw.cell (n + 1) // j ∉ E.I (n + 1) } ≃
            Topology.CWComplex.cell (Set.univ : Set X) n,
        (E : Set (X × I)) = cylinderBoundary X ∧
          IsEmpty { j : cw.cell 0 // j ∉ E.I 0 } := by
  rcases h with ⟨E, hrel, hE, h0⟩
  exact ⟨E, hrel, hE, h0⟩

/-- A cylinder CW structure exposes the boundary copy `X × ∂I` as a subcomplex containing all
`0`-cells. -/
theorem boundarySubcomplex_spec (h : IsCylinderCWStructure X cw) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set (X × I)),
      (E : Set (X × I)) = cylinderBoundary X ∧
        ∀ j : cw.cell 0, j ∈ E.I 0 := by
  rcases h.spec with ⟨E, _, hE, h0⟩
  refine ⟨E, hE, ?_⟩
  intro j
  by_contra hj
  exact h0.false ⟨j, hj⟩

/-- A cylinder CW structure reindexes the complementary `(n + 1)`-cells by the `n`-cells of `X`
once the boundary subcomplex is fixed. -/
theorem relativeCellEquiv_spec (h : IsCylinderCWStructure X cw) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set (X × I)),
      ∃ _ :
        ∀ n : ℕ,
          { j : cw.cell (n + 1) // j ∉ E.I (n + 1) } ≃
            Topology.CWComplex.cell (Set.univ : Set X) n,
        (E : Set (X × I)) = cylinderBoundary X := by
  rcases h.spec with ⟨E, hrel, hE, _⟩
  exact ⟨E, hrel, hE⟩

end IsCylinderCWStructure

/-- Lemma 10.2.7 applied to the chosen product CW structure on `X × I` from Lemma 10.2.6. -/
theorem productCWComplex_isCylinderCWStructure
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex (Set.univ : Set I)] [CompactlyGeneratedSpace (X × I)] :
    IsCylinderCWStructure X (productCWComplex X I) := sorry

/-- Lemma 10.2.7. For a CW complex `X`, the cylinder `X × I` admits a CW structure in which
`X × ∂I`, formalized as `cylinderBoundary X`, is a subcomplex containing all `0`-cells, and the
complementary `(n + 1)`-cells are indexed by the `n`-cells of `X`. -/
theorem cylinder_hasBoundarySubcomplexAndRelativeCells
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    ∃ cw : CWComplex (Set.univ : Set (X × I)), IsCylinderCWStructure X cw := sorry

/-- The cylinder of a CW complex admits a CW-complex structure. -/
theorem cylinder_isCWComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    Nonempty (CWComplex (Set.univ : Set (X × I))) := by
  rcases cylinder_hasBoundarySubcomplexAndRelativeCells X with ⟨cw, _⟩
  exact ⟨cw⟩
