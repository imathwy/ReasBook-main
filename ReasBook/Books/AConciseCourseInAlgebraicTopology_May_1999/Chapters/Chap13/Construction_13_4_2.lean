import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_6

open Topology

/- Construction 13.4.2. The chosen product CW structure on `X × Y` comes with the canonical
cell-indexing equivalence
`productCWComplex_cellEquiv X Y n :
  (productCWComplex X Y).cell n ≃ productCWCellIndex X Y n`.
The source-facing bijectivity statement is the companion theorem below. -/
#check productCWComplex_cellEquiv

/-- Construction 13.4.2. For the chosen product CW structure on `X × Y`, the cell-indexing map
`productCWComplex_cellEquiv X Y n` is bijective. -/
theorem productCWComplex_cellEquiv_bijective
    (X Y : TopCat) [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] (n : ℕ) :
    Function.Bijective (productCWComplex_cellEquiv X Y n) := by
  simpa using (productCWComplex_cellEquiv X Y n).bijective
