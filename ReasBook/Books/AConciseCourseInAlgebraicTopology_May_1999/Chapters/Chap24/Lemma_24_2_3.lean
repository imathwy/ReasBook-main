import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open CategoryTheory Limits
open HomotopicalAlgebra
open scoped BasedSpace ComplexKTheory

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` did not surface a verified reduced topological `K`-theory
-- owner for smash products in this environment. The source-facing statement therefore reuses the
-- repository's canonical Chapter 2 `BasedSpace`/`underTopBasepoint` owner together with the
-- Chapter 19 notion of nondegenerately based space and the Chapter 8 smash-product owner
-- `smashProduct`.

/-- The smash product of compact based spaces is compact. This supplies the compactness input for
`K̃((X ∧ Y).right, underTopBasepoint (X ∧ Y))` from the compactness of the two factors,
instead of exposing that quotient compactness as an extra theorem hypothesis. -/
instance smashProductCompactSpace
    (X Y : BasedSpace) [CompactSpace X.right] [CompactSpace Y.right] :
    CompactSpace (X ∧ Y).right := by
  change CompactSpace (smashProductType X Y)
  infer_instance

/-- Lemma 24.2.3: for compact nondegenerately based spaces `X` and `Y`, the finite direct sum
`K̃(X ∧ Y) ⊕ K̃(X) ⊕ K̃(Y)` is additively isomorphic to `K̃(X × Y)`. On this Lean surface, the
finite direct sum is represented by the canonically equivalent iterated product of additive groups,
the smash product is the Chapter 8 quotient `smashProduct`, and the reduced groups are the Chapter
24 groups written directly as `K̃(...)` at the distinguished points; nondegeneracy is expressed by
the cofibrancy hypotheses `[IsCofibrant X]` and `[IsCofibrant Y]`. -/
theorem reducedComplexKTheorySmashProductSumEquivProduct
    [CategoryWithCofibrations BasedSpace]
    (X Y : BasedSpace) [IsCofibrant X] [IsCofibrant Y]
    [CompactSpace X.right] [CompactSpace Y.right] :
    Nonempty
      ((((K̃((X ∧ Y).right, underTopBasepoint (X ∧ Y))) ×
          K̃(X.right, underTopBasepoint X)) ×
        K̃(Y.right, underTopBasepoint Y)) ≃+
        K̃(X.right × Y.right, (underTopBasepoint X, underTopBasepoint Y))) := sorry
