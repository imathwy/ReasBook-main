import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_6_1

open Topology
open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: no more canonical owner for the source's
-- "no relative q-cells for q ≤ n" clause surfaced than the local Chapter 10 predicate
-- `Topology.RelCWComplex.NoCellsLE`. The refinement therefore strengthens
-- `exists_cwPairApproximation_extending` by keeping its ambient CW-complex owner
-- `hΓX : TopCat.CWComplex ΓX`, its existing `Set.range i` pair surface, and adding `NoCellsLE`
-- for the chosen relative CW structure, while reusing the Chapter 10 owner
-- `IsCWApproximation γA` for the boundary approximation data.

/-- Refinement 10.6.3: if `(X, A)` is `n`-connected, then the CW pair approximation from
Theorem 10.6.1 can be chosen so that the relative CW structure on `(ΓX, ΓA)` has no relative
`q`-cells for every `q ≤ n`. The pair is expressed on the canonical distinguished subspace
`Set.range i ⊆ ΓX`, the ambient CW approximation owner `hΓX : TopCat.CWComplex ΓX` from
Theorem 10.6.1 is retained explicitly, and the low-dimensional cell-vanishing clause is recorded
by `h_rel.NoCellsLEOf n` for the chosen relative CW structure `h_rel`; the boundary extension
clause is recorded on the induced subspace map `f.mapSubspace : C(Set.range i, A)` after
identifying `ΓA` with `Set.range i` via `h_embedding.toHomeomorph`. -/
theorem exists_cwPairApproximation_extending_noCellsLE
    (X : TopCat.{u}) (A : Set X) (n : ℕ) [NConnectedPair n A]
    (ΓA : TopCat.{u}) (γA : C(ΓA, TopCat.of A)) [IsCWApproximation γA] :
    ∃ (ΓX : TopCat.{u}) (hΓX : TopCat.CWComplex ΓX) (i : ΓA ⟶ ΓX)
      (h_embedding : IsEmbedding i)
      (h_rel : Topology.RelCWComplex (Set.univ : Set ΓX) (Set.range i))
      (f : SpacePair.Hom
        { space := ΓX, subspace := Set.range i }
        { space := X, subspace := A }),
        h_rel.NoCellsLEOf n ∧
          (∀ m : ℕ, SpacePair.Hom.IsNEquivalence m f) ∧
            f.mapSubspace.comp h_embedding.toHomeomorph = γA := sorry
