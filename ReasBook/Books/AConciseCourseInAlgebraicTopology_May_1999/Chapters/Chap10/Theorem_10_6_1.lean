import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWApproximation
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homeomorph.Lemmas

open Topology
open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: `IsCWApproximation γA` is the Chapter 10 owner for a
-- chosen CW approximation of the boundary model, while
-- `Topology.RelCWComplex (Set.univ : Set ΓX) B` is the
-- canonical classical owner for a chosen CW pair `(ΓX, B)`, `Topology.IsEmbedding.toHomeomorph`
-- is the standard bridge from an embedding to its range, and Chapter 11 fixes
-- `SpacePair.Hom.IsNEquivalence` together with the induced continuous map
-- `SpacePair.Hom.mapSubspace` on distinguished subspaces as the source-faithful pair-level
-- approximation surface. The source theorem therefore keeps the Chapter 10 approximation owner
-- on the
-- boundary model `ΓA`, returns the ambient chapter-local CW witness on `ΓX`, records the
-- distinguished-subspace pair structure by `Topology.RelCWComplex (Set.univ : Set ΓX)
-- (Set.range i)`, and expresses the boundary extension clause through the standard
-- embedding-to-range homeomorphism.

/-- Theorem 10.6.1: if `γA : C(ΓA, A)` is a chosen CW approximation of the subspace `A ⊆ X`,
recorded by the Chapter 10 owner `IsCWApproximation γA`, then one can extend it to a CW pair
`(ΓX, ΓA)` over `(X, A)` by choosing an ambient CW approximation space `ΓX` with CW owner
`hΓX : TopCat.CWComplex ΓX`, embedding `ΓA` as the distinguished subspace `Set.range i ⊆ ΓX`,
equipping `(ΓX, Set.range i)` with a relative CW structure, and obtaining a weak equivalence of
pairs `(ΓX, Set.range i) ⟶ (X, A)` in the sense of pair `n`-equivalences whose induced map on
the distinguished subspace agrees with `γA` after identifying `ΓA` with `Set.range i` via
`Topology.IsEmbedding.toHomeomorph`. -/
theorem exists_cwPairApproximation_extending
    (X : TopCat.{u}) (A : Set X) (ΓA : TopCat.{u})
    (γA : C(ΓA, TopCat.of A)) [IsCWApproximation γA] :
    ∃ (ΓX : TopCat.{u}) (hΓX : TopCat.CWComplex ΓX) (i : ΓA ⟶ ΓX)
      (h_embedding : IsEmbedding i)
      (h_rel : Topology.RelCWComplex (Set.univ : Set ΓX) (Set.range i))
      (f : SpacePair.Hom
        { space := ΓX, subspace := Set.range i }
        { space := X, subspace := A }),
        (∀ n : ℕ, SpacePair.Hom.IsNEquivalence n f) ∧
          f.mapSubspace.comp h_embedding.toHomeomorph = γA := sorry
