import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Axiom_13_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomotopicalAlgebra
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only generic long-exact-sequence owners in
-- mathlib, not a source-faithful owner for the triple sequence on a Chapter 13 pair homology
-- theory. The triple pair `(A, B)` is therefore kept source-facing here, while the ambient pairs
-- `(X, A)` and `(X, B)` reuse the chapter-level owner `subsetPair`.

/-- The pair `(A, B)` attached to nested subsets `B ⊆ A ⊆ X`, regarded as a `SpacePair` with
ambient space `A` and distinguished subspace `B`. -/
abbrev tripleSubpair {X : TopCat.{u}} (A B : Set X) : SpacePair :=
  subsetPair (TopCat.of A) (Subtype.val ⁻¹' B)

/-- The ambient-relative pair `(X, A)`, reusing the chapter-level `subsetPair` owner. -/
abbrev subspacePair {X : TopCat.{u}} (A : Set X) : SpacePair :=
  subsetPair X A

/-- The inclusion `(A, B) ⟶ (X, B)` induced by the subtype embedding `A ↪ X`. -/
def tripleLeftPairHom {X : TopCat.{u}} (A B : Set X) :
    tripleSubpair A B ⟶ subspacePair B where
  hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  map_subspace' := by
    intro x hx
    exact hx

/-- The identity-on-ambient-space map `(X, B) ⟶ (X, A)` determined by an inclusion `B ⊆ A`. -/
abbrev tripleRightPairHom {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    subspacePair B ⟶ subspacePair A :=
  subsetPairInclusion hBA

@[simp] theorem tripleRightPairHom_rfl {X : TopCat.{u}} (A : Set X) :
    tripleRightPairHom Set.Subset.rfl = 𝟙 (subspacePair A) :=
  subsetPairInclusion_rfl A

@[simp] theorem tripleRightPairHom_comp {X : TopCat.{u}} {A B C : Set X}
    (hAB : B ⊆ A) (hBC : C ⊆ B) :
    tripleRightPairHom (Set.Subset.trans hBC hAB) =
      tripleRightPairHom hBC ≫ tripleRightPairHom hAB :=
  subsetPairInclusion_comp hAB hBC

/-- The degree-`q` map `E_q(A, B) ⟶ E_q(X, B)` induced by the inclusion of pairs
`(A, B) ⟶ (X, B)`. -/
abbrev tripleLeftHomologyMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} (A B : Set X) :
    (H.homology q).obj (tripleSubpair A B) ⟶ (H.homology q).obj (subspacePair B) :=
  (H.homology q).map (tripleLeftPairHom A B)

/-- The degree-`q` map `E_q(X, B) ⟶ E_q(X, A)` induced by the map of pairs `(X, B) ⟶ (X, A)`. -/
abbrev tripleRightHomologyMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    (H.homology q).obj (subspacePair B) ⟶ (H.homology q).obj (subspacePair A) :=
  (H.homology q).map (tripleRightPairHom hBA)

/- The connecting morphism for a triple is assembled from the pair boundary
`E_q(X, A) ⟶ E_(q - 1)(A, ∅)` and the canonical map `(A, ∅) ⟶ (A, B)`. -/
/-- The connecting morphism `E_q(X, A) ⟶ E_(q - 1)(A, B)` in the homology sequence of a triple
`B ⊆ A ⊆ X`, induced from the pair boundary for `(X, A)`. -/
abbrev pairHomologyTheoryTripleBoundary
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} (A B : Set X) :
    (H.homology q).obj (subspacePair A) ⟶ (H.homology (q - 1)).obj (tripleSubpair A B) :=
  (H.boundary q).app (subspacePair A) ≫
    (H.homology (q - 1)).map (absoluteToRelative (tripleSubpair A B))

/-- Proposition 14.5.1 (1): for a triple `B ⊆ A ⊆ X` and a Chapter 13 pair homology theory `E`,
the window `E_q(A, B) ⟶ E_q(X, B) ⟶ E_q(X, A)` is exact. -/
theorem pairHomologyTheoryTripleExact₁
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    Function.Exact (tripleLeftHomologyMap H q A B) (tripleRightHomologyMap H q hBA) := sorry

/-- Proposition 14.5.1 (2): for a triple `B ⊆ A ⊆ X` and a Chapter 13 pair homology theory `E`,
the window `E_q(X, B) ⟶ E_q(X, A) ⟶ E_(q - 1)(A, B)` is exact. -/
theorem pairHomologyTheoryTripleExact₂
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    Function.Exact (tripleRightHomologyMap H q hBA)
      (pairHomologyTheoryTripleBoundary H q A B) := sorry
