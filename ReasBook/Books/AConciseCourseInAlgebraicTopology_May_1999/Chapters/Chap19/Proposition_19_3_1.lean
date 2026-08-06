import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Proposition_14_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only unrelated general long-exact-sequence APIs
-- in group cohomology and derived categories. Local precedent from `Proposition_14_5_1` already
-- provides the generic triple pair maps, and `PairCohomologyTheory` from Chapter 18 is the
-- source-faithful owner for the cohomological exactness data used here.

/-- The degree-`q` restriction map `H^q(X, A) ⟶ H^q(X, B)` induced by the map of pairs
`(X, B) ⟶ (X, A)` coming from `B ⊆ A`. -/
abbrev tripleRestrictionCohomologyMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    (H q).obj (Opposite.op (subspacePair A)) ⟶
      (H q).obj (Opposite.op (subspacePair B)) :=
  (H q).map (tripleRightPairHom hBA).op

@[simp] theorem tripleRestrictionCohomologyMap_rfl
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} (A : Set X) :
    tripleRestrictionCohomologyMap H q Set.Subset.rfl =
      𝟙 ((H q).obj (Opposite.op (subspacePair A))) := by
  simp [tripleRestrictionCohomologyMap]

@[simp] theorem tripleRestrictionCohomologyMap_comp
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B C : Set X} (hAB : B ⊆ A) (hBC : C ⊆ B) :
    tripleRestrictionCohomologyMap H q (Set.Subset.trans hBC hAB) =
      tripleRestrictionCohomologyMap H q hAB ≫ tripleRestrictionCohomologyMap H q hBC := by
  rw [tripleRestrictionCohomologyMap, tripleRestrictionCohomologyMap,
    tripleRestrictionCohomologyMap]
  rw [tripleRightPairHom_comp hAB hBC]
  simp

/-- The degree-`q` restriction map `H^q(X, B) ⟶ H^q(A, B)` induced by the inclusion of pairs
`(A, B) ⟶ (X, B)`. -/
abbrev tripleSubpairRestrictionCohomologyMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} (A B : Set X) :
    (H q).obj (Opposite.op (subspacePair B)) ⟶
      (H q).obj (Opposite.op (tripleSubpair A B)) :=
  (H q).map (tripleLeftPairHom A B).op

/-- The connecting morphism `H^q(A, B) ⟶ H^(q + 1)(X, A)` in the cohomology sequence of a triple
`B ⊆ A ⊆ X`, obtained by first forgetting `B` and then applying the pair boundary for `(X, A)`. -/
abbrev pairCohomologyTheoryTripleBoundary
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} (A B : Set X) :
    (H q).obj (Opposite.op (tripleSubpair A B)) ⟶
      (H (q + 1)).obj (Opposite.op (subspacePair A)) :=
  (H q).map (absoluteToRelative (tripleSubpair A B)).op ≫
    (H.boundary q).app (Opposite.op (subspacePair A))

/-- Proposition 19.3.1 (1): for a triple `B ⊆ A ⊆ X` and a Chapter 18 pair cohomology theory
`E`, the window `H^q(X, A) ⟶ H^q(X, B) ⟶ H^q(A, B)` is exact. -/
theorem pairCohomologyTheoryTripleExact₁
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    Function.Exact (tripleRestrictionCohomologyMap H q hBA)
      (tripleSubpairRestrictionCohomologyMap H q A B) := sorry

/-- Proposition 19.3.1 (2): for a triple `B ⊆ A ⊆ X` and a Chapter 18 pair cohomology theory
`E`, the window `H^q(X, B) ⟶ H^q(A, B) ⟶ H^(q + 1)(X, A)` is exact. -/
theorem pairCohomologyTheoryTripleExact₂
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    Function.Exact (tripleSubpairRestrictionCohomologyMap H q A B)
      (pairCohomologyTheoryTripleBoundary H q A B) := sorry

/-- Proposition 19.3.1 (3): for a triple `B ⊆ A ⊆ X` and a Chapter 18 pair cohomology theory
`E`, the window `H^q(A, B) ⟶ H^(q + 1)(X, A) ⟶ H^(q + 1)(X, B)` is exact. -/
theorem pairCohomologyTheoryTripleExact₃
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    Function.Exact (pairCohomologyTheoryTripleBoundary H q A B)
      (tripleRestrictionCohomologyMap H (q + 1) hBA) := sorry
