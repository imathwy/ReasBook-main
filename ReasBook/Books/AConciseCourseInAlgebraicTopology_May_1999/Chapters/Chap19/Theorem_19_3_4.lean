import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.RelativeMayerVietorisTriad
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Proposition_19_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_3_3

open CategoryTheory
open CategoryTheory.Limits
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced sheaf-theoretic Mayer-Vietoris owners.
-- Local Chapter 19 precedent already fixes the source-faithful pair-cohomology and triple APIs,
-- while `Triad.relativeMayerVietoris` supplies the shared excisive triad on the subspace
-- `X ⊆ Y`.

/-- The degree-`q` restriction map
`E^q(Y, X) ⟶ E^q(Y, A) ⊞ E^q(Y, B)` induced by `A ⊆ X` and `B ⊆ X`. -/
noncomputable def pairCohomologyRelativeMayerVietorisRestrictionMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    (H q).obj (Opposite.op (subspacePair X)) ⟶
      (H q).obj (Opposite.op (subspacePair A)) ⊞
        (H q).obj (Opposite.op (subspacePair B)) :=
  biprod.lift
    (tripleRestrictionCohomologyMap H q hAX)
    (tripleRestrictionCohomologyMap H q hBX)

/-- The degree-`q` difference map
`E^q(Y, A) ⊞ E^q(Y, B) ⟶ E^q(Y, C)` for `C = A ∩ B`, with the standard minus sign on the
right summand. -/
noncomputable def pairCohomologyRelativeMayerVietorisDifferenceMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} (A B : Set Y) :
    (H q).obj (Opposite.op (subspacePair A)) ⊞
        (H q).obj (Opposite.op (subspacePair B)) ⟶
      (H q).obj (Opposite.op (subspacePair (A ∩ B))) :=
  biprod.desc
    (tripleRestrictionCohomologyMap H q Set.inter_subset_left)
    (-tripleRestrictionCohomologyMap H q Set.inter_subset_right)

@[simp] theorem pairCohomologyRelativeMayerVietorisRestrictionMap_fst
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    pairCohomologyRelativeMayerVietorisRestrictionMap H q hAX hBX ≫ biprod.fst =
      tripleRestrictionCohomologyMap H q hAX := by
  simp [pairCohomologyRelativeMayerVietorisRestrictionMap]

@[simp] theorem pairCohomologyRelativeMayerVietorisRestrictionMap_snd
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    pairCohomologyRelativeMayerVietorisRestrictionMap H q hAX hBX ≫ biprod.snd =
      tripleRestrictionCohomologyMap H q hBX := by
  simp [pairCohomologyRelativeMayerVietorisRestrictionMap]

@[simp] theorem pairCohomologyRelativeMayerVietorisDifferenceMap_inl
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} (A B : Set Y) :
    biprod.inl ≫ pairCohomologyRelativeMayerVietorisDifferenceMap H q A B =
      tripleRestrictionCohomologyMap H q Set.inter_subset_left := by
  simp [pairCohomologyRelativeMayerVietorisDifferenceMap]

@[simp] theorem pairCohomologyRelativeMayerVietorisDifferenceMap_inr
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} (A B : Set Y) :
    biprod.inr ≫ pairCohomologyRelativeMayerVietorisDifferenceMap H q A B =
      -tripleRestrictionCohomologyMap H q Set.inter_subset_right := by
  simp [pairCohomologyRelativeMayerVietorisDifferenceMap]

/-- Theorem 19.3.4: if `X ⊆ Y`, `C = A ∩ B`, and `(X; A, B)` is excisive, then the relative
cohomological Mayer-Vietoris window
`E^q(Y, X) ⟶ E^q(Y, A) ⊞ E^q(Y, B) ⟶ E^q(Y, C)` is exact. -/
theorem pairCohomologyRelativeMayerVietorisExact
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hExcisive : (Triad.relativeMayerVietoris X A B).IsExcisive) :
    Function.Exact
      (pairCohomologyRelativeMayerVietorisRestrictionMap H q hAX hBX)
      (pairCohomologyRelativeMayerVietorisDifferenceMap H q A B) := sorry
