import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Proposition_14_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.RelativeMayerVietorisTriad

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only generic Mayer-Vietoris owners in mathlib,
-- not the source-faithful relative pair-homology sequence. Local Chapter 14 precedent already
-- models relative homology terms as `subspacePair` objects and triple connecting morphisms via
-- `pairHomologyTheoryTripleBoundary`, while `Triad.relativeMayerVietoris` supplies the shared
-- excisive triad on the subspace `X ⊆ Y`.

/-- The degree-`q` relative Mayer-Vietoris map
`E_q(Y, A ∩ B) ⟶ E_q(Y, A) ⊞ E_q(Y, B)`, with the standard sign on the right summand. -/
noncomputable def pairHomologyRelativeMayerVietorisIntersectionMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    (A B : Set Y) :
    (H.homology q).obj (subspacePair (A ∩ B)) ⟶
      (H.homology q).obj (subspacePair A) ⊞ (H.homology q).obj (subspacePair B) :=
  biprod.lift
    (tripleRightHomologyMap H q Set.inter_subset_left)
    (-tripleRightHomologyMap H q Set.inter_subset_right)

/-- The degree-`q` relative Mayer-Vietoris map
`E_q(Y, A) ⊞ E_q(Y, B) ⟶ E_q(Y, X)` induced by the inclusions `A ⊆ X` and `B ⊆ X`. -/
noncomputable def pairHomologyRelativeMayerVietorisSumMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    (H.homology q).obj (subspacePair A) ⊞ (H.homology q).obj (subspacePair B) ⟶
      (H.homology q).obj (subspacePair X) :=
  biprod.desc
    (tripleRightHomologyMap H q hAX)
    (tripleRightHomologyMap H q hBX)

/-- The relative Mayer-Vietoris connecting morphism `E_q(Y, X) ⟶ E_(q - 1)(Y, A ∩ B)`, formed
from the triple boundary for `A ∩ B ⊆ X ⊆ Y` and the inclusion `(X, A ∩ B) ⟶ (Y, A ∩ B)`. -/
noncomputable abbrev pairHomologyRelativeMayerVietorisBoundary
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    (X A B : Set Y) :
    (H.homology q).obj (subspacePair X) ⟶
      (H.homology (q - 1)).obj (subspacePair (A ∩ B)) :=
  pairHomologyTheoryTripleBoundary H q X (A ∩ B) ≫
    tripleLeftHomologyMap H (q - 1) X (A ∩ B)

@[simp] theorem pairHomologyRelativeMayerVietorisIntersectionMap_fst
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    (A B : Set Y) :
    pairHomologyRelativeMayerVietorisIntersectionMap H q A B ≫ biprod.fst =
      tripleRightHomologyMap H q Set.inter_subset_left := by
  simp [pairHomologyRelativeMayerVietorisIntersectionMap]

@[simp] theorem pairHomologyRelativeMayerVietorisIntersectionMap_snd
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    (A B : Set Y) :
    pairHomologyRelativeMayerVietorisIntersectionMap H q A B ≫ biprod.snd =
      -tripleRightHomologyMap H q Set.inter_subset_right := by
  simp [pairHomologyRelativeMayerVietorisIntersectionMap]

@[simp] theorem pairHomologyRelativeMayerVietorisSumMap_inl
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    biprod.inl ≫ pairHomologyRelativeMayerVietorisSumMap H q hAX hBX =
      tripleRightHomologyMap H q hAX := by
  simp [pairHomologyRelativeMayerVietorisSumMap]

@[simp] theorem pairHomologyRelativeMayerVietorisSumMap_inr
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    biprod.inr ≫ pairHomologyRelativeMayerVietorisSumMap H q hAX hBX =
      tripleRightHomologyMap H q hBX := by
  simp [pairHomologyRelativeMayerVietorisSumMap]

/-- Theorem 14.5.4 (1): if `X ⊆ Y` and `(X; A, B)` is excisive, then the relative
Mayer-Vietoris sequence is exact at `E_q(Y, A) ⊞ E_q(Y, B)`, i.e.
`E_q(Y, A ∩ B) ⟶ E_q(Y, A) ⊞ E_q(Y, B) ⟶ E_q(Y, X)` is exact. -/
theorem pairHomologyRelativeMayerVietorisExact₁
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hExcisive : (Triad.relativeMayerVietoris X A B).IsExcisive) :
    Function.Exact
      (pairHomologyRelativeMayerVietorisIntersectionMap H q A B)
      (pairHomologyRelativeMayerVietorisSumMap H q hAX hBX) := sorry

/-- Theorem 14.5.4 (2): if `X ⊆ Y` and `(X; A, B)` is excisive, then the relative
Mayer-Vietoris sequence is exact at `E_q(Y, X)`, i.e.
`E_q(Y, A) ⊞ E_q(Y, B) ⟶ E_q(Y, X) ⟶ E_(q - 1)(Y, A ∩ B)` is exact. -/
theorem pairHomologyRelativeMayerVietorisExact₂
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hExcisive : (Triad.relativeMayerVietoris X A B).IsExcisive) :
    Function.Exact
      (pairHomologyRelativeMayerVietorisSumMap H q hAX hBX)
      (pairHomologyRelativeMayerVietorisBoundary H q X A B) := sorry

/-- Theorem 14.5.4 (3): if `X ⊆ Y` and `(X; A, B)` is excisive, then the relative
Mayer-Vietoris sequence is exact at `E_(q - 1)(Y, A ∩ B)`, i.e.
`E_q(Y, X) ⟶ E_(q - 1)(Y, A ∩ B) ⟶ E_(q - 1)(Y, A) ⊞ E_(q - 1)(Y, B)` is exact. -/
theorem pairHomologyRelativeMayerVietorisExact₃
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hExcisive : (Triad.relativeMayerVietoris X A B).IsExcisive) :
    Function.Exact
      (pairHomologyRelativeMayerVietorisBoundary H q X A B)
      (pairHomologyRelativeMayerVietorisIntersectionMap H (q - 1) A B) := sorry
