import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_5_4

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only sheaf-theoretic Mayer-Vietoris squares in
-- mathlib. The source corollary is therefore stated directly on the local `PairHomologyTheory`
-- Mayer-Vietoris APIs, reusing the neutral pair-level restriction maps from `Chap14.SubsetPair`.

/-- The homology map induced by restricting the absolute pair on `A ⊆ Y` to the corresponding
restricted subset of `X`. -/
abbrev pairHomologyMayerVietorisRestrictionHomologyMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A : Set Y} (hAX : A ⊆ X) :
    (H.homology q).obj (absolute (TopCat.of A)) ⟶
      (H.homology q).obj (absolute (TopCat.of (restrictedSubset X A))) :=
  (H.homology q).map (restrictionAbsoluteMap hAX)

/-- The comparison map from the relative homology of `(Y, A)` to the absolute homology of the
restricted subset of `X`, obtained by the pair boundary followed by restriction. -/
abbrev pairHomologyMayerVietorisBoundaryRestrictionMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A : Set Y} (hAX : A ⊆ X) :
    (H.homology q).obj (subspacePair A) ⟶
      (H.homology (q - 1)).obj
        (absolute (TopCat.of (restrictedSubset X A))) :=
  (H.boundary q).app (subspacePair A) ≫
    pairHomologyMayerVietorisRestrictionHomologyMap H (q - 1) hAX

/-- The homology map induced by restricting the absolute pair on `A ∩ B ⊆ Y` to the common
restricted subset of `X`. -/
abbrev pairHomologyMayerVietorisIntersectionRestrictionHomologyMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X) :
    (subspaceFunctor ⋙ H.homology q).obj (subspacePair (A ∩ B)) ⟶
      (H.homology q).obj
        (pairHomologyMayerVietorisIntersectionAbsolutePair
          (restrictedSubset X A)
          (restrictedSubset X B)) :=
  (H.homology q).map (intersectionRestrictionAbsoluteMap hAX)

/-- The comparison map from the relative homology of `(Y, A ∩ B)` to the absolute homology of the
restricted intersection in `X`, obtained by the pair boundary followed by restriction. -/
abbrev pairHomologyMayerVietorisIntersectionBoundaryRestrictionMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X) :
    (H.homology q).obj (subspacePair (A ∩ B)) ⟶
      (H.homology (q - 1)).obj
        (pairHomologyMayerVietorisIntersectionAbsolutePair
          (restrictedSubset X A)
          (restrictedSubset X B)) :=
  (H.boundary q).app (subspacePair (A ∩ B)) ≫
    pairHomologyMayerVietorisIntersectionRestrictionHomologyMap H (q - 1) hAX

/-- Corollary 14.5.5 (1): the left square comparing the relative Mayer-Vietoris map
`E_q(Y, A ∩ B) ⟶ E_q(Y, A) ⊞ E_q(Y, B)` with the absolute Mayer-Vietoris map on the subspace
`X` commutes after passing to the pair-boundary maps. -/
theorem pairHomologyMayerVietorisBoundaryDiagramIntersection
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X)
    (hBX : B ⊆ X) :
    CommSq
      (pairHomologyRelativeMayerVietorisIntersectionMap H q A B)
      (pairHomologyMayerVietorisIntersectionBoundaryRestrictionMap H q hAX)
      (biprod.map
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hAX)
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hBX))
      (pairHomologyMayerVietorisIntersectionMap H
        (restrictedSubset X A)
        (restrictedSubset X B)
        (q - 1)) := by
  sorry

/-- Corollary 14.5.5 (1) as an equality of composites. -/
theorem pairHomologyMayerVietorisBoundaryDiagramIntersection_w
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X)
    (hBX : B ⊆ X) :
    pairHomologyMayerVietorisIntersectionBoundaryRestrictionMap H q hAX ≫
        pairHomologyMayerVietorisIntersectionMap H
          (restrictedSubset X A)
          (restrictedSubset X B)
          (q - 1) =
      pairHomologyRelativeMayerVietorisIntersectionMap H q A B ≫
        biprod.map
          (pairHomologyMayerVietorisBoundaryRestrictionMap H q hAX)
          (pairHomologyMayerVietorisBoundaryRestrictionMap H q hBX) :=
  (pairHomologyMayerVietorisBoundaryDiagramIntersection H q hAX hBX).w.symm

/-- Corollary 14.5.5 (2): the middle square comparing
`E_q(Y, A) ⊞ E_q(Y, B) ⟶ E_q(Y, X)` with the absolute Mayer-Vietoris sum map on `X` commutes
after passing to the pair-boundary maps. -/
theorem pairHomologyMayerVietorisBoundaryDiagramSum
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X)
    (hBX : B ⊆ X) :
    CommSq
      (pairHomologyRelativeMayerVietorisSumMap H q hAX hBX)
      (biprod.map
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hAX)
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hBX))
      ((H.boundary q).app (subspacePair X))
      (pairHomologyMayerVietorisSumMap H
        (restrictedSubset X A)
        (restrictedSubset X B)
        (q - 1)) := by
  sorry

/-- Corollary 14.5.5 (2) as an equality of composites. -/
theorem pairHomologyMayerVietorisBoundaryDiagramSum_w
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X)
    (hBX : B ⊆ X) :
    biprod.map
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hAX)
        (pairHomologyMayerVietorisBoundaryRestrictionMap H q hBX) ≫
      pairHomologyMayerVietorisSumMap H
        (restrictedSubset X A)
        (restrictedSubset X B)
        (q - 1) =
    pairHomologyRelativeMayerVietorisSumMap H q hAX hBX ≫
      (H.boundary q).app (subspacePair X) :=
  (pairHomologyMayerVietorisBoundaryDiagramSum H q hAX hBX).w.symm

/-- Corollary 14.5.5 (3): the right square comparing the relative Mayer-Vietoris boundary
`E_q(Y, X) ⟶ E_(q - 1)(Y, A ∩ B)` with the absolute Mayer-Vietoris boundary on `X` commutes
after composing with the pair-boundary map of `(Y, A ∩ B)`. -/
theorem pairHomologyMayerVietorisBoundaryDiagramBoundary
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X) :
    CommSq
      (pairHomologyRelativeMayerVietorisBoundary H q X A B)
      ((H.boundary q).app (subspacePair X))
      (pairHomologyMayerVietorisIntersectionBoundaryRestrictionMap H (q - 1) hAX)
      (pairHomologyMayerVietorisBoundary H
        (restrictedSubset X A)
        (restrictedSubset X B)
        (q - 1)) := by
  sorry

/-- Corollary 14.5.5 (3) as an equality of composites. -/
theorem pairHomologyMayerVietorisBoundaryDiagramBoundary_w
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) {Y : TopCat.{u}}
    {X A B : Set Y} (hAX : A ⊆ X) :
    (H.boundary q).app (subspacePair X) ≫
      pairHomologyMayerVietorisBoundary H
        (restrictedSubset X A)
        (restrictedSubset X B)
        (q - 1) =
    pairHomologyRelativeMayerVietorisBoundary H q X A B ≫
      pairHomologyMayerVietorisIntersectionBoundaryRestrictionMap H (q - 1) hAX :=
  (pairHomologyMayerVietorisBoundaryDiagramBoundary H q hAX).w.symm
