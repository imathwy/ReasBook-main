import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_3_4

open CategoryTheory
open CategoryTheory.Limits
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced sheaf-theoretic Mayer-Vietoris squares.
-- Local Chapter 14 precedent from `Corollary_14_5_5`, together with the Chapter 14 owner
-- `Triad.relativeMayerVietoris` and the Chapter 19 absolute/relative Mayer-Vietoris APIs,
-- provides the source-faithful cohomological comparison diagram, reusing the neutral
-- pair-level restriction maps from `Chap14.SubsetPair`.

/-- The cohomology map induced by restricting the absolute pair on `A ∩ B ⊆ Y` to the common
restricted subset of `X`. -/
abbrev pairCohomologyMayerVietorisIntersectionRestrictionCohomologyMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) :
    (H.cohomology q).obj
        (Opposite.op
          (pairCohomologyMayerVietorisIntersectionAbsolutePair
            (restrictedSubset X A)
            (restrictedSubset X B))) ⟶
      (subspaceFunctor.op ⋙ H.cohomology q).obj (Opposite.op (subspacePair (A ∩ B))) :=
  (H.cohomology q).map (intersectionRestrictionAbsoluteMap hAX).op

/-- The vertical comparison map from the absolute cohomology of the restricted subset of `X`
coming from `A ⊆ Y` to the relative cohomology term `E^(q + 1)(Y, A)`. -/
abbrev pairCohomologyMayerVietorisAbsoluteConnectingMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A : Set Y} (hAX : A ⊆ X) :
    (H.cohomology q).obj
        (Opposite.op (absolute (TopCat.of (restrictedSubset X A)))) ⟶
      (H.cohomology (q + 1)).obj (Opposite.op (subspacePair A)) :=
  (H.cohomology q).map (restrictionAbsoluteMap hAX).op ≫
    (H.boundary q).app (Opposite.op (subspacePair A))

/-- The vertical comparison map from the absolute cohomology of the common restricted subset of
`X` to the relative cohomology term `E^(q + 1)(Y, A ∩ B)`. -/
abbrev pairCohomologyMayerVietorisIntersectionConnectingMap
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) :
    (H.cohomology q).obj
        (Opposite.op
          (pairCohomologyMayerVietorisIntersectionAbsolutePair
            (restrictedSubset X A)
            (restrictedSubset X B))) ⟶
      (H.cohomology (q + 1)).obj (Opposite.op (subspacePair (A ∩ B))) :=
  pairCohomologyMayerVietorisIntersectionRestrictionCohomologyMap H q hAX ≫
    (H.boundary q).app (Opposite.op (subspacePair (A ∩ B)))

/-- The relative Mayer-Vietoris connecting morphism `E^q(Y, A ∩ B) ⟶ E^(q + 1)(Y, X)`, formed
from the restriction `E^q(Y, A ∩ B) ⟶ E^q(X, A ∩ B)` and the triple connecting homomorphism for
`A ∩ B ⊆ X ⊆ Y`. -/
noncomputable abbrev pairCohomologyRelativeMayerVietorisBoundary
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) (q : ℤ)
    {Y : TopCat.{u}} {X A B : Set Y} :
    (H.cohomology q).obj (Opposite.op (subspacePair (A ∩ B))) ⟶
      (H.cohomology (q + 1)).obj (Opposite.op (subspacePair X)) :=
  tripleSubpairRestrictionCohomologyMap H q X (A ∩ B) ≫
    pairCohomologyTheoryTripleBoundary H q X (A ∩ B)

/-- Corollary 19.3.5 (1): the left square in the commutative diagram comparing the absolute
Mayer-Vietoris sequence on the subspace `X` with the relative Mayer-Vietoris sequence in `Y`
commutes after passing to the connecting homomorphisms of the pairs `(Y, X)`, `(Y, A)`, and
`(Y, B)`. -/
theorem pairCohomologyMayerVietorisConnectingDiagramRestriction
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    CommSq
      (pairCohomologyMayerVietorisRestrictionMap H
        (restrictedSubset X A)
        (restrictedSubset X B) q)
      ((H.boundary q).app (Opposite.op (subspacePair X)))
      (biprod.map
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hAX)
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hBX))
      (pairCohomologyRelativeMayerVietorisRestrictionMap H (q + 1) hAX hBX) := by
  sorry

/-- Corollary 19.3.5 (1) as an equality of composites. -/
theorem pairCohomologyMayerVietorisConnectingDiagramRestriction_w
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    pairCohomologyMayerVietorisRestrictionMap H
        (restrictedSubset X A)
        (restrictedSubset X B) q ≫
      biprod.map
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hAX)
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hBX) =
      (H.boundary q).app (Opposite.op (subspacePair X)) ≫
        pairCohomologyRelativeMayerVietorisRestrictionMap H (q + 1) hAX hBX :=
  (pairCohomologyMayerVietorisConnectingDiagramRestriction H q hAX hBX).w

/-- Corollary 19.3.5 (2): the middle square in the commutative diagram comparing the absolute
Mayer-Vietoris sequence on the subspace `X` with the relative Mayer-Vietoris sequence in `Y`
commutes after passing to the connecting homomorphisms of the pairs `(Y, A)`, `(Y, B)`, and
`(Y, A ∩ B)`. -/
theorem pairCohomologyMayerVietorisConnectingDiagramDifference
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    CommSq
      (biprod.map
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hAX)
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hBX))
      (pairCohomologyMayerVietorisDifferenceMap H
        (restrictedSubset X A)
        (restrictedSubset X B) q)
      (pairCohomologyRelativeMayerVietorisDifferenceMap H (q + 1) A B)
      (pairCohomologyMayerVietorisIntersectionConnectingMap H q hAX) := by
  sorry

/-- Corollary 19.3.5 (2) as an equality of composites. -/
theorem pairCohomologyMayerVietorisConnectingDiagramDifference_w
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) (hBX : B ⊆ X) :
    biprod.map
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hAX)
        (pairCohomologyMayerVietorisAbsoluteConnectingMap H q hBX) ≫
      pairCohomologyRelativeMayerVietorisDifferenceMap H (q + 1) A B =
    pairCohomologyMayerVietorisDifferenceMap H
        (restrictedSubset X A)
        (restrictedSubset X B) q ≫
      pairCohomologyMayerVietorisIntersectionConnectingMap H q hAX :=
  (pairCohomologyMayerVietorisConnectingDiagramDifference H q hAX hBX).w

/-- Corollary 19.3.5 (3): the right square in the commutative diagram comparing the absolute
Mayer-Vietoris sequence on the subspace `X` with the relative Mayer-Vietoris sequence in `Y`
commutes after composing the connecting morphisms for the pairs `(Y, A ∩ B)` and `(Y, X)`. -/
theorem pairCohomologyMayerVietorisConnectingDiagramBoundary
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) :
    CommSq
      (pairCohomologyMayerVietorisIntersectionConnectingMap H q hAX)
      (pairCohomologyMayerVietorisBoundary H
        (restrictedSubset X A)
        (restrictedSubset X B) q)
      (pairCohomologyRelativeMayerVietorisBoundary H (q + 1))
      ((H.boundary (q + 1)).app (Opposite.op (subspacePair X))) := by
  sorry

/-- Corollary 19.3.5 (3) as an equality of composites. -/
theorem pairCohomologyMayerVietorisConnectingDiagramBoundary_w
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (q : ℤ) {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) :
    pairCohomologyMayerVietorisIntersectionConnectingMap H q hAX ≫
      pairCohomologyRelativeMayerVietorisBoundary H (q + 1) =
    pairCohomologyMayerVietorisBoundary H
        (restrictedSubset X A)
        (restrictedSubset X B) q ≫
      (H.boundary (q + 1)).app (Opposite.op (subspacePair X)) :=
  (pairCohomologyMayerVietorisConnectingDiagramBoundary H q hAX).w
