import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Lemma_19_3_2

open CategoryTheory Limits
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced sheaf-theoretic Mayer-Vietoris squares.
-- Local Chapter 14 precedent for the absolute homology sequence and Lemma 19.3.2 for the
-- cohomological excision comparison provide the source-faithful owner here.

/-- The absolute pair on the common subspace `C = A ∩ B`. -/
abbrev pairCohomologyMayerVietorisIntersectionAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  subspaceFunctor.obj (pairCohomologyMayerVietorisTargetPair A B)

/-- The absolute pair on the left summand `A`. -/
abbrev pairCohomologyMayerVietorisLeftAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairCohomologyMayerVietorisLeftPair A B)

/-- The absolute pair on the right summand `B`. -/
abbrev pairCohomologyMayerVietorisRightAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairCohomologyMayerVietorisRightPair A B)

/-- The absolute pair on the ambient space `X`. -/
abbrev pairCohomologyMayerVietorisAmbientAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairCohomologyMayerVietorisTargetPair A B)

/-- The degree-`q` restriction map `E^q(X) ⟶ E^q(A) ⊞ E^q(B)` in the cohomological
Mayer-Vietoris sequence. -/
noncomputable def pairCohomologyMayerVietorisRestrictionMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (Opposite.op (pairCohomologyMayerVietorisAmbientAbsolutePair A B)) ⟶
      (H q).obj (Opposite.op (pairCohomologyMayerVietorisLeftAbsolutePair A B)) ⊞
        (H q).obj (Opposite.op (pairCohomologyMayerVietorisRightAbsolutePair A B)) :=
  let leftAbsoluteInclusion :
      pairCohomologyMayerVietorisLeftAbsolutePair A B ⟶
        pairCohomologyMayerVietorisAmbientAbsolutePair A B :=
    ambientFunctor.map (pairCohomologyMayerVietorisLeftInclusion A B)
  let rightAbsoluteInclusion :
      pairCohomologyMayerVietorisRightAbsolutePair A B ⟶
        pairCohomologyMayerVietorisAmbientAbsolutePair A B :=
    ambientFunctor.map (pairCohomologyMayerVietorisRightInclusion A B)
  biprod.lift
    ((H q).map leftAbsoluteInclusion.op)
    ((H q).map rightAbsoluteInclusion.op)

/-- The degree-`q` difference map `E^q(A) ⊞ E^q(B) ⟶ E^q(A ∩ B)` in the cohomological
Mayer-Vietoris sequence, with the standard minus sign on the right summand. -/
noncomputable def pairCohomologyMayerVietorisDifferenceMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (Opposite.op (pairCohomologyMayerVietorisLeftAbsolutePair A B)) ⊞
        (H q).obj (Opposite.op (pairCohomologyMayerVietorisRightAbsolutePair A B)) ⟶
      (H q).obj
        (Opposite.op (pairCohomologyMayerVietorisIntersectionAbsolutePair A B)) :=
  let leftInclusion :
      pairCohomologyMayerVietorisIntersectionAbsolutePair A B ⟶
        pairCohomologyMayerVietorisLeftAbsolutePair A B :=
    { hom := TopCat.ofHom
        ⟨fun x ↦ ⟨x.1, x.2.1⟩,
          continuous_subtype_val.subtype_mk fun x ↦ x.2.1⟩
      map_subspace' := by
        intro x hx
        cases hx }
  let rightInclusion :
      pairCohomologyMayerVietorisIntersectionAbsolutePair A B ⟶
        pairCohomologyMayerVietorisRightAbsolutePair A B :=
    { hom := TopCat.ofHom
        ⟨fun x ↦ ⟨x.1, x.2.2⟩,
          continuous_subtype_val.subtype_mk fun x ↦ x.2.2⟩
      map_subspace' := by
        intro x hx
        cases hx }
  biprod.desc
    ((H q).map leftInclusion.op)
    (-((H q).map rightInclusion.op))

/-- The connecting morphism `E^q(A ∩ B) ⟶ E^(q + 1)(X)` in the cohomological Mayer-Vietoris
sequence, obtained from the long exact sequence of the pair `(X, A ∩ B)`. -/
abbrev pairCohomologyMayerVietorisBoundary
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj
        (Opposite.op (pairCohomologyMayerVietorisIntersectionAbsolutePair A B)) ⟶
      (H (q + 1)).obj
        (Opposite.op (pairCohomologyMayerVietorisAmbientAbsolutePair A B)) :=
  (H.boundary q).app (Opposite.op (pairCohomologyMayerVietorisTargetPair A B)) ≫
    (H (q + 1)).map (absoluteToRelative (pairCohomologyMayerVietorisTargetPair A B)).op

/-- The incoming morphism `E^(q - 1)(A ∩ B) ⟶ E^q(X)` at the `E^q(X)` term of the cohomological
Mayer-Vietoris sequence. -/
abbrev pairCohomologyMayerVietorisBoundaryToAmbient
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ) :
    (H (q - 1)).obj
        (Opposite.op (pairCohomologyMayerVietorisIntersectionAbsolutePair A B)) ⟶
      (H q).obj (Opposite.op (pairCohomologyMayerVietorisAmbientAbsolutePair A B)) :=
  pairCohomologyMayerVietorisBoundary H A B (q - 1) ≫
    eqToHom
      (congrArg
        (fun n ↦
          (H n).obj
            (Opposite.op (pairCohomologyMayerVietorisAmbientAbsolutePair A B)))
        (sub_add_cancel q 1))

/-- Theorem 19.3.3 (1): for an excisive triad `(X; A, B)`, the cohomological Mayer-Vietoris
sequence is exact at `E^q(X)`, i.e.
`E^(q - 1)(A ∩ B) ⟶ E^q(X) ⟶ E^q(A) ⊞ E^q(B)` is exact. -/
theorem pairCohomologyMayerVietorisExact₁
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairCohomologyMayerVietorisBoundaryToAmbient H A B q)
      (pairCohomologyMayerVietorisRestrictionMap H A B q) := sorry

/-- Theorem 19.3.3 (2): for an excisive triad `(X; A, B)`, the cohomological Mayer-Vietoris
sequence is exact at `E^q(A) ⊞ E^q(B)`, i.e.
`E^q(X) ⟶ E^q(A) ⊞ E^q(B) ⟶ E^q(A ∩ B)` is exact. -/
theorem pairCohomologyMayerVietorisExact₂
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairCohomologyMayerVietorisRestrictionMap H A B q)
      (pairCohomologyMayerVietorisDifferenceMap H A B q) := sorry

/-- Theorem 19.3.3 (3): for an excisive triad `(X; A, B)`, the cohomological Mayer-Vietoris
sequence is exact at `E^q(A ∩ B)`, i.e.
`E^q(A) ⊞ E^q(B) ⟶ E^q(A ∩ B) ⟶ E^(q + 1)(X)` is exact. -/
theorem pairCohomologyMayerVietorisExact₃
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairCohomologyMayerVietorisDifferenceMap H A B q)
      (pairCohomologyMayerVietorisBoundary H A B q) := sorry
