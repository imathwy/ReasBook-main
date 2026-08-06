import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Lemma_14_5_2

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only generic long-exact-sequence owners in
-- mathlib. Local Chapter 13 precedent fixes the source-facing owner `PairHomologyTheory`, while
-- Lemma 14.5.2 supplies the excisive-triad direct-sum comparison for the relative term
-- `E_q(X, A ∩ B)`.

/-- The absolute pair on the common subspace `C = A ∩ B`. -/
abbrev pairHomologyMayerVietorisIntersectionAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  subspaceFunctor.obj (pairHomologyMayerVietorisTargetPair A B)

/-- The absolute pair on the left summand `A`. -/
abbrev pairHomologyMayerVietorisLeftAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairHomologyMayerVietorisLeftPair A B)

/-- The absolute pair on the right summand `B`. -/
abbrev pairHomologyMayerVietorisRightAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairHomologyMayerVietorisRightPair A B)

/-- The absolute pair on the ambient space `X`. -/
abbrev pairHomologyMayerVietorisAmbientAbsolutePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) : SpacePair :=
  ambientFunctor.obj (pairHomologyMayerVietorisTargetPair A B)

/-- The degree-`q` Mayer-Vietoris map `E_q(A ∩ B) ⟶ E_q(A) ⊞ E_q(B)`, with the standard sign on
the right summand. -/
noncomputable def pairHomologyMayerVietorisIntersectionMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (pairHomologyMayerVietorisIntersectionAbsolutePair A B) ⟶
      (H q).obj (pairHomologyMayerVietorisLeftAbsolutePair A B) ⊞
        (H q).obj (pairHomologyMayerVietorisRightAbsolutePair A B) :=
  let leftInclusion :
      pairHomologyMayerVietorisIntersectionAbsolutePair A B ⟶
        pairHomologyMayerVietorisLeftAbsolutePair A B :=
    { hom := TopCat.ofHom
        ⟨fun x ↦ ⟨x.1, x.2.1⟩,
          continuous_subtype_val.subtype_mk fun x ↦ x.2.1⟩
      map_subspace' := by
        intro x hx
        cases hx }
  let rightInclusion :
      pairHomologyMayerVietorisIntersectionAbsolutePair A B ⟶
        pairHomologyMayerVietorisRightAbsolutePair A B :=
    { hom := TopCat.ofHom
        ⟨fun x ↦ ⟨x.1, x.2.2⟩,
          continuous_subtype_val.subtype_mk fun x ↦ x.2.2⟩
      map_subspace' := by
        intro x hx
        cases hx }
  biprod.lift
    ((H q).map leftInclusion)
    (-((H q).map rightInclusion))

/-- The degree-`q` Mayer-Vietoris map `E_q(A) ⊞ E_q(B) ⟶ E_q(X)` induced by the two absolute
inclusions into `X`. -/
noncomputable def pairHomologyMayerVietorisSumMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (pairHomologyMayerVietorisLeftAbsolutePair A B) ⊞
        (H q).obj (pairHomologyMayerVietorisRightAbsolutePair A B) ⟶
      (H q).obj (pairHomologyMayerVietorisAmbientAbsolutePair A B) :=
  let leftInclusion :
      pairHomologyMayerVietorisLeftAbsolutePair A B ⟶
        pairHomologyMayerVietorisAmbientAbsolutePair A B :=
    ambientFunctor.map (pairHomologyMayerVietorisLeftInclusion A B)
  let rightInclusion :
      pairHomologyMayerVietorisRightAbsolutePair A B ⟶
        pairHomologyMayerVietorisAmbientAbsolutePair A B :=
    ambientFunctor.map (pairHomologyMayerVietorisRightInclusion A B)
  biprod.desc
    ((H q).map leftInclusion)
    ((H q).map rightInclusion)

/-- The Mayer-Vietoris connecting morphism `E_q(X) ⟶ E_(q - 1)(A ∩ B)` obtained from the long
exact sequence of the pair `(X, A ∩ B)`. -/
abbrev pairHomologyMayerVietorisBoundary
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (pairHomologyMayerVietorisAmbientAbsolutePair A B) ⟶
      (H (q - 1)).obj (pairHomologyMayerVietorisIntersectionAbsolutePair A B) :=
  ((H q).map (absoluteToRelative (pairHomologyMayerVietorisTargetPair A B))) ≫
    (H.boundary q).app (pairHomologyMayerVietorisTargetPair A B)

/-- Theorem 14.5.3 (1): for an excisive triad `(X; A, B)`, the Mayer-Vietoris sequence is exact
at `E_q(A) ⊞ E_q(B)`, i.e. `E_q(A ∩ B) ⟶ E_q(A) ⊞ E_q(B) ⟶ E_q(X)` is exact. -/
theorem pairHomologyMayerVietorisExact₁
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairHomologyMayerVietorisIntersectionMap H A B q)
      (pairHomologyMayerVietorisSumMap H A B q) := sorry

/-- Theorem 14.5.3 (2): for an excisive triad `(X; A, B)`, the Mayer-Vietoris sequence is exact
at `E_q(X)`, i.e. `E_q(A) ⊞ E_q(B) ⟶ E_q(X) ⟶ E_(q - 1)(A ∩ B)` is exact. -/
theorem pairHomologyMayerVietorisExact₂
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairHomologyMayerVietorisSumMap H A B q)
      (pairHomologyMayerVietorisBoundary H A B q) := sorry

/-- Theorem 14.5.3 (3): for an excisive triad `(X; A, B)`, the Mayer-Vietoris sequence is exact
at `E_(q - 1)(A ∩ B)`, i.e.
`E_q(X) ⟶ E_(q - 1)(A ∩ B) ⟶ E_(q - 1)(A) ⊞ E_(q - 1)(B)` is exact. -/
theorem pairHomologyMayerVietorisExact₃
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    Function.Exact
      (pairHomologyMayerVietorisBoundary H A B q)
      (pairHomologyMayerVietorisIntersectionMap H A B (q - 1)) := sorry
