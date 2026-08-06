import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Axiom_13_1_4

open CategoryTheory
open CategoryTheory.Limits
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` surfaced only sheaf-theoretic Mayer-Vietoris owners in
-- the current environment. Local Chapter 13 precedent already fixes the relative-pair homology
-- owner `PairHomologyTheory`, the excisive-triad hypothesis `Triad.IsExcisive`, and the target
-- pair owner `pairHomologyExcisionTargetPair`. This item therefore stays source-facing as the
-- explicit biproduct map induced by the two inclusions `(A, A ∩ B) ⟶ (X, A ∩ B)` and
-- `(B, A ∩ B) ⟶ (X, A ∩ B)`.

/-- The left source pair `(A, C)` in the Mayer-Vietoris map, with `C = A ∩ B`. -/
abbrev pairHomologyMayerVietorisLeftPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyExcisionSourcePair A B

/-- The right source pair `(B, C)` in the Mayer-Vietoris map, with `C = A ∩ B`. -/
abbrev pairHomologyMayerVietorisRightPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyExcisionSourcePair B A

/-- The target pair `(X, A ∩ B)` in the Mayer-Vietoris map. -/
abbrev pairHomologyMayerVietorisTargetPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyExcisionTargetPair (A ∩ B)

/-- The inclusion `(A, C) ⟶ (X, C)` used in the left summand of the Mayer-Vietoris map. -/
def pairHomologyMayerVietorisLeftInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyMayerVietorisLeftPair A B ⟶ pairHomologyMayerVietorisTargetPair A B :=
  { hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    map_subspace' := by
      intro a ha
      exact ⟨a.2, ha⟩ }

/-- The inclusion `(B, C) ⟶ (X, C)` used in the right summand of the Mayer-Vietoris map. -/
def pairHomologyMayerVietorisRightInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyMayerVietorisRightPair A B ⟶ pairHomologyMayerVietorisTargetPair A B :=
  { hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    map_subspace' := by
      intro b hb
      exact ⟨hb, b.2⟩ }

/-- The canonical direct-sum map
`E_q(A, A ∩ B) ⊞ E_q(B, A ∩ B) ⟶ E_q(X, A ∩ B)` induced by the two pair inclusions. -/
noncomputable def pairHomologyMayerVietorisMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (pairHomologyMayerVietorisLeftPair A B) ⊞
        (H q).obj (pairHomologyMayerVietorisRightPair A B) ⟶
      (H q).obj (pairHomologyMayerVietorisTargetPair A B) :=
  biprod.desc
    ((H q).map (pairHomologyMayerVietorisLeftInclusion A B))
    ((H q).map (pairHomologyMayerVietorisRightInclusion A B))

/-- Lemma 14.5.2: for an excisive triad `(X; A, B)` with `C = A ∩ B`, the canonical map
`pairHomologyMayerVietorisMap H A B q : E_q(A, C) ⊞ E_q(B, C) ⟶ E_q(X, C)` induced by the
inclusions `(A, C) ⟶ (X, C)` and `(B, C) ⟶ (X, C)` is an isomorphism. -/
instance pairHomologyMayerVietoris
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso (pairHomologyMayerVietorisMap H A B q) := sorry

/-- Lemma 14.5.2 in callable form: for an excisive triad `(X; A, B)`, the canonical Mayer-Vietoris
comparison `E_q(A, A ∩ B) ⊞ E_q(B, A ∩ B) ⟶ E_q(X, A ∩ B)` is an isomorphism. -/
theorem pairHomologyMayerVietoris_isIso
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso (pairHomologyMayerVietorisMap H A B q) := by
  exact pairHomologyMayerVietoris H A B q hExcisive
