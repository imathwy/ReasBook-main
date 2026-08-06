import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Lemma_14_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced sheaf-theoretic Mayer-Vietoris squares.
-- Local Chapter 14 already owns the source-facing relative pairs and inclusions
-- `(A, A ∩ B) ⟶ (X, A ∩ B)` and `(B, A ∩ B) ⟶ (X, A ∩ B)`, while Chapter 18 fixes the
-- contravariant owner `PairCohomologyTheory`. This item therefore keeps only the cohomological
-- comparison map built from those canonical pair maps.

/-- The left source pair `(A, C)` in the cohomological Mayer-Vietoris map, with
`C = A ∩ B`. -/
abbrev pairCohomologyMayerVietorisLeftPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyMayerVietorisLeftPair A B

/-- The right source pair `(B, C)` in the cohomological Mayer-Vietoris map, with
`C = A ∩ B`. -/
abbrev pairCohomologyMayerVietorisRightPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyMayerVietorisRightPair A B

/-- The target pair `(X, C)` in the cohomological Mayer-Vietoris map, with `C = A ∩ B`. -/
abbrev pairCohomologyMayerVietorisTargetPair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair :=
  pairHomologyMayerVietorisTargetPair A B

/-- The inclusion `(A, C) ⟶ (X, C)` used in the left component of the cohomological
Mayer-Vietoris map. -/
abbrev pairCohomologyMayerVietorisLeftInclusion {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    pairCohomologyMayerVietorisLeftPair A B ⟶ pairCohomologyMayerVietorisTargetPair A B :=
  pairHomologyMayerVietorisLeftInclusion A B

/-- The inclusion `(B, C) ⟶ (X, C)` used in the right component of the cohomological
Mayer-Vietoris map. -/
abbrev pairCohomologyMayerVietorisRightInclusion {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    pairCohomologyMayerVietorisRightPair A B ⟶ pairCohomologyMayerVietorisTargetPair A B :=
  pairHomologyMayerVietorisRightInclusion A B

/-- The canonical map
`E^q(X, C; π) ⟶ E^q(A, C; π) ⊞ E^q(B, C; π)` induced by the inclusions
`(A, C) ⟶ (X, C)` and `(B, C) ⟶ (X, C)`. -/
noncomputable def pairCohomologyMayerVietorisMap
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ) :
    (H q).obj (Opposite.op (pairCohomologyMayerVietorisTargetPair A B)) ⟶
      (H q).obj (Opposite.op (pairCohomologyMayerVietorisLeftPair A B)) ⊞
        (H q).obj (Opposite.op (pairCohomologyMayerVietorisRightPair A B)) :=
  biprod.lift
    ((H q).map (pairCohomologyMayerVietorisLeftInclusion A B).op)
    ((H q).map (pairCohomologyMayerVietorisRightInclusion A B).op)

/-- Lemma 19.3.2: for an excisive triad `(X; A, B)` with `C = A ∩ B`, the canonical map
`pairCohomologyMayerVietorisMap H A B q : E^q(X, C; π) ⟶ E^q(A, C; π) ⊞ E^q(B, C; π)` induced
by the inclusions `(A, C) ⟶ (X, C)` and `(B, C) ⟶ (X, C)` is an isomorphism. -/
instance pairCohomologyMayerVietoris_isIso
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso (pairCohomologyMayerVietorisMap H A B q) := sorry
