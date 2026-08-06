import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Theorem_6_4_5

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X}

-- Semantic recall via `lean_leansearch`: mathlib exposes the surrounding closed-subspace API, while
-- the exact source-facing criterion already appears in this workspace as Theorem 6.4.5 (3).

/- Criterion 6.4.6. For the closed subspace `A ⊆ X`, the inclusion `A ↪ X` is a cofibration
exactly when `(X, A)` admits an NDR-pair structure. This is Theorem 6.4.5 (3), recorded here as a
recall-only block rather than as a duplicate theorem with the equivalence reversed. -/
recall isNDRPair_iff_isCofibration_subtypeVal
    {X : Type u} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
      IsNDRPair A ↔ IsCofibration.{u, u, u} (TopCat.subtypeInclusion A).hom

/-- An NDR-pair structure on `(X, A)` makes the canonical inclusion `A ↪ X` a cofibration. -/
theorem IsNDRPair.isCofibration_subtypeVal {A : Set X} (hA : IsNDRPair A) :
    IsCofibration.{u, u, u} (TopCat.subtypeInclusion A).hom :=
  (isNDRPair_iff_isCofibration_subtypeVal hA.isClosed).1 hA

/-- If the canonical inclusion `A ↪ X` is a cofibration, then `(X, A)` is an NDR-pair. -/
theorem isNDRPair_of_isCofibration_subtypeVal
    (hClosed : IsClosed A)
    (hA : IsCofibration.{u, u, u} (TopCat.subtypeInclusion A).hom) : IsNDRPair A :=
  (isNDRPair_iff_isCofibration_subtypeVal hClosed).2 hA

#check isNDRPair_iff_isCofibration_subtypeVal
