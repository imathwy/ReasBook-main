import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

open CategoryTheory
open HomotopicalAlgebra

universe u

-- Semantic recall via `lean_leansearch` surfaced only general weak-equivalence infrastructure,
-- not a canonical mathlib owner for this chapter-specific axiom. The local owner
-- `PairHomologyTheory` already records weak-equivalence invariance, and the target owner exports
-- the canonical instance induced by that field.

/- Axiom 13.1.6. A weak equivalence of pairs induces an isomorphism on homology, recorded here by
the canonical instance `PairHomologyTheory.map_isIso_of_weakEquivalence`. -/
#check PairHomologyTheory.map_isIso_of_weakEquivalence

namespace PairHomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- The source-facing weak-equivalence predicate on `SpacePair` maps induces the same homology
isomorphism as the canonical `WeakEquivalence` instance API. -/
theorem map_isIso_of_isWeakEquivalence
    (H : PairHomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q)
    (hf : SpacePair.IsWeakEquivalence f) :
    IsIso ((H q).map f) := by
  let _ : WeakEquivalence f := (spacePair_weakEquivalence_iff f).2 hf
  infer_instance

end PairHomologyTheory
