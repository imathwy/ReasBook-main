import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/- Lemma 10.39.11 (Equational criterion of flatness): an `R`-module `M` is flat if and only if
every relation in `M` is trivial. In mathlib, triviality of a finite relation
`∑ i, f i • x i = 0` is the predicate `Module.IsTrivialRelation f x`, and the canonical owner
theorem for this criterion is `Module.Flat.iff_forall_isTrivialRelation`. -/
recall Module.Flat.iff_forall_isTrivialRelation

end
