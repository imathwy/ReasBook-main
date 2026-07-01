import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Tactic.Recall
-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section flat_base_change

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommGroup M] [Module R M]

section

variable [Module.Flat R M]

/- Lemma 10.39.7 (Stacks tag `00HI`): if `M` is flat over `R`, then its base change to `R'` is
flat over `R'`. In mathlib the canonical base-changed module is `R' ⊗[R] M`, which is canonically
isomorphic to the textbook tensor product `M ⊗[R] R'`. This is exactly `Module.Flat.baseChange`. -/
recall Module.Flat.baseChange

end

section

variable [Module.FaithfullyFlat R M]

/- Companion recall: the faithfully flat clause of tag `00HI` is the canonical base-change
instance for `Module.FaithfullyFlat`, again on the standard mathlib model `R' ⊗[R] M` of the
textbook module `M ⊗[R] R'`. -/
recall Module.FaithfullyFlat.instTensorProduct

end

end flat_base_change
