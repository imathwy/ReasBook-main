import Mathlib.RingTheory.Ideal.Pure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.108.3: if `I, J ⊆ R` are pure ideals and `V(I) = V(J)` in `Spec(R)`, then `I = J`.
This is exactly the canonical theorem `Ideal.zeroLocus_inj_of_pure`. -/
recall Ideal.zeroLocus_inj_of_pure

end
