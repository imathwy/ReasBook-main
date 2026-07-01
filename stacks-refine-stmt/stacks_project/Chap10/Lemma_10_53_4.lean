import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Lemma 10.53.4: if `R` is Artinian, then its Jacobson radical is nilpotent. The owner
declaration is the canonical mathlib theorem `IsArtinianRing.isNilpotent_jacobson_bot`; the source
wording identifies `Ideal.jacobson (⊥ : Ideal R)` with `Ring.jacobson R` via `Ideal.jacobson_bot`.
-/
recall IsArtinianRing.isNilpotent_jacobson_bot
