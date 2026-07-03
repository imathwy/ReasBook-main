import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

/- Lemma 10.78.5: if `R` is a local ring and `M` is a finite flat `R`-module, then `M` is free.
Together with the hypothesis `Module.Finite R M`, this is exactly the statement that `M` is finite
free, and mathlib provides it as `Module.free_of_flat_of_isLocalRing`. -/
recall Module.free_of_flat_of_isLocalRing

end
