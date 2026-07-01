import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Lemma 10.31.10 (Stacks tag `06RN`): any surjective endomorphism of a Noetherian ring is an
isomorphism. Mathlib organizes this under the owner theorem
`OrzechProperty.bijective_of_surjective_endomorphism`; the commutative Noetherian ring case is
recovered from `IsNoetherianRing.orzechProperty`, viewing a ring endomorphism `f : R →+* R` as the
linear endomorphism `f.toLinearMap` of the finite `R`-module `R`. -/
recall OrzechProperty.bijective_of_surjective_endomorphism

end
