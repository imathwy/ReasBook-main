import Mathlib.RingTheory.OrzechProperty

-- Declarations for this item will be appended below by the statement pipeline.

import Mathlib.Tactic.Recall

universe u v

section

variable {R : Type u} {M : Type v} [Semiring R] [OrzechProperty R]
variable [AddCommMonoid M] [Module R M] [Module.Finite R M]

/- Lemma 10.16.4: for a commutative ring `R`, any surjective endomorphism of a finite
`R`-module is bijective. Mathlib states this canonically over any semiring satisfying
`OrzechProperty`; the Stacks-project commutative-ring case is recovered via
`CommRing.orzechProperty`. -/
recall OrzechProperty.bijective_of_surjective_endomorphism

end
