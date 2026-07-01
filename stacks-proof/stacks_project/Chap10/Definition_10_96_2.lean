import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.96.2: an `R`-module `M` is `I`-adically complete if it satisfies the canonical
mathlib predicate `IsAdicComplete I M`; for `M = R`, this is the textbook notion that `R` is
`I`-adically complete as a ring. -/
recall IsAdicComplete

/- Companion recall: `AdicCompletion.of_bijective_iff` identifies `I`-adic completeness with the
statement that the canonical map `M → AdicCompletion I M`, i.e. to the inverse limit of the
quotients `M / I^n M`, is bijective. -/
recall AdicCompletion.of_bijective_iff

end
