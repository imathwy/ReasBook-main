import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.28.10 (1): an ideal of `R` that is maximal among the ideals that are not finitely
generated is prime. This is the exact canonical specialization of the owner theorem
`Ideal.IsOka.isPrime_of_maximal_not` to the Oka predicate `Ideal.FG`. -/
#check Ideal.isOka_fg.isPrime_of_maximal_not

/- Lemma 10.28.10 (2): if every prime ideal of `R` is finitely generated, then every ideal of
`R` is finitely generated. The owner theorem is `IsNoetherianRing.of_prime`; the textbook wording
for a particular ideal is then the standard consequence `Ideal.fg_of_isNoetherianRing`. -/
recall IsNoetherianRing.of_prime

end
