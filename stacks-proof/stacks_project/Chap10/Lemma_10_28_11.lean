import Mathlib.Tactic.Recall
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.28.11 (1): an ideal of `R` maximal among the non-principal ideals is prime. This is
the exact canonical specialization of the owner theorem `Ideal.IsOka.isPrime_of_maximal_not` to
the Oka predicate `Ideal.isOka_isPrincipal` recalled in Example 10.28.5. -/
#check Ideal.isOka_isPrincipal.isPrime_of_maximal_not

/- Lemma 10.28.11 (2): if every prime ideal of `R` is principal, then every ideal of `R` is
principal. This is the canonical theorem `IsPrincipalIdealRing.of_prime`, already stated in the
stronger generality of commutative semirings; the source phrasing follows by specializing the
resulting `IsPrincipalIdealRing R` instance to an ideal `I`. -/
recall IsPrincipalIdealRing.of_prime

/-- If every prime ideal of `R` is principal, then every ideal of `R` is principal. -/
-- Proof sketch: equip `R` with the canonical `IsPrincipalIdealRing R` instance from
-- `IsPrincipalIdealRing.of_prime hprime`, then specialize the resulting instance to `I`.
lemma ideal_isPrincipal_of_isPrime_isPrincipal
    (hprime : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) (I : Ideal R) : I.IsPrincipal := by
  -- The source proof's maximal-nonprincipal Zorn argument is already packaged in mathlib.
  letI : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_prime hprime
  -- Once `R` is a principal ideal ring, the target ideal is principal by the canonical API.
  exact IsPrincipalIdealRing.principal I

end
