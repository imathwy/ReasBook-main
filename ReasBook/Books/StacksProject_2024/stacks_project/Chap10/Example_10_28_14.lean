import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open TopologicalSpace

variable {R : Type u} [CommRing R]

namespace Ideal

/-- An ideal has finitely generated radical if its radical is the radical of a finitely generated
ideal. -/
def HasFinitelyGeneratedRadical (I : Ideal R) : Prop :=
  ∃ J : Ideal R, J.FG ∧ I.radical = J.radical

/-- For a prime ideal, having finitely generated radical means being the radical of a finitely
generated ideal. -/
theorem hasFinitelyGeneratedRadical_iff_eq_radical {P : Ideal R} (hP : P.IsPrime) :
    P.HasFinitelyGeneratedRadical ↔ ∃ J : Ideal R, J.FG ∧ P = J.radical := by
  simp [HasFinitelyGeneratedRadical, hP.radical]

/-- The ideals whose radicals are radicals of finitely generated ideals form an Oka family. -/
-- Proof sketch: the unit ideal is trivially in the family. For the Oka step, combine finite
-- generation data for `I ⊔ Ideal.span {a}` and `I.colon (Ideal.span {a})` with the identity
-- `I.radical = ((I ⊔ Ideal.span ({a} : Set R)) * I.colon (Ideal.span ({a} : Set R))).radical`.
theorem isOka_hasFinitelyGeneratedRadical :
    IsOka (fun I : Ideal R ↦ I.HasFinitelyGeneratedRadical) := sorry

end Ideal

/-- Example 10.28.14: the prime spectrum `Spec(R)` is Noetherian if and only if every prime ideal
of `R` is the radical of a finitely generated ideal. -/
-- Proof sketch: apply the Oka-family maximal-ideal argument to the predicate
-- `Ideal.HasFinitelyGeneratedRadical`. For a prime ideal, this predicate is exactly the statement
-- that the prime is the radical of a finitely generated ideal.
theorem primeSpectrum_noetherianSpace_iff_every_prime_hasFinitelyGeneratedRadical :
    NoetherianSpace (PrimeSpectrum R) ↔
      ∀ P : Ideal R, P.IsPrime → ∃ J : Ideal R, J.FG ∧ P = J.radical := sorry

/-- Bridge reformulation of Example 10.28.14: `Spec(R)` is Noetherian if and only if every ideal of
`R` has radical equal to the radical of a finitely generated ideal. Since this predicate depends
only on the radical, it is equivalent to the radical-ideal wording in the source text. -/
-- Proof sketch: combine the prime-ideal criterion with the Oka-family theorem
-- `Ideal.isOka_hasFinitelyGeneratedRadical`, and use
-- `Ideal.hasFinitelyGeneratedRadical_iff_eq_radical` on prime ideals.
theorem primeSpectrum_noetherianSpace_iff_every_ideal_hasFinitelyGeneratedRadical :
    NoetherianSpace (PrimeSpectrum R) ↔ ∀ I : Ideal R, I.HasFinitelyGeneratedRadical := sorry

end
