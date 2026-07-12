import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/- Domain triage:
* primary domain: integral and finite-dimensional commutative `k`-algebras over a field;
* core/canonical owners: `fieldOfFiniteDimensional`, `isField_of_isIntegral_of_isField'`, and
  `Ideal.Quotient.maximal_of_isField`;
* layer split: parts (1) and (2) are direct owner recalls, while part (3) is the source-facing
  bridge from prime ideals to the owner quotient-field criterion.
-/

/- A domain that is finite-dimensional as a `k`-algebra over a field `k` is a field. This is
exactly the owner declaration `fieldOfFiniteDimensional`, which supplies the field structure
itself. -/
recall fieldOfFiniteDimensional

/- A domain that is integral as a `k`-algebra over a field `k` is a field. This is exactly the
canonical theorem `isField_of_isIntegral_of_isField'`, specialized to the field `k`. -/
recall isField_of_isIntegral_of_isField'

-- Proof sketch: for a prime ideal `P`, the quotient `S ⧸ P` is a domain and remains integral over
-- `k`; apply part (2) to conclude that `S ⧸ P` is a field, which is equivalent to `P` being
-- maximal.
/-- Lemma 10.36.19: if a `k`-algebra `S` is integral over the field `k`, then every prime ideal of
`S` is maximal. -/
@[stacks 00GS]
theorem ideal_isMaximal_of_isPrime_of_integral_over_field
    [Algebra.IsIntegral k S] (P : Ideal S) (hP : P.IsPrime) : P.IsMaximal := by
  letI : P.IsPrime := hP
  exact Ideal.Quotient.maximal_of_isField P <|
    isField_of_isIntegral_of_isField' (Field.toIsField k)

end
