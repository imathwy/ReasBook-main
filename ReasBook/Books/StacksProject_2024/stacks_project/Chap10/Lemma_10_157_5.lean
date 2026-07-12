import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Definition_10_110_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
* primary domain: regular and normal Noetherian commutative rings;
* sampled owner declarations:
  `IsRegularRing`,
  `IsNormalRing`,
  `IsRegularRing.isRegularLocalRing_atPrime`,
  `IsNormalRing.isNormalLocalizationAtPrime`;
* best owner abstraction: the source-facing hypothesis is the chapter owner `IsRegularRing R`, and
  the conclusion should be the chapter owner `IsNormalRing R`;
* primitive data vs derived API: the primitive public input is only `[IsRegularRing R]`; the old
  primewise pair of `IsDomain` and `IsIntegrallyClosed` instances is derived local API already
  packaged by `IsNormalRing`.

Layering:
* `source-facing`: the textbook statement that a regular ring is normal;
* `core/canonical`: the owner predicates `IsRegularRing R` and `IsNormalRing R`;
* `bridge/view`: the prime-local domain and integrally-closed consequences recovered from
  `IsNormalRing.isNormalLocalizationAtPrime`.
-/

-- Proof sketch: a regular ring satisfies the primewise regular-local hypothesis built into
-- `IsRegularRing`; Serre's criterion from Lemma `10.157.4` then yields that the ring is normal.
/-- Lemma 10.157.5: a regular ring is normal. -/
theorem isNormalRing_of_isRegularRing [IsRegularRing R] : IsNormalRing R := by
  sorry

end
