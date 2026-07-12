import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section AtPrime

variable {A : Type u} [CommRing A]

/- Example 10.9.8: the localization of a commutative ring `A` at a prime ideal `p` is the
canonical owner construction `Localization.AtPrime`. -/
recall Localization.AtPrime

end AtPrime

section ModuleAtPrime

variable {A : Type u} [CommRing A]

/- The localization of an `A`-module `M` at the prime ideal `p` is
the canonical owner construction `LocalizedModule.AtPrime`. -/
recall LocalizedModule.AtPrime

end ModuleAtPrime

section Away

variable {A : Type u} [CommRing A]

/- The localization of `A` with respect to the multiplicative set `{1, f, f^2, ...}` is
the canonical owner construction `Localization.Away`. -/
recall Localization.Away

/- The localization of an `A`-module `M` with respect to `{1, f, f^2, ...}` is
the canonical owner construction `LocalizedModule.Away`. -/
recall LocalizedModule.Away

/-- Localization away from `f` is the zero ring exactly when `f` is nilpotent. -/
-- Proof sketch: if `f` is nilpotent, then some power of `f` vanishes, so after inverting `f`
-- the localization collapses to the zero ring. Conversely, if `Localization.Away f` is
-- subsingleton, then `0 = 1` there; clearing denominators in that equality shows that a power of
-- `f` is zero in `A`.
theorem localization_away_subsingleton_iff (f : A) :
    Subsingleton (Localization.Away f) ↔ IsNilpotent f := by
  simpa [Localization.Away, isNilpotent_iff_zero_mem_powers] using
    (IsLocalization.subsingleton_iff :
      Subsingleton (Localization (Submonoid.powers f)) ↔ 0 ∈ Submonoid.powers f)

end Away

section FractionRing

variable {A : Type u} [CommRing A]

/- The total quotient ring of `A`, i.e. the localization at all non-zero-divisors, is
the canonical owner construction `FractionRing`. -/
recall FractionRing

section

variable [IsDomain A]

/- If `A` is a domain, then its total quotient ring is its field of fractions, expressed by the
canonical `IsFractionRing` instance on `FractionRing A`. -/
#check (inferInstance : IsFractionRing A (FractionRing A))

end

end FractionRing
