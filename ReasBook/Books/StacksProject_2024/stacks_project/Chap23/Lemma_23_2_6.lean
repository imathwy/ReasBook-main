import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import StacksProject_2024.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Ideal

open Ideal.Quotient (eq_zero_iff_mem)

/-
Source/core/bridge triage:
- `source-facing`: Lemma 23.2.6 about a divided power ideal `I` and the nilpotence of `p` modulo `I`;
- `core/canonical`: the mathlib owner `DividedPowers I` together with the Chapter 10 owner
  `Ideal.IsLocallyNilpotent`;
- `bridge/view`: `Ideal.isNilpotent_natCast_of_isLocallyNilpotent_quotient` is the ideal-only
  forward direction, while
  `DividedPowers.isLocallyNilpotent_of_isNilpotent_natCast` is the divided-powers reverse
  direction.
-/

section

variable {p : ℕ}
variable {A : Type u} [CommRing A]

/-- Lemma 23.2.6 companion, forward direction: under the nilpotence hypothesis on the class of
`p` in `A ⧸ I`, local nilpotence of `I` forces `(p : A)` to be nilpotent. -/
@[stacks 07GR]
theorem isNilpotent_natCast_of_isLocallyNilpotent_quotient
    (I : Ideal A) (hp : IsNilpotent (p : A ⧸ I))
    (hI : I.IsLocallyNilpotent) :
    IsNilpotent (p : A) := by
  rcases hp with ⟨n, hn⟩
  exact IsNilpotent.of_pow <|
    (isLocallyNilpotent_iff I).mp hI ((p : A) ^ n) <|
      eq_zero_iff_mem.mp (by simpa using hn)

end

end Ideal

namespace DividedPowers

section

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A]

/-- Lemma 23.2.6 companion, reverse direction: a divided power structure on `I` and nilpotence of
`(p : A)` already force `I` to be locally nilpotent, so the quotient nilpotence hypothesis in
`A ⧸ I` is unnecessary in this direction. -/
@[stacks 07GR]
theorem isLocallyNilpotent_of_isNilpotent_natCast
    {I : Ideal A} (γ : DividedPowers I) (hpA : IsNilpotent (p : A)) :
    I.IsLocallyNilpotent := by
  rw [Ideal.isLocallyNilpotent_iff]
  intro x hx
  rcases hpA with ⟨n, hn⟩
  refine ⟨p ^ n, γ.nilpotent_of_mem_dpIdeal ?_ ?_ hx⟩
  · exact pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : p.Prime))
  · intro y hy
    simpa [nsmul_eq_mul, Nat.cast_pow, hn]

/-- Lemma 23.2.6: let `p` be a prime number, let `A` be a ring, let `I` be an ideal of `A`, and
let `γ` be a divided power structure on `I`. If the class of `p` in the quotient `A ⧸ I` is
nilpotent, then `I` is locally nilpotent if and only if `(p : A)` is nilpotent. -/
@[stacks 07GR]
theorem isLocallyNilpotent_iff_isNilpotent_natCast
    {I : Ideal A} (γ : DividedPowers I) (hp : IsNilpotent (p : A ⧸ I)) :
    I.IsLocallyNilpotent ↔ IsNilpotent (p : A) := by
  constructor
  · exact Ideal.isNilpotent_natCast_of_isLocallyNilpotent_quotient I hp
  · exact γ.isLocallyNilpotent_of_isNilpotent_natCast

end

end DividedPowers
