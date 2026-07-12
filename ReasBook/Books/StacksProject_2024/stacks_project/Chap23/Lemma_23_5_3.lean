import Mathlib.RingTheory.DividedPowers.Basic

open scoped BigOperators
open Nat Ring

namespace DividedPowers

variable {A : Type*} [CommRing A]
variable {I : Ideal A}

/-- The source-facing `p`th divided-power map on `I`, viewed as an endomorphism of the ideal and
specialized directly from the canonical divided-power operation `DividedPowers.dpow`. -/
abbrev dpowPrime (γ : DividedPowers I) (p : ℕ) [Fact p.Prime] : I → I :=
  fun x ↦ ⟨γ.dpow p x, γ.dpow_mem (Fact.out : p.Prime).ne_zero x.2⟩

/-- Coercing the ideal-valued `p`th divided power back to `A` recovers `γ_p(x)`. -/
@[simp] theorem coe_dpowPrime_apply (γ : DividedPowers I) (p : ℕ) [Fact p.Prime] (x : I) :
    (γ.dpowPrime p x : A) = γ.dpow p x :=
  rfl

/-- The correction term appearing in the source additivity formula for a candidate `p`th divided
power map. -/
noncomputable def dpowPrimeAddCorrection (p : ℕ) (x y : I) : A :=
  Finset.sum (Finset.antidiagonal p) fun ij ↦
    if 0 < ij.1 ∧ 0 < ij.2 then
      inverse (ij.1.factorial : A) * inverse (ij.2.factorial : A) *
        (x : A) ^ ij.1 * (y : A) ^ ij.2
    else
      0

end DividedPowers

namespace Function

open DividedPowers

variable {A : Type*} [CommRing A]
variable {I : Ideal A}

/-- The three source `p`th-divided-power identities for an ideal-valued map `δ : I → I`. This is
the bundled source predicate, not a typeclass intended for instance search. -/
structure IsDpowPrime (δ : I → I) (p : ℕ) : Prop where
  /-- The factorial identity in the source characterization. -/
  factorial : ∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p
  /-- Scalar compatibility in the source characterization. -/
  smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x
  /-- The source additivity formula. -/
  add : ∀ x y : I,
    (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y

/-- The defining source characterization of `Function.IsDpowPrime`. -/
theorem isDpowPrime_iff (δ : I → I) (p : ℕ) :
    δ.IsDpowPrime p ↔
      (∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p) ∧
      (∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x) ∧
        ∀ x y : I, (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y := by
  constructor
  · intro h
    exact ⟨h.factorial, h.smul, h.add⟩
  · rintro ⟨hfactorial, hsmul, hadd⟩
    exact ⟨hfactorial, hsmul, hadd⟩

end Function

namespace DividedPowers

open Function

variable {A : Type*} [CommRing A]
variable {I : Ideal A}

/-- The `p`th divided-power map of a divided power structure satisfies the source `p`th
divided-power identities under the prime-to-`p` unit hypothesis used in Lemma 23.5.3. -/
theorem isDpowPrime_dpowPrime (γ : DividedPowers I) (p : ℕ) [Fact p.Prime]
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) :
    (γ.dpowPrime p).IsDpowPrime p := sorry

end DividedPowers

namespace Ideal

open DividedPowers Function

/- Source/core/bridge triage for Lemma 23.5.3:
- `source-facing`: the uniqueness and existence statements for divided power structures in terms of
  the source `p`th divided-power map on the ideal;
- `core/canonical`: the bridge owner `DividedPowers.dpowPrime` and the source predicate
  `Function.IsDpowPrime`;
- `bridge/view`: the `Ideal`-namespace uniqueness and existence theorems below, which express the
  source Stacks statements directly in terms of those canonical Chapter 23 owners.
-/

-- Mathlib's `DividedPowers I` is the canonical owner for divided power structures; the source-facing
-- `p`th divided power on `I` itself is the ideal-valued bridge `DividedPowers.dpowPrime`, and the
-- three source identities for a candidate `p`th divided power are bundled by
-- `Function.IsDpowPrime`.

variable {A : Type*} [CommRing A]

/-- Lemma 23.5.3 (1): if every integer not divisible by `p` is invertible in `A`, then two divided
power structures on `I` are equal if and only if their ideal-valued `p`th divided power maps
agree as endomorphisms of `I`. -/
@[stacks 07GS]
theorem dividedPowers_eq_iff_dpowPrime_eq
    (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) {γ γ' : DividedPowers I} :
    γ = γ' ↔ γ.dpowPrime p = γ'.dpowPrime p := sorry

/-- Core companion to Lemma 23.5.3 (1): under the same prime-to-`p` unit hypothesis, the source
`p`th divided-power map determines a divided power structure injectively. -/
theorem injective_dpowPrime (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) :
    Function.Injective fun γ : DividedPowers I ↦ γ.dpowPrime p := by
  intro γ γ' h
  exact (dividedPowers_eq_iff_dpowPrime_eq p I hunit).2 h

/-- Pointwise reformulation of `dividedPowers_eq_iff_dpowPrime_eq`. -/
theorem dividedPowers_eq_iff_forall_dpowPrime_eq
    (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) {γ γ' : DividedPowers I} :
    γ = γ' ↔ ∀ x : I, γ.dpowPrime p x = γ'.dpowPrime p x := by
  constructor
  · intro h x
    subst h
    rfl
  · intro h
    exact (dividedPowers_eq_iff_dpowPrime_eq p I hunit).2 (funext h)

/-- Lemma 23.5.3 (2): if every integer not divisible by `p` is invertible in `A`, then any map
`δ : I → I` satisfying the three source `p`th-divided-power identities extends uniquely to a
divided power structure on `I` whose `p`th divided power is `δ`. -/
@[stacks 07GS]
theorem existsUnique_dividedPowers_of_dpowPrime
    (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (δ : I → I)
    (hfactorial : ∀ x : I, ((p ! : A) * (δ x : A)) = (x : A) ^ p)
    (hsmul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (hadd : ∀ x y : I, (δ (x + y) : A) = (δ x : A) + dpowPrimeAddCorrection p x y + δ y) :
    ∃! γ : DividedPowers I, γ.dpowPrime p = δ := sorry

/-- Core companion to Lemma 23.5.3 (2): the same unique-extension statement with the three source
identities bundled by `Function.IsDpowPrime`. -/
theorem existsUnique_dividedPowers_of_isDpowPrime
    (p : ℕ) [Fact p.Prime] (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (δ : I → I) (hδ : δ.IsDpowPrime p) :
    ∃! γ : DividedPowers I, γ.dpowPrime p = δ :=
  existsUnique_dividedPowers_of_dpowPrime p I hunit δ hδ.factorial hδ.smul hδ.add

end Ideal
