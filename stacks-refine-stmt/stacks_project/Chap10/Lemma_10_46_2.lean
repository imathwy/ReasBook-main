import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']

/-- The positive-characteristic prime-field algebraic branch appearing in Lemma `10.46.2`. This
depends only on the target field, not on an auxiliary presentation as an extension. -/
def PrimeFieldAlgebraic (K : Type*) [Field K] :
    Prop :=
  ∃ p : ℕ, ∃ (_ : Fact p.Prime) (_ : CharP K p),
    let _ : Algebra (ZMod p) K := ZMod.algebra K p
    Algebra.IsAlgebraic (ZMod p) K

/-- Core/canonical bridge for Lemma 10.46.2: package the textbook power-in-the-image criterion
around the owner predicate `IsPurelyInseparable k k'`, leaving only the prime-field algebraic
exception as a separate branch. -/
private theorem exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic :
    (∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) ↔
      IsPurelyInseparable k k' ∨ PrimeFieldAlgebraic k' :=
  sorry

/-- Lemma 10.46.2: for a field extension `k'/k`, every element of `k'` has a positive power in
the image of `k` if and only if the extension is trivial, or `k` has positive characteristic and
`k'/k` is purely inseparable, or `k'` is algebraic over a prime field `ZMod p`. -/
-- Proof sketch: the owner-form theorem
-- `exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic` already isolates the
-- canonical purely inseparable branch.  In characteristic zero, a purely inseparable extension of
-- fields is separable over a perfect base, hence trivial; in positive characteristic, this yields
-- exactly the textbook split.
theorem exists_pos_pow_mem_base_iff_surjective_or_positiveCharacteristic_cases :
    (∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) ↔
      Function.Surjective (algebraMap k k') ∨
        (ringChar k ≠ 0 ∧ IsPurelyInseparable k k') ∨ PrimeFieldAlgebraic k' := by
  rw [exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic]
  constructor
  · rintro (hpi | hp)
    · by_cases h0 : ringChar k = 0
      · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
        letI : PerfectField k := PerfectField.ofCharZero
        letI : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
        letI : Algebra.IsSeparable k k' := Algebra.IsAlgebraic.isSeparable_of_perfectField
        exact .inl (IsPurelyInseparable.surjective_algebraMap_of_isSeparable k k')
      · exact .inr <| .inl ⟨h0, hpi⟩
    · exact .inr <| .inr hp
  · rintro (hsurj | hpi | hp)
    · let e : k ≃ₐ[k] k' :=
        AlgEquiv.ofBijective (Algebra.ofId k k')
          ⟨FaithfulSMul.algebraMap_injective k k', hsurj⟩
      exact .inl e.isPurelyInseparable
    · exact .inl hpi.2
    · exact .inr hp

end
