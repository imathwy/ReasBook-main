import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_64_1 (from Chap10) -/
universe u

namespace Ideal

section

open Localization Localization.AtPrime

variable {R : Type u} [CommRing R]
variable (𝔭 : Ideal R) [𝔭.IsPrime]

/-
Domain triage: this file is in commutative algebra of prime ideals and localization. The
source-facing declaration is the symbolic power itself, so `Ideal.symbolicPower` stays primitive.
Its derived API should come from the owner abstraction given by the canonical map
`R → Localization.AtPrime 𝔭` and the maximal ideal of that local ring, rather than from a parallel
local wrapper layer.
-/

/-- Definition 10.64.1: for a prime ideal `𝔭` of `R`, the `n`th symbolic power `𝔭^(n)` is the
contraction of the `n`th power of the extended prime ideal in `R_𝔭`. -/
local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "toRₚ" => algebraMap R Rₚ
local notation "𝔭ₚ" => map (algebraMap R Rₚ) 𝔭

def symbolicPower (n : ℕ) : Ideal R :=
  comap toRₚ (𝔭ₚ ^ n)

/-- Definition 10.64.1 in Stacks-project form: for a prime ideal `𝔭` of `R`, the `n`th symbolic
power `𝔭^(n)` is the kernel of the canonical map `R → R_𝔭 / 𝔭^n R_𝔭`. -/
theorem symbolicPower_eq_ker_quotient_map_pow (n : ℕ) :
    symbolicPower 𝔭 n =
      RingHom.ker ((Ideal.Quotient.mk (𝔭ₚ ^ n)).comp toRₚ) := by
  rw [symbolicPower, RingHom.ker_eq_comap_bot, ← comap_comap, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

/-- Positive symbolic powers of a prime ideal are primary. -/
theorem symbolicPower_isPrimary {n : ℕ} (hn : 0 < n) :
    (symbolicPower 𝔭 n).IsPrimary := by
  have hmax : ((𝔭ₚ ^ n).radical).IsMaximal := by
    rw [radical_pow 𝔭ₚ (Nat.ne_of_gt hn), map_eq_maximalIdeal,
      (Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal Rₚ)).radical]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  simpa [symbolicPower] using (isPrimary_of_isMaximal_radical hmax).comap toRₚ

/-- The radical of a positive symbolic power of a prime ideal is the prime ideal itself. -/
theorem radical_symbolicPower {n : ℕ} (hn : 0 < n) :
    radical (symbolicPower 𝔭 n) = 𝔭 := by
  change radical (comap toRₚ (𝔭ₚ ^ n)) = 𝔭
  rw [← comap_radical, radical_pow 𝔭ₚ (Nat.ne_of_gt hn),
    map_eq_maximalIdeal,
    (Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal Rₚ)).radical,
    comap_maximalIdeal]

end

end Ideal

/-! ### Lemma_10_64_2 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 10.64.2: for a prime ideal `𝔭` of a Noetherian ring `R` and `n > 0`, the associated
primes of `R ⧸ 𝔭^(n)` are exactly `{𝔭}`, where `𝔭^(n)` is the symbolic power from
Definition `10.64.1`. -/
-- Proof sketch: `symbolicPower 𝔭 n` is a `𝔭`-primary ideal for `n > 0`, so
-- `associatedPrimes.eq_singleton_of_isPrimary` identifies the associated primes of the quotient by
-- this ideal with the singleton consisting of its radical, which is `𝔭`.
theorem associatedPrimes_quotient_symbolicPower_eq_singleton (𝔭 : Ideal R) [𝔭.IsPrime] {n : ℕ}
    (hn : 0 < n) :
    associatedPrimes R (R ⧸ 𝔭.symbolicPower n) = {𝔭} := by
  simpa [Ideal.radical_symbolicPower 𝔭 hn] using
    associatedPrimes.eq_singleton_of_isPrimary (Ideal.symbolicPower_isPrimary 𝔭 hn)

end
