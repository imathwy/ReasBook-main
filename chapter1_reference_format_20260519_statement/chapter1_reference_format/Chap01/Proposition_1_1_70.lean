import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace Int

/-- Proposition 1.1.70: if a prime number `p` divides the product `∏ i, a i` of finitely many
integers, then it divides one of the factors. -/
-- Proof sketch: regard `(p : ℤ)` as a prime element via `Nat.prime_iff_prime_int`, then apply
-- `Prime.dvd_finset_prod_iff` to `Finset.univ` and the family `a`.
theorem exists_dvd_of_prime_dvd_prod {ι : Type*} [Fintype ι] {p : ℕ} {a : ι → ℤ}
    (hp : Nat.Prime p) (hprod : (p : ℤ) ∣ ∏ i, a i) :
    ∃ i, (p : ℤ) ∣ a i := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases (hp'.dvd_finset_prod_iff a).mp hprod with ⟨i, -, hi⟩
  exact ⟨i, hi⟩

end Int
