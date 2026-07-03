import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.WellKnown

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators PowerSeries
open PowerSeries

noncomputable section

-- Proof sketch: write `p = d + 1`, identify the summand with `Nat.multichoose (d + 1) m`,
-- and apply the canonical owner theorem `Nat.sum_range_multichoose`.
/-- Exercise 2 (1): the finite sum appearing in part (a) is the hockey-stick identity for the
binomial coefficients `((p - 1 + m).choose m)`. -/
theorem geometric_power_series_partial_sum_choose
    (p n : ℕ) (hp : 0 < p) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (p - 1 + m) m = Nat.choose (p + n) n := by
  rcases Nat.exists_eq_succ_of_ne_zero hp.ne' with ⟨d, rfl⟩
  calc
    ∑ m ∈ Finset.range (n + 1), Nat.choose (d + m) m
        = ∑ m ∈ Finset.range (n + 1), (d + 1).multichoose m := by
            simp [Nat.multichoose_eq, Nat.add_left_comm, Nat.add_comm]
    _ = Nat.choose (n + (d + 1)) (d + 1) := Nat.sum_range_multichoose n (d + 1)
    _ = Nat.choose ((d + 1) + n) n := by
      simpa [Nat.add_comm] using
        (Nat.choose_symm_add : Nat.choose ((d + 1) + n) (d + 1) = Nat.choose ((d + 1) + n) n)
    _ = Nat.choose (d.succ + n) n := rfl

-- Proof sketch: write `p = d + 1`, apply `mk_one_pow_eq_mk_choose_add`, and rewrite the
-- coefficient formula into the textbook `((p - 1 + n).choose n)` form.
/-- Exercise 2 (2): over any commutative ring, for `p ≥ 1`, the formal power series
`S_p(X) = (1 + X + X^2 + ⋯)^p` has coefficients `((p - 1 + n).choose n)`. -/
theorem geometric_power_series_pow_eq_mk_choose
    (S : Type*) [CommRing S] (p : ℕ) (hp : 0 < p) :
    (mk 1 : S⟦X⟧) ^ p = mk (fun n ↦ (Nat.choose (p - 1 + n) n : S)) := by
  rcases Nat.exists_eq_succ_of_ne_zero hp.ne' with ⟨d, rfl⟩
  calc
    (mk 1 : S⟦X⟧) ^ (d + 1) = mk (fun n ↦ (Nat.choose (d + n) d : S)) := by
      simpa using mk_one_pow_eq_mk_choose_add S d
    _ = mk (fun n ↦ (Nat.choose (d + n) n : S)) := by
      ext n
      simp only [coeff_mk]
      simpa using
        congrArg (fun m : ℕ ↦ (m : S))
          (Nat.choose_symm_add : Nat.choose (d + n) d = Nat.choose (d + n) n)

-- Proof sketch: compare the coefficient of degree `n` in
-- `(PowerSeries.mk 1 : ℤ⟦X⟧) ^ p * (PowerSeries.mk 1 : ℤ⟦X⟧) ^ q =
--   (PowerSeries.mk 1 : ℤ⟦X⟧) ^ (p + q)`,
-- then use `PowerSeries.coeff_mul` together with the expansion from
-- `geometric_power_series_pow_eq_mk_choose`.
/-- Exercise 2 (3): comparing coefficients in `S_p(X) S_q(X) = S_{p+q}(X)` gives the
Vandermonde-type convolution identity for the coefficients of the powers of the geometric series. -/
theorem geometric_power_series_pow_vandermonde
    (p q n : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ∑ l ∈ Finset.range (n + 1),
      Nat.choose (p - 1 + l) l * Nat.choose (q - 1 + (n - l)) (n - l) =
        Nat.choose (p + q - 1 + n) n := by
  rcases Nat.exists_eq_succ_of_ne_zero hp.ne' with ⟨d, rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero hq.ne' with ⟨e, rfl⟩
  have hd :
      (mk 1 : ℤ⟦X⟧) ^ (d + 1) = mk (fun k ↦ (Nat.choose (d + k) k : ℤ)) := by
    simpa [Nat.add_assoc] using
      (geometric_power_series_pow_eq_mk_choose ℤ (d + 1) (Nat.succ_pos _))
  have he :
      (mk 1 : ℤ⟦X⟧) ^ (e + 1) = mk (fun k ↦ (Nat.choose (e + k) k : ℤ)) := by
    simpa [Nat.add_assoc] using
      (geometric_power_series_pow_eq_mk_choose ℤ (e + 1) (Nat.succ_pos _))
  have hde :
      (mk 1 : ℤ⟦X⟧) ^ (d + e + 2) = mk (fun k ↦ (Nat.choose (d + e + 1 + k) k : ℤ)) := by
    simpa [Nat.add_assoc] using
      (geometric_power_series_pow_eq_mk_choose ℤ (d + e + 2) (Nat.succ_pos _))
  have hseries :
      (mk (fun k ↦ (Nat.choose (d + k) k : ℤ)) : ℤ⟦X⟧) *
          mk (fun k ↦ (Nat.choose (e + k) k : ℤ)) =
        mk (fun k ↦ (Nat.choose (d + e + 1 + k) k : ℤ)) := by
    calc
      (mk (fun k ↦ (Nat.choose (d + k) k : ℤ)) : ℤ⟦X⟧) *
          mk (fun k ↦ (Nat.choose (e + k) k : ℤ))
          = (mk 1 : ℤ⟦X⟧) ^ (d + 1) * (mk 1 : ℤ⟦X⟧) ^ (e + 1) := by
            rw [← hd, ← he]
      _ = (mk 1 : ℤ⟦X⟧) ^ ((d + 1) + (e + 1)) := by rw [← pow_add]
      _ = (mk 1 : ℤ⟦X⟧) ^ (d + e + 2) := by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = mk (fun k ↦ (Nat.choose (d + e + 1 + k) k : ℤ)) := hde
  have hcoeff := congrArg (coeff n) hseries
  rw [coeff_mul] at hcoeff
  have hsum :
      ∑ p ∈ Finset.antidiagonal n,
        coeff p.1 (mk (fun k ↦ (Nat.choose (d + k) k : ℤ))) *
          coeff p.2 (mk (fun k ↦ (Nat.choose (e + k) k : ℤ))) =
        ∑ l ∈ Finset.range (n + 1),
          coeff l (mk (fun k ↦ (Nat.choose (d + k) k : ℤ))) *
            coeff (n - l) (mk (fun k ↦ (Nat.choose (e + k) k : ℤ))) := by
    simpa using
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun l r ↦
          coeff l (mk (fun k ↦ (Nat.choose (d + k) k : ℤ))) *
            coeff r (mk (fun k ↦ (Nat.choose (e + k) k : ℤ))))
        n)
  rw [hsum] at hcoeff
  simp only [coeff_mk] at hcoeff
  apply Int.ofNat_injective
  simpa [Nat.succ_sub_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcoeff
