import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

-- This item is source-facing, but its primitive data is just a prime `p` with four properties.
-- The canonical owner surface is therefore the direct existential over `Nat.Prime`, not a local
-- wrapper class for a conjunction of those properties.

/-- Helper for Lemma PI-13: the sequence `A * B^q / (q - 1)!` is eventually less than `1`. -/
lemma exists_eventual_factorial_bound (A B : ℝ) :
    ∃ N1 : ℕ, ∀ q ≥ N1, A * B ^ q / ((q - 1)! : ℝ) < 1 := by
  -- Extract the eventual bound from the standard limit `A * B^q / (q - 1)! → 0`.
  have hEventually :
      ∀ᶠ q : ℕ in Filter.atTop, A * B ^ q / ((q - 1)! : ℝ) < 1 :=
    (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop A B 1).eventually_lt_const zero_lt_one
  -- Convert the eventual statement on `atTop` into a concrete threshold.
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hEventually
  exact ⟨N1, fun q hq ↦ hN1 q hq⟩

/-- Helper for Lemma PI-13: there is a prime above a threshold and above every `natAbs` in a
finite set of integers. -/
lemma exists_prime_gt_natAbs_sup (M : Finset ℤ) (K : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ K < p ∧ ∀ m ∈ M, Int.natAbs m < p := by
  -- Choose a prime above both `K + 1` and the finite supremum of the absolute values.
  obtain ⟨p, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (max (K + 1) (M.sup Int.natAbs + 1))
  have hKp : K < p := by
    calc
      K < K + 1 := Nat.lt_succ_self K
      _ ≤ max (K + 1) (M.sup Int.natAbs + 1) := le_max_left _ _
      _ ≤ p := hpLower
  refine ⟨p, hpPrime, hKp, ?_⟩
  intro m hm
  -- Every member of `M` has `natAbs` bounded by the supremum, hence strictly below `p`.
  calc
    Int.natAbs m ≤ M.sup Int.natAbs := Finset.le_sup hm
    _ < M.sup Int.natAbs + 1 := Nat.lt_succ_self _
    _ ≤ max (K + 1) (M.sup Int.natAbs + 1) := le_max_right _ _
    _ ≤ p := hpLower

/-- Helper for Lemma PI-13: a natural number cannot divide a nonzero integer whose
absolute value is smaller than that natural number. -/
lemma not_int_dvd_of_natAbs_lt {p : ℕ} {m : ℤ} (hm : m ≠ 0) (hmp : Int.natAbs m < p) :
    ¬ ((p : ℤ) ∣ m) := by
  -- Move divisibility to `natAbs m`, then compare sizes in `ℕ`.
  intro hdiv
  have hdivNat : p ∣ Int.natAbs m := (Int.natCast_dvd.mp hdiv)
  have hle : p ≤ Int.natAbs m := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hdivNat
  exact Nat.not_le_of_lt hmp hle

/-- Lemma PI-13: for real constants `A` and `B`, a natural-number threshold `N`, and a
finite set `M` of nonzero integers, there exists a prime `p > N` such that
`A * B ^ p / ((p - 1)!) < 1` and `p` divides none of the integers in `M`. -/
theorem exists_large_prime_avoiding_finset_with_factorial_bound
    (A B : ℝ) (N : ℕ) (M : Finset ℤ)
    (hM : ∀ m ∈ M, m ≠ 0) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      N < p ∧
      A * B ^ p / ((p - 1)! : ℝ) < 1 ∧
      ∀ m ∈ M, ¬ ((p : ℤ) ∣ m) := by
  -- First choose a threshold after which the factorial term is uniformly small.
  obtain ⟨N1, hN1⟩ := exists_eventual_factorial_bound A B
  -- Then choose a prime above both `N`, `N1`, and all absolute values in `M`.
  obtain ⟨p, hpPrime, hpLarge, hpAbs⟩ := exists_prime_gt_natAbs_sup M (max N N1)
  have hNp : N < p := lt_of_le_of_lt (le_max_left N N1) hpLarge
  have hN1p : N1 ≤ p := Nat.le_of_lt (lt_of_le_of_lt (le_max_right N N1) hpLarge)
  have hAnalytic : A * B ^ p / ((p - 1)! : ℝ) < 1 := hN1 p hN1p
  refine ⟨p, hpPrime, hNp, hAnalytic, ?_⟩
  intro m hm
  -- A divisor `p` of `m` would force `p ≤ natAbs m`, contradicting the chosen size bound.
  exact not_int_dvd_of_natAbs_lt (hM m hm) (hpAbs m hm)
