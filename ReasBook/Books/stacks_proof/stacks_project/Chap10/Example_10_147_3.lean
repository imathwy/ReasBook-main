import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open Polynomial

section

variable (p d : ℕ)

local notation "K" => Localization.Away (p : ℤ)
local notation "P" => cyclotomic p K
local notation "A" => AdjoinRoot P
local notation "ζ" => (AdjoinRoot.root P : A)

/-- Helper for Example 10.147.3: the distinguished adjoined root satisfies `ζ ^ p = 1`. -/
lemma zeta_pow_prime_eq_one [Fact p.Prime] : ζ ^ p = (1 : A) := by
  -- Evaluate the cyclotomic factorization at the distinguished root.
  have h :=
    congrArg (fun Q : K[X] => aeval ζ Q) (Polynomial.cyclotomic_prime_mul_X_sub_one K p)
  have hzero : 0 = ζ ^ p - 1 := by
    simpa [aeval_def] using h
  exact sub_eq_zero.mp hzero.symm

/-- Helper for Example 10.147.3: the distinguished root is a unit because its `p`-th power is `1`.
-/
lemma zeta_isUnit [Fact p.Prime] : IsUnit ζ := by
  -- A `p`-th root of unity is invertible, with inverse `ζ ^ (p - 1)`.
  have hp : p.Prime := Fact.out
  refine IsUnit.of_mul_eq_one (ζ ^ (p - 1)) ?_
  rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero]
  exact zeta_pow_prime_eq_one (p := p)

/-- Helper for Example 10.147.3: the basic cyclotomic unit `ζ - 1` is invertible. -/
lemma zeta_sub_one_isUnit [Fact p.Prime] : IsUnit (ζ - 1) := by
  -- Differentiate `(Φ_p) * (X - 1) = X ^ p - 1`, then evaluate at `ζ`.
  have h :=
    congrArg
      (fun Q : K[X] => aeval ζ Q)
      (congrArg (@Polynomial.derivative K _) (Polynomial.cyclotomic_prime_mul_X_sub_one K p))
  have hderiv_eval :
      aeval ζ (derivative P) * (ζ - 1) = aeval ζ (derivative (X ^ p : K[X])) := by
    simpa [aeval_def, derivative_mul] using h
  have hderiv_rhs : aeval ζ (derivative (X ^ p : K[X])) = (p : A) * ζ ^ (p - 1) := by
    rw [Polynomial.derivative_X_pow]
    simp [aeval_def]
  have hderiv : aeval ζ (derivative P) * (ζ - 1) = (p : A) * ζ ^ (p - 1) :=
    hderiv_eval.trans hderiv_rhs
  have hp_unit : IsUnit (p : A) := by
    simpa using
      (IsLocalization.Away.algebraMap_isUnit (S := K) (x := (p : ℤ))).map (algebraMap K A)
  have hrhs_unit : IsUnit ((p : A) * ζ ^ (p - 1)) := by
    exact hp_unit.mul ((zeta_isUnit (p := p)).pow (p - 1))
  -- The derivative identity shows `ζ - 1` divides a unit.
  exact
    isUnit_of_dvd_unit
      ⟨aeval ζ (derivative P), by simpa [mul_comm] using hderiv.symm⟩
      hrhs_unit

/-- Helper for Example 10.147.3: every nontrivial smaller power difference `ζ ^ m - 1` is a unit.
-/
lemma zeta_pow_sub_one_isUnit [Fact p.Prime] {m : ℕ} (hm0 : 0 < m) (hmp : m < p) :
    IsUnit (ζ ^ m - 1) := by
  -- Use a modular inverse of `m` modulo `p` to compare `ζ ^ m - 1` with `ζ - 1`.
  have hp : p.Prime := Fact.out
  have hm_coprime : m.Coprime p := (Nat.coprime_of_lt_prime hm0.ne' hmp hp).symm
  obtain ⟨n, _, hmod_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm_coprime hp.one_lt
  have hmod : m * n ≡ 1 [MOD p] := by
    simpa [Nat.ModEq, Nat.one_mod_eq_one.mpr hp.one_lt.ne'] using hmod_mod
  have hn0 : 0 < n := by
    by_contra hn0
    have hn : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hbad : 0 ≡ 1 [MOD p] := by simpa [hn] using hmod
    have hp1 : 1 < p := hp.one_lt
    simpa [Nat.ModEq, hp1.ne', Nat.one_mod_eq_one.mpr hp1.ne'] using hbad
  have hle : 1 ≤ m * n := by
    simpa using Nat.mul_le_mul (Nat.succ_le_of_lt hm0) (Nat.succ_le_of_lt hn0)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
  have hpow : (ζ ^ m) ^ n = ζ := by
    calc
      (ζ ^ m) ^ n = ζ ^ (m * n) := by rw [pow_mul]
      _ = ζ ^ (1 + p * k) := by rw [hk]
      _ = ζ ^ 1 * (ζ ^ p) ^ k := by rw [pow_add, pow_mul]
      _ = ζ * (ζ ^ p) ^ k := by rw [pow_one]
      _ = ζ := by rw [zeta_pow_prime_eq_one (p := p), one_pow, mul_one]
  have hdiv : ζ ^ m - 1 ∣ ζ - 1 := by
    refine ⟨∑ i ∈ Finset.range n, (ζ ^ m) ^ i, ?_⟩
    calc
      ζ - 1 = (ζ ^ m) ^ n - 1 := by simpa [hpow]
      _ = (ζ ^ m - 1) * ∑ i ∈ Finset.range n, (ζ ^ m) ^ i := by
        symm
        exact mul_geom_sum _ _
  -- A divisor of the unit `ζ - 1` is again a unit.
  exact isUnit_of_dvd_unit hdiv (zeta_sub_one_isUnit (p := p))

/-- Helper for Example 10.147.3: each ordered pairwise difference among the first `d` powers of `ζ`
is a unit when `d < p`. -/
lemma pairwise_power_difference_isUnit [Fact p.Prime] {i j : Fin d} (hij : i < j) (hd : d < p) :
    IsUnit (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) := by
  -- Rewrite the difference as a unit multiple of `ζ ^ (j - i) - 1`.
  have hm0 : 0 < (j : ℕ) - i := Nat.sub_pos_of_lt hij
  have hmp : (j : ℕ) - i < p := by
    exact lt_trans (lt_of_le_of_lt (Nat.sub_le _ _) j.2) hd
  have hz_pow_unit : IsUnit (ζ ^ (i : ℕ)) := (zeta_isUnit (p := p)).pow (i : ℕ)
  have hfactor :
      ζ ^ (i : ℕ) - ζ ^ (j : ℕ) = -(ζ ^ (i : ℕ)) * (ζ ^ ((j : ℕ) - i) - 1) := by
    calc
      ζ ^ (i : ℕ) - ζ ^ (j : ℕ)
          = ζ ^ (i : ℕ) - ζ ^ (i : ℕ) * ζ ^ ((j : ℕ) - i) := by
              rw [show (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) from
                    (Nat.add_sub_of_le (Nat.le_of_lt hij)).symm, pow_add, Nat.add_sub_cancel_left]
      _ = ζ ^ (i : ℕ) * (1 - ζ ^ ((j : ℕ) - i)) := by ring
      _ = -(ζ ^ (i : ℕ)) * (ζ ^ ((j : ℕ) - i) - 1) := by ring
  -- The remaining factor is a unit by the modular-inverse argument.
  rw [hfactor]
  exact (hz_pow_unit.neg).mul (zeta_pow_sub_one_isUnit (p := p) hm0 hmp)

/-- Example 10.147.3: for `d < p`, the first `d` powers of the distinguished root in
`ℤ[1/p][X] / (1 + X + ··· + X^(p - 1))` have unit pairwise-difference product. -/
-- Proof sketch: `Polynomial.cyclotomic_prime` identifies the defining polynomial with
-- `1 + X + ··· + X^(p - 1)`, so the example ring is the canonical adjoin-root quotient
-- `AdjoinRoot (cyclotomic p (Localization.Away (p : ℤ)))`. Take `α_i = ζ^i`, where `ζ` is the
-- distinguished root of this owner polynomial. In the fraction field these are distinct
-- `p`-th roots of unity, so `T^p - 1` factors as `∏ (T - α_i)`. Differentiating and evaluating at
-- each `α_i` identifies the omitted-difference product with `p * α_i^(p - 1)`, which is a unit
-- because `p` is inverted in the base ring and each `α_i` is itself a unit.
@[stacks 03GF]
theorem cyclotomic_prime_example_unit_pairwise_difference_product
    [Fact p.Prime] (hd : d < p) :
    IsUnit
      (∏ ij ∈ (Finset.univ : Finset (Fin d)).offDiag with ij.1 < ij.2,
        (ζ ^ (ij.1 : ℕ) - ζ ^ (ij.2 : ℕ))) := by
  -- Each factor in the filtered off-diagonal product is already a unit.
  refine (IsUnit.prod_iff).2 ?_
  intro ij hij
  exact pairwise_power_difference_isUnit (p := p) (d := d) ((Finset.mem_filter.mp hij).2) hd

end
