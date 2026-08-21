/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open BigOperators
open scoped BigOperators Topology

section Chap02
section Section05

variable {α : Type*}

/-- Definition 2.5.1: For a sequence `x : ℕ → α`, the expression
`∑_{n=1}^{∞} x n` denotes the formal series. Its `k`-th partial sum is
`s k = ∑_{n=1}^k x n`. The series converges to `ℓ` when the partial sums
`s k` converge to `ℓ` as `k → ∞`; otherwise the series is divergent. When the
series converges we identify its value with this limit. -/
def partialSumsFromOne [AddCommMonoid α] (x : ℕ → α) (k : ℕ) : α :=
  (Finset.Icc 1 k).sum fun n => x n

lemma partialSumsFromOne_eq_sum_range_succ {β : Type*} [AddCommMonoid β]
    (x : ℕ → β) (k : ℕ) :
    partialSumsFromOne x k =
      (Finset.range k).sum (fun n => x (n + 1)) := by
  classical
  induction k with
  | zero =>
      simp [partialSumsFromOne]
  | succ k ih =>
      have hIcc :
          partialSumsFromOne x (Nat.succ k) =
            partialSumsFromOne x k + x (k + 1) := by
        have hle : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        simpa [partialSumsFromOne, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Finset.sum_Icc_succ_top (a := 1) (b := k) (f := x) hle)
      calc
        partialSumsFromOne x (Nat.succ k)
            = partialSumsFromOne x k + x (k + 1) := hIcc
        _ = (Finset.range k).sum (fun n => x (n + 1)) + x (k + 1) := by simp [ih]
        _ = (Finset.range (Nat.succ k)).sum (fun n => x (n + 1)) := by
              simp [Finset.sum_range_succ]

variable [NormedAddCommGroup α]

/-- Convergence of the series `∑_{n=1}^{∞} x n` to a limit `ℓ`, expressed via
the convergence of the partial sums `∑_{n=1}^k x n` as `k → ∞`. -/
def SeriesConvergesTo (x : ℕ → α) (ℓ : α) : Prop :=
  HasSum (fun n => x (n + 1)) ℓ

/-- The series `∑_{n=1}^{∞} x n` is convergent if its partial sums admit some
limit. -/
def SeriesConvergent (x : ℕ → α) : Prop :=
  Summable (fun n => x (n + 1))

/-- A divergent series is one whose partial sums do not converge. -/
def SeriesDivergent (x : ℕ → α) : Prop :=
  ¬ SeriesConvergent x

/-- Definition 2.5.7: A series `∑_{n=1}^{∞} x n` is called Cauchy (a Cauchy
series) when its sequence of partial sums `∑_{n=1}^k x n` forms a Cauchy
sequence. -/
def SeriesCauchy (x : ℕ → α) : Prop :=
  CauchySeq fun k : ℕ => partialSumsFromOne x k

/-- Bridge to mathlib's `HasSum`: using the shift starting at `1` our notion of
converging series agrees with `HasSum`. -/
lemma seriesConvergesTo_iff_hasSum_shift (x : ℕ → α) (ℓ : α) :
    SeriesConvergesTo x ℓ ↔ HasSum (fun n => x (n + 1)) ℓ := by
  rfl

/-- The book's notion of a convergent series agrees with mathlib's `Summable`
for the shifted sequence starting at index `1`. -/
lemma seriesConvergent_iff_summable (x : ℕ → α) :
    SeriesConvergent x ↔ Summable (fun n => x (n + 1)) := by
  rfl

/-- When the series `∑_{n=1}^{∞} x n` converges to `ℓ`, the limit equals the
`tsum` of the underlying sequence indexed from `1`. -/
lemma series_limit_eq_tsum {x : ℕ → α} {ℓ : α} :
    SeriesConvergesTo x ℓ ↔
      Summable (fun n => x (n + 1)) ∧ tsum (fun n => x (n + 1)) = ℓ := by
  constructor
  · intro h
    exact ⟨h.summable, h.tsum_eq⟩
  · rintro ⟨hs, htsum⟩
    simpa [htsum] using (hs.hasSum)

/-- Proposition 2.5.6: For a series `∑_{n=1}^{∞} x n` and any `M ∈ ℕ`,
convergence is unchanged by discarding the first `M - 1` terms; equivalently
`∑_{n=1}^{∞} x n` converges if and only if the tail `∑_{n=M}^{∞} x n`
converges. -/
lemma series_convergent_iff_convergent_tail (x : ℕ → α) (M : ℕ) :
    SeriesConvergent x ↔ SeriesConvergent (fun n => x (n + (M - 1))) := by
  cases M with
  | zero =>
      simp [SeriesConvergent]
  | succ M =>
      -- now `M - 1 = M`
      simpa [SeriesConvergent, Nat.succ_sub_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (summable_nat_add_iff (k := M) (f := fun n => x (n + 1))).symm

/-- Proposition 2.5.5: For a real number `r` with `-1 < r < 1`, the geometric
series `∑_{n=0}^{∞} r^n` converges and its sum equals `1 / (1 - r)`. -/
lemma geometric_series_sum {r : ℝ} (h₁ : -1 < r) (h₂ : r < 1) :
    Summable (fun n : ℕ => r ^ n) ∧ tsum (fun n => r ^ n) = 1 / (1 - r) := by
  have hnorm : ‖r‖ < 1 := by
    have habs : |r| < 1 := abs_lt.mpr ⟨h₁, h₂⟩
    simpa [Real.norm_eq_abs] using habs
  have hs : Summable (fun n : ℕ => r ^ n) :=
    (summable_geometric_iff_norm_lt_one).2 hnorm
  have hsum : tsum (fun n : ℕ => r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_norm_lt_one hnorm
  constructor
  · exact hs
  · simpa [one_div] using hsum

/-- A closed form for the partial sums of the geometric series with ratio `1/2`. -/
lemma geometric_half_partial_sum_closed_form (k : ℕ) :
    partialSumsFromOne (fun n : ℕ => (1 / 2 : ℝ) ^ n) k =
      1 - (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      simp [partialSumsFromOne_eq_sum_range_succ]
  | succ k ih =>
      have hsum := partialSumsFromOne_eq_sum_range_succ (fun n : ℕ => (1 / 2 : ℝ) ^ n) (Nat.succ k)
      have hsum_prev :=
        partialSumsFromOne_eq_sum_range_succ (fun n : ℕ => (1 / 2 : ℝ) ^ n) k
      calc
        partialSumsFromOne (fun n : ℕ => (1 / 2 : ℝ) ^ n) (Nat.succ k)
            = (Finset.range (Nat.succ k)).sum (fun n => (1 / 2 : ℝ) ^ (n + 1)) := hsum
        _ = (Finset.range k).sum (fun n => (1 / 2 : ℝ) ^ (n + 1)) +
              (1 / 2 : ℝ) ^ (k + 1) := by
              simp [Finset.sum_range_succ]
        _ = partialSumsFromOne (fun n : ℕ => (1 / 2 : ℝ) ^ n) k +
              (1 / 2 : ℝ) ^ (k + 1) := by
              rw [hsum_prev]
        _ = (1 - (1 / 2 : ℝ) ^ k) + (1 / 2 : ℝ) ^ (k + 1) := by
              rw [ih]
        _ = 1 - (1 / 2 : ℝ) ^ (k + 1) := by ring

lemma geometric_half_partial_sum_closed_form_inv (k : ℕ) :
    partialSumsFromOne (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) k =
      1 - ((2 : ℝ) ^ k)⁻¹ := by
  simpa [one_div, inv_pow] using (geometric_half_partial_sum_closed_form k)

/-- Example 2.5.4: The geometric series `∑_{n=1}^{∞} (1/2)^n` converges to `1`.
For each `k ≥ 1`, the partial sum satisfies
`∑_{n=1}^k (1/2)^n + (1/2)^k = 1`, so the sequence of partial sums tends to `1`. -/
lemma geometric_half_partial_sum_eq (k : ℕ) (hk : 1 ≤ k) :
    partialSumsFromOne (fun n : ℕ => (1 / 2 : ℝ) ^ n) k + (1 / 2 : ℝ) ^ k = 1 := by
  have hk0 : 0 < k := (Nat.succ_le_iff).mp hk
  obtain ⟨k₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
  calc
    partialSumsFromOne (fun n : ℕ => (1 / 2 : ℝ) ^ n) (Nat.succ k₀) +
        (1 / 2 : ℝ) ^ (Nat.succ k₀)
        = (1 - (1 / 2 : ℝ) ^ (Nat.succ k₀)) + (1 / 2 : ℝ) ^ (Nat.succ k₀) := by
            rw [geometric_half_partial_sum_closed_form]
    _ = 1 := by ring

/-- Example 2.5.4: Consequently, the series `∑_{n=1}^{∞} (1/2)^n` converges and
its sum equals `1`. -/
lemma geometric_half_series_converges :
    SeriesConvergesTo (fun n : ℕ => (1 / 2 : ℝ) ^ n) (1 : ℝ) := by
  have hsum : HasSum (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) (2 : ℝ) := by
    have hlt : |(2 : ℝ)⁻¹| < 1 := by norm_num
    have h :
        HasSum (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) ((1 - (2 : ℝ)⁻¹)⁻¹) :=
      hasSum_geometric_of_abs_lt_one hlt
    have hval : (1 - (2 : ℝ)⁻¹)⁻¹ = (2 : ℝ) := by norm_num
    simpa [one_div, inv_pow, hval] using h
  have hshift :
      HasSum (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) (1 : ℝ) := by
    have := hsum.mul_left ((2 : ℝ)⁻¹)
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc, inv_pow, one_div] using this
  simpa [SeriesConvergesTo, one_div, inv_pow] using hshift

/-- Split partial sums into an initial segment plus a tail over `Icc (n+1) k`. -/
lemma partialSumsFromOne_add_tail {β : Type*} [AddCommMonoid β]
    (x : ℕ → β) {n k : ℕ} (hnk : n ≤ k) :
    partialSumsFromOne x k =
      partialSumsFromOne x n + (Finset.Icc (n + 1) k).sum (fun i => x i) := by
  classical
  induction k generalizing n with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnk
      subst hn0
      simp [partialSumsFromOne]
  | succ k ih =>
      have hsum :
          partialSumsFromOne x (Nat.succ k) =
            partialSumsFromOne x k + x (k + 1) := by
        have hle : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        simpa [partialSumsFromOne, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Finset.sum_Icc_succ_top (a := 1) (b := k) (f := x) hle)
      rcases lt_or_eq_of_le hnk with hlt | rfl
      · have hnk' : n ≤ k := Nat.lt_succ_iff.mp hlt
        have htail :
            (Finset.Icc (n + 1) (Nat.succ k)).sum (fun i => x i) =
              (Finset.Icc (n + 1) k).sum (fun i => x i) + x (k + 1) := by
          have hle : n + 1 ≤ k + 1 := Nat.succ_le_succ hnk'
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.sum_Icc_succ_top (a := n + 1) (b := k) (f := x) hle)
        calc
          partialSumsFromOne x (Nat.succ k)
              = partialSumsFromOne x k + x (k + 1) := hsum
          _ = (partialSumsFromOne x n + (Finset.Icc (n + 1) k).sum (fun i => x i)) + x (k + 1) := by
                simp [ih hnk', add_left_comm, add_comm]
          _ = partialSumsFromOne x n + ((Finset.Icc (n + 1) k).sum (fun i => x i) + x (k + 1)) := by
                simp [add_assoc]
          _ = partialSumsFromOne x n + (Finset.Icc (n + 1) (Nat.succ k)).sum (fun i => x i) := by
                simpa using congrArg (fun t => partialSumsFromOne x n + t) htail.symm
      · have hlt : (Nat.succ k) < Nat.succ k + 1 := Nat.lt_succ_self (Nat.succ k)
        simp [Finset.Icc_eq_empty_of_lt, hlt]

/-- The difference of partial sums is the tail sum over `Icc (n+1) k`. -/
lemma partialSumsFromOne_sub_eq_tail {β : Type*} [AddCommGroup β]
    (x : ℕ → β) {n k : ℕ} (hnk : n ≤ k) :
    partialSumsFromOne x k - partialSumsFromOne x n =
      (Finset.Icc (n + 1) k).sum (fun i => x i) := by
  have h := partialSumsFromOne_add_tail (x := x) (n := n) (k := k) hnk
  have h' := congrArg (fun t => t - partialSumsFromOne x n) h
  simpa [add_sub_cancel_left] using h'

/-- Distance between partial sums equals the norm of the corresponding tail sum. -/
lemma dist_partialSums_eq_norm_tail (x : ℕ → α) {n k : ℕ} (hnk : n ≤ k) :
    dist (partialSumsFromOne x n) (partialSumsFromOne x k) =
      ‖(Finset.Icc (n + 1) k).sum (fun i => x i)‖ := by
  have h := partialSumsFromOne_sub_eq_tail (x := x) (n := n) (k := k) hnk
  calc
    dist (partialSumsFromOne x n) (partialSumsFromOne x k)
        = dist (partialSumsFromOne x k) (partialSumsFromOne x n) := by
            simp [dist_comm]
    _ = ‖partialSumsFromOne x k - partialSumsFromOne x n‖ := by
          simp [dist_eq_norm]
    _ = ‖(Finset.Icc (n + 1) k).sum (fun i => x i)‖ := by
          simp [h]

/-- Proposition 2.5.8: The series `∑_{n=1}^{∞} x n` is Cauchy if and only if
for every `ε > 0` there exists `M ∈ ℕ` such that for all `n ≥ M` and `k > n`,
the tail sum `∑_{i=n+1}^k x i` has norm less than `ε`. -/
lemma series_cauchy_iff_tail_norm_small (x : ℕ → α) :
    SeriesCauchy x ↔
      ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ ⦃n k : ℕ⦄, M ≤ n → n < k →
        ‖(Finset.Icc (n + 1) k).sum (fun i => x i)‖ < ε := by
  constructor
  · intro h ε hε
    have hC :
        ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, ∀ n ≥ M,
          dist (partialSumsFromOne x m) (partialSumsFromOne x n) < ε :=
      (Metric.cauchySeq_iff).1 (by simpa [SeriesCauchy] using h)
    obtain ⟨M, hM⟩ := hC ε hε
    refine ⟨M, ?_⟩
    intro n k hn hk
    have hk' : M ≤ k := le_trans hn (Nat.le_of_lt hk)
    have hdist : dist (partialSumsFromOne x n) (partialSumsFromOne x k) < ε := hM n hn k hk'
    have hnk : n ≤ k := Nat.le_of_lt hk
    simpa [dist_partialSums_eq_norm_tail (x := x) (n := n) (k := k) hnk] using hdist
  · intro h
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
    obtain ⟨M, hM⟩ := h ε hε
    refine ⟨M, ?_⟩
    intro m hm n hn
    cases le_total m n with
    | inl hmn =>
        cases lt_or_eq_of_le hmn with
        | inl hlt =>
            have htail :
                ‖(Finset.Icc (m + 1) n).sum (fun i => x i)‖ < ε := hM hm hlt
            have hdist :
                dist (partialSumsFromOne x m) (partialSumsFromOne x n) =
                  ‖(Finset.Icc (m + 1) n).sum (fun i => x i)‖ :=
              dist_partialSums_eq_norm_tail (x := x) (n := m) (k := n) (Nat.le_of_lt hlt)
            simpa [hdist] using htail
        | inr hEq =>
            subst hEq
            simpa [dist_self] using hε
    | inr hnm =>
        cases lt_or_eq_of_le hnm with
        | inl hlt =>
            have htail :
                ‖(Finset.Icc (n + 1) m).sum (fun i => x i)‖ < ε := hM hn hlt
            have hdist :
                dist (partialSumsFromOne x n) (partialSumsFromOne x m) =
                  ‖(Finset.Icc (n + 1) m).sum (fun i => x i)‖ :=
              dist_partialSums_eq_norm_tail (x := x) (n := n) (k := m) (Nat.le_of_lt hlt)
            have hdist' :
                dist (partialSumsFromOne x m) (partialSumsFromOne x n) =
                  ‖(Finset.Icc (n + 1) m).sum (fun i => x i)‖ := by
              simpa [dist_comm] using hdist
            simpa [hdist'] using htail
        | inr hEq =>
            subst hEq
            simpa [dist_self] using hε

/-- Proposition 2.5.9: If the series `∑_{n=1}^{∞} x n` converges, then the
underlying sequence converges and its limit is `0`; equivalently,
`lim_{n→∞} x n = 0`. -/
lemma series_convergent_tendsto_zero {x : ℕ → α} (hx : SeriesConvergent x) :
    Filter.Tendsto (fun n => x n) Filter.atTop (𝓝 (0 : α)) := by
  have hsum_tail : Summable (fun n => x (n + 1)) := by
    simpa [SeriesConvergent] using hx
  have hsum : Summable x :=
    (summable_nat_add_iff (k := 1) (f := x)).1 hsum_tail
  exact hsum.tendsto_atTop_zero

/-- If `|r| ≥ 1`, then `‖r‖` is not less than `1`. -/
lemma abs_ge_one_not_norm_lt_one {r : ℝ} (h : 1 ≤ |r|) : ¬ (‖r‖ < 1) := by
  have h' : ¬ |r| < 1 := not_lt_of_ge h
  intro hnorm
  exact h' (by simpa [Real.norm_eq_abs] using hnorm)

/-- Example 2.5.10: If `r ≥ 1` or `r ≤ -1`, the geometric series
`∑_{n=0}^{∞} r^n` diverges since the terms have absolute value at least `1` and
do not tend to zero. -/
lemma geometric_series_diverges_of_abs_ge_one {r : ℝ} (h : 1 ≤ |r|) :
    ¬ Summable (fun n : ℕ => r ^ n) := by
  intro hsum
  have hnorm : ‖r‖ < 1 :=
    (summable_geometric_iff_norm_lt_one).1 hsum
  exact (abs_ge_one_not_norm_lt_one h) hnorm

/-- A shifted tail of the harmonic series is not summable. -/
lemma harmonic_shift_not_summable :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (↑n + 1 + 1)) := by
  intro hsum
  have hbase : ¬ Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
    Real.not_summable_one_div_natCast
  have hsum' : Summable (fun n : ℕ => (1 : ℝ) / (n + 2)) := by
    have h2 : (1 : ℝ) + 1 = (2 : ℝ) := by norm_num
    simpa [h2, add_assoc, add_left_comm, add_comm] using hsum
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff (k := 2) (f := fun n : ℕ => (1 : ℝ) / (n : ℝ))).1
      (by
        simpa [Nat.cast_add] using hsum')
  exact hbase h

/-- Example 2.5.11: The harmonic series `∑_{n=1}^{∞} 1/n` diverges even though
its terms tend to `0`. Grouping the terms in blocks of length `2^{k-1}` shows
that the partial sums `s_{2^k}` satisfy `s_{2^k} ≥ 1 + k/2`, which is
unbounded by the Archimedean property; hence the whole sequence of partial
sums is unbounded and the series diverges. -/
lemma harmonic_series_diverges :
    SeriesDivergent (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
  simpa [SeriesDivergent, SeriesConvergent, Nat.cast_add, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, one_div] using harmonic_shift_not_summable

/-- Proposition 2.5.12 (linearity of series). Let `α : ℝ` and suppose the
series `∑_{n=1}^{∞} x n` and `∑_{n=1}^{∞} y n` converge. Then
(i) the series `∑_{n=1}^{∞} α * x n` converges and its value is
`α * ∑_{n=1}^{∞} x n`; and
(ii) the series `∑_{n=1}^{∞} (x n + y n)` converges and its value is the sum of
the two series. -/
lemma series_convergesTo_smul {x : ℕ → ℝ} {α s : ℝ}
    (hx : SeriesConvergesTo x s) :
    SeriesConvergesTo (fun n => α * x n) (α * s) := by
  simpa [SeriesConvergesTo] using hx.mul_left α

lemma series_convergesTo_add {x y : ℕ → ℝ} {sx sy : ℝ}
    (hx : SeriesConvergesTo x sx) (hy : SeriesConvergesTo y sy) :
    SeriesConvergesTo (fun n => x n + y n) (sx + sy) := by
  simpa [SeriesConvergesTo] using hx.add hy

/-- Proposition 2.5.13: For a sequence of nonnegative real numbers, the series
`∑_{n=1}^{∞} x n` converges if and only if the sequence of partial sums is
bounded above. -/
lemma series_convergent_nonneg_iff_bddAbove {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) :
    SeriesConvergent x ↔
      BddAbove (Set.range fun k : ℕ => partialSumsFromOne x k) := by
  constructor
  · intro hsum
    have hsum' : Summable (fun n => x (n + 1)) := by
      simpa [SeriesConvergent] using hsum
    refine ⟨tsum (fun n => x (n + 1)), ?_⟩
    rintro _ ⟨k, rfl⟩
    have hx' : ∀ n, 0 ≤ x (n + 1) := by
      intro n
      exact hx (n + 1)
    simpa [partialSumsFromOne_eq_sum_range_succ] using
      (hsum'.sum_le_tsum (Finset.range k) (fun n _ => hx' n))
  · intro hbdd
    obtain ⟨c, hc⟩ := hbdd
    have hx' : ∀ n, 0 ≤ x (n + 1) := by
      intro n
      exact hx (n + 1)
    have hle : ∀ n, (Finset.range n).sum (fun i => x (i + 1)) ≤ c := by
      intro n
      have h' : partialSumsFromOne x n ≤ c := hc ⟨n, rfl⟩
      simpa [partialSumsFromOne_eq_sum_range_succ] using h'
    have hsum : Summable (fun n => x (n + 1)) :=
      summable_of_sum_range_le hx' hle
    simpa [SeriesConvergent] using hsum

/-- Definition 2.5.14: A series `∑_{n=1}^{∞} x n` converges absolutely if the
series of norms `∑_{n=1}^{∞} ‖x n‖` converges. If the original series converges
but does not converge absolutely, it is conditionally convergent. -/
def SeriesAbsolutelyConvergent (x : ℕ → α) : Prop :=
  SeriesConvergent (fun n => (‖x n‖ : ℝ))

def SeriesConditionallyConvergent (x : ℕ → α) : Prop :=
  SeriesConvergent x ∧ ¬ SeriesAbsolutelyConvergent x

/-- Proposition 2.5.15: An absolutely convergent series `∑_{n=1}^{∞} x n`
necessarily converges. -/
lemma series_convergent_of_abs_convergent [CompleteSpace α] {x : ℕ → α}
    (h : SeriesAbsolutelyConvergent x) :
    SeriesConvergent x := by
  have hsum_norm : Summable (fun n => ‖x (n + 1)‖) := by
    simpa [SeriesAbsolutelyConvergent, SeriesConvergent] using h
  have hsum : Summable (fun n => x (n + 1)) :=
    hsum_norm.of_norm
  simpa [SeriesConvergent] using hsum

/-- Proposition 2.5.16 (comparison test). Let `∑_{n=1}^{∞} x n` and
`∑_{n=1}^{∞} y n` be series with `0 ≤ x n ≤ y n` for all `n ∈ ℕ`.
(i) If `∑_{n=1}^{∞} y n` converges, then `∑_{n=1}^{∞} x n` converges.
(ii) If `∑_{n=1}^{∞} x n` diverges, then `∑_{n=1}^{∞} y n` diverges. -/
lemma series_convergent_of_le {x y : ℕ → ℝ}
    (hxy : ∀ n, 0 ≤ x n ∧ x n ≤ y n) (hy : SeriesConvergent y) :
    SeriesConvergent x := by
  have hy' : Summable (fun n => y (n + 1)) :=
    (seriesConvergent_iff_summable (x := y)).1 hy
  have hx_nonneg : ∀ n, 0 ≤ x (n + 1) := fun n => (hxy (n + 1)).1
  have hxy' : ∀ n, x (n + 1) ≤ y (n + 1) := fun n => (hxy (n + 1)).2
  have hx' : Summable (fun n => x (n + 1)) :=
    Summable.of_nonneg_of_le hx_nonneg hxy' hy'
  exact (seriesConvergent_iff_summable (x := x)).2 hx'

lemma series_divergent_of_le {x y : ℕ → ℝ}
    (hxy : ∀ n, 0 ≤ x n ∧ x n ≤ y n) (hx : SeriesDivergent x) :
    SeriesDivergent y := by
  intro hy
  apply hx
  exact series_convergent_of_le hxy hy

/-- Proposition 2.5.17 ($p$-series or the $p$-test). For `p ∈ ℝ`, the series
`∑_{n=1}^{∞} 1 / n^p` converges if and only if `p > 1`. -/
lemma p_series_converges_iff (p : ℝ) :
    SeriesConvergent (fun n => 1 / (Nat.succ n : ℝ) ^ p) ↔ 1 < p := by
  have hshift :
      SeriesConvergent (fun n => 1 / (Nat.succ n : ℝ) ^ p) ↔
        Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := by
    calc
      SeriesConvergent (fun n => 1 / (Nat.succ n : ℝ) ^ p)
          ↔ Summable (fun n : ℕ => 1 / ((Nat.succ (n + 1) : ℝ) ^ p)) := by rfl
      _ ↔ Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ p) := by
            simp [Nat.succ_eq_add_one, Nat.cast_add, add_comm, add_left_comm]
      _ ↔ Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := by
            simpa using
              (summable_nat_add_iff (k := 2) (f := fun n : ℕ => 1 / (n : ℝ) ^ p))
  have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
    Real.summable_one_div_nat_rpow (p := p)
  exact hshift.trans hps

/-- Example 2.5.18: The series `∑_{n=1}^{∞} 1 / (n^2 + 1)` converges, for instance
by comparison with the $p$-series `∑_{n=1}^{∞} 1 / n^2`. -/
lemma series_convergent_one_div_sq_add_one :
    SeriesConvergent (fun n : ℕ => 1 / ((n : ℝ) ^ 2 + 1)) := by
  -- drop the first term and compare the tail with the convergent $p$-series `p = 2`
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hshift :
      Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) :=
    (summable_nat_add_iff (k := 2)
          (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ))).2 hsum
  have h_major : SeriesConvergent (fun n : ℕ => 1 / (Nat.succ n : ℝ) ^ (2 : ℕ)) := by
    simpa [SeriesConvergent, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_two,
      Nat.cast_one, add_comm, add_left_comm, add_assoc] using hshift
  have hxy :
      ∀ n, 0 ≤ 1 / ((Nat.succ n : ℝ) ^ 2 + 1) ∧
        1 / ((Nat.succ n : ℝ) ^ 2 + 1) ≤ 1 / (Nat.succ n : ℝ) ^ 2 := by
    intro n
    have hpos : 0 < (Nat.succ n : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hsqpos : 0 < (Nat.succ n : ℝ) ^ 2 := by
      have := pow_pos hpos (2 : ℕ)
      simpa using this
    have hle : (Nat.succ n : ℝ) ^ 2 ≤ (Nat.succ n : ℝ) ^ 2 + 1 := by linarith
    have hden_nonneg : 0 ≤ (Nat.succ n : ℝ) ^ 2 + 1 := by
      have hsq_nonneg : 0 ≤ (Nat.succ n : ℝ) ^ 2 := sq_nonneg _
      linarith
    constructor
    · exact one_div_nonneg.mpr hden_nonneg
    · exact one_div_le_one_div_of_le hsqpos hle
  have h_tail :
      SeriesConvergent (fun n : ℕ => 1 / ((Nat.succ n : ℝ) ^ 2 + 1)) :=
    series_convergent_of_le hxy h_major
  -- convergence is unchanged by discarding the first term
  refine
    (series_convergent_iff_convergent_tail
        (x := fun n : ℕ => 1 / ((n : ℝ) ^ 2 + 1)) (M := 2)).2 ?_
  simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
    add_assoc] using h_tail

/-- Proposition 2.5.19 (ratio test). Let `∑_{n=1}^{∞} x n` be a real series with
`x n ≠ 0` for all `n`, and suppose the limit
`L = lim_{n→∞} |x (n+1)| / |x n|` exists. (i) If `L < 1`, the series converges
absolutely. (ii) If `L > 1`, the series diverges. -/
lemma ratio_test_converges {x : ℕ → ℝ} (hx : ∀ n, x n ≠ 0) {L : ℝ}
    (hlim : Filter.Tendsto (fun n => |x (n + 1)| / |x n|) Filter.atTop (𝓝 L))
    (hL : L < 1) :
    SeriesAbsolutelyConvergent x := by
  have hshift :
      Filter.Tendsto (fun n => |x (n + 2)| / |x (n + 1)|) Filter.atTop (𝓝 L) :=
    (Filter.tendsto_add_atTop_iff_nat
        (f := fun n => |x (n + 1)| / |x n|) (l := 𝓝 L) 1).2 hlim
  have hnonzero :
      ∀ᶠ n in Filter.atTop, ‖x (n + 1)‖ ≠ (0 : ℝ) :=
    by
      refine Filter.Eventually.of_forall ?_
      intro n
      have hx' : x (n + 1) ≠ 0 := hx (n + 1)
      simpa [Real.norm_eq_abs] using hx'
  have hlim' :
      Filter.Tendsto
        (fun n =>
          ‖(fun n => ‖x (n + 1)‖) (n + 1)‖ /
            ‖(fun n => ‖x (n + 1)‖) n‖)
        Filter.atTop (𝓝 L) := by
    simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using hshift
  have hsum :
      Summable (fun n => ‖x (n + 1)‖) :=
    summable_of_ratio_test_tendsto_lt_one (α := ℝ)
      (f := fun n => ‖x (n + 1)‖) hL hnonzero hlim'
  exact (seriesConvergent_iff_summable (x := fun n => (‖x n‖ : ℝ))).2 hsum

lemma ratio_test_diverges {x : ℕ → ℝ} (_hx : ∀ n, x n ≠ 0) {L : ℝ}
    (hlim : Filter.Tendsto (fun n => |x (n + 1)| / |x n|) Filter.atTop (𝓝 L))
    (hL : 1 < L) :
    SeriesDivergent x := by
  have hshift :
      Filter.Tendsto (fun n => |x (n + 2)| / |x (n + 1)|) Filter.atTop (𝓝 L) :=
    (Filter.tendsto_add_atTop_iff_nat
        (f := fun n => |x (n + 1)| / |x n|) (l := 𝓝 L) 1).2 hlim
  have hsum :
      ¬ Summable (fun n => x (n + 1)) :=
    not_summable_of_ratio_test_tendsto_gt_one (α := ℝ)
      (f := fun n => x (n + 1)) hL
      (by
        simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using hshift)
  simpa [SeriesDivergent, SeriesConvergent] using hsum

/-- The base series with terms `2^n / n!` is summable. -/
lemma summable_pow_div_factorial :
    Summable (fun n : ℕ => (2 : ℝ) ^ n / Nat.factorial n) := by
  simpa using (Real.summable_pow_div_factorial 2)

/-- Shifting the index preserves summability for `2^n / n!`. -/
lemma summable_shift_pow_div_factorial :
    Summable (fun n : ℕ => (2 : ℝ) ^ (n + 1) / Nat.factorial (n + 1)) := by
  simpa using
    (summable_nat_add_iff (k := 1)
        (f := fun n : ℕ => (2 : ℝ) ^ n / Nat.factorial n)).2
      summable_pow_div_factorial

/-- The series of norms of the shifted terms is summable. -/
lemma summable_norm_shift_pow_div_factorial :
    Summable (fun n : ℕ => ‖(2 : ℝ) ^ (n + 1) / Nat.factorial (n + 1)‖) := by
  exact summable_shift_pow_div_factorial.norm

/-- Example 2.5.20: The series `∑_{n=1}^{∞} 2^n / n!` converges absolutely.
The ratio of successive terms tends to `0`, so the ratio test applies. -/
lemma series_abs_convergent_two_pow_div_factorial :
    SeriesAbsolutelyConvergent (fun n : ℕ => (2 : ℝ) ^ n / Nat.factorial n) := by
  simpa [SeriesAbsolutelyConvergent, SeriesConvergent] using
    summable_norm_shift_pow_div_factorial

end Section05
end Chap02
