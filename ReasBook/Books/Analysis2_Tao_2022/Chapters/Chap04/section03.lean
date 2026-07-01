/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap04.section01

open scoped BigOperators

section Chap04
section Section03

/-- Helper for Lemma 4.3.1: one-step algebraic summation-by-parts identity. -/
lemma helperForLemma_4_3_1_stepIdentity (a b : ℕ → ℝ) (n : ℕ) :
    (a (n + 1) - a n) * b n + a (n + 1) * (b (n + 1) - b n)
      = a (n + 1) * b (n + 1) - a n * b n := by
  ring

/-- Helper for Lemma 4.3.1: telescoping finite sum of the two-by-parts terms. -/
lemma helperForLemma_4_3_1_telescoping (a b : ℕ → ℝ) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        ((a (n + 1) - a n) * b n + a (n + 1) * (b (n + 1) - b n)))
        = a N * b N - a 0 * b 0
  | 0 => by
      simp
  | N + 1 => by
      calc
        (∑ n ∈ Finset.range (N + 1),
            ((a (n + 1) - a n) * b n + a (n + 1) * (b (n + 1) - b n)))
            = (∑ n ∈ Finset.range N,
                ((a (n + 1) - a n) * b n + a (n + 1) * (b (n + 1) - b n))) +
                ((a (N + 1) - a N) * b N + a (N + 1) * (b (N + 1) - b N)) := by
              simp [Finset.sum_range_succ]
        _ = (a N * b N - a 0 * b 0) +
              ((a (N + 1) - a N) * b N + a (N + 1) * (b (N + 1) - b N)) := by
              rw [helperForLemma_4_3_1_telescoping a b N]
        _ = (a N * b N - a 0 * b 0) +
              (a (N + 1) * b (N + 1) - a N * b N) := by
              rw [helperForLemma_4_3_1_stepIdentity a b N]
        _ = a (N + 1) * b (N + 1) - a 0 * b 0 := by
              ring

/-- Helper for Lemma 4.3.1: finite summation-by-parts identity over `Finset.range N`. -/
lemma helperForLemma_4_3_1_finiteFormula (a b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n)
      = a N * b N - a 0 * b 0 - ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n) := by
  have hdecomp :
      (∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n) +
          (∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
        = a N * b N - a 0 * b 0 := by
    calc
      (∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n) +
          (∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
          = ∑ n ∈ Finset.range N,
              ((a (n + 1) - a n) * b n + a (n + 1) * (b (n + 1) - b n)) := by
              symm
              exact Finset.sum_add_distrib
      _ = a N * b N - a 0 * b 0 := by
            exact helperForLemma_4_3_1_telescoping a b N
  exact (eq_sub_iff_add_eq).2 hdecomp

/-- Helper for Lemma 4.3.1: convergence of ordered partial sums of
`a (n+1) * (b (n+1) - b n)` to the summation-by-parts limit value. -/
lemma helperForLemma_4_3_1_tendsto_partialSums
    (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n)) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
      Filter.atTop
      (nhds (A * B - a 0 * b 0 - ∑' n : ℕ, (a (n + 1) - a n) * b n)) := by
  have hprod : Filter.Tendsto (fun N : ℕ => a N * b N) Filter.atTop (nhds (A * B)) :=
    ha.mul hb
  have hsum :
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n)
        Filter.atTop
        (nhds (∑' n : ℕ, (a (n + 1) - a n) * b n)) :=
    hconv.hasSum.tendsto_sum_nat
  have hright :
      Filter.Tendsto
        (fun N : ℕ =>
          a N * b N - a 0 * b 0 - ∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n)
        Filter.atTop
        (nhds (A * B - a 0 * b 0 - ∑' n : ℕ, (a (n + 1) - a n) * b n)) := by
    exact (hprod.sub tendsto_const_nhds).sub hsum
  have hEq :
      (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n)) =
        (fun N : ℕ =>
          a N * b N - a 0 * b 0 - ∑ n ∈ Finset.range N, (a (n + 1) - a n) * b n) := by
    funext N
    have hfinite := helperForLemma_4_3_1_finiteFormula a b N
    linarith
  simpa [hEq] using hright

/-- Helper for Lemma 4.3.1: if the forward-difference series has a prescribed sum `S`,
the summation-by-parts identity holds with that same `S`. -/
lemma helperForLemma_4_3_1_identity_of_hasSumForwardDifference
    (a b : ℕ → ℝ) (A B S : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hhasSumForward : HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) S) :
    (∑' n : ℕ, (a (n + 1) - a n) * b n) =
      A * B - a 0 * b 0 - S := by
  have hpartial := helperForLemma_4_3_1_tendsto_partialSums a b A B ha hb hconv
  have hforward :
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
        Filter.atTop
        (nhds S) :=
    hhasSumForward.tendsto_sum_nat
  have hlimitEq :
      A * B - a 0 * b 0 - ∑' n : ℕ, (a (n + 1) - a n) * b n = S :=
    tendsto_nhds_unique hpartial hforward
  linarith

/-- Helper for Lemma 4.3.1: a `HasSum` hypothesis for the forward-difference series
immediately yields summability and the corresponding summation-by-parts identity. -/
lemma helperForLemma_4_3_1_formula_with_hasSumForwardDifference
    (a b : ℕ → ℝ) (A B S : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hhasSumForward : HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) S) :
    Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
      (∑' n : ℕ, (a (n + 1) - a n) * b n) =
        A * B - a 0 * b 0 - S := by
  refine ⟨hhasSumForward.summable, ?_⟩
  exact helperForLemma_4_3_1_identity_of_hasSumForwardDifference
    a b A B S ha hb hconv hhasSumForward

/-- Helper for Lemma 4.3.1: an explicit forward-difference `HasSum` hypothesis
already yields the textbook identity written with `tsum`. -/
lemma helperForLemma_4_3_1_tsumIdentity_of_hasSumForwardDifference
    (a b : ℕ → ℝ) (A B S : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hhasSumForward : HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) S) :
    (∑' n : ℕ, (a (n + 1) - a n) * b n) =
      A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n) := by
  have hIdentityWithS :
      (∑' n : ℕ, (a (n + 1) - a n) * b n) =
        A * B - a 0 * b 0 - S :=
    helperForLemma_4_3_1_identity_of_hasSumForwardDifference
      a b A B S ha hb hconv hhasSumForward
  calc
    (∑' n : ℕ, (a (n + 1) - a n) * b n) = A * B - a 0 * b 0 - S := hIdentityWithS
    _ = A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n) := by
      rw [← hhasSumForward.tsum_eq]

/-- Helper for Lemma 4.3.1: a corrected summation-by-parts statement with an explicit
forward `HasSum` hypothesis gives both forward summability and the textbook `tsum` identity. -/
lemma helperForLemma_4_3_1_formula_with_explicitForwardHasSum
    (a b : ℕ → ℝ) (A B S : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hhasSumForward : HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) S) :
    Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
      (∑' n : ℕ, (a (n + 1) - a n) * b n) =
        A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n) := by
  refine ⟨hhasSumForward.summable, ?_⟩
  exact helperForLemma_4_3_1_tsumIdentity_of_hasSumForwardDifference
    a b A B S ha hb hconv hhasSumForward

/-- Helper for Lemma 4.3.1: unconditional forward-difference summability supplies
the canonical `HasSum` witness at its `tsum`. -/
lemma helperForLemma_4_3_1_hasSumForwardDifference_of_summable
    (a b : ℕ → ℝ)
    (hsummableForward : Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) :
    HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))
      (∑' n : ℕ, a (n + 1) * (b (n + 1) - b n)) :=
  hsummableForward.hasSum

/-- Helper for Lemma 4.3.1: assuming unconditional summability of the forward-difference
series, the target summation-by-parts identity follows from uniqueness of the partial-sum limit. -/
lemma helperForLemma_4_3_1_identity_of_summableForwardDifference
    (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hsummableForward : Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) :
    (∑' n : ℕ, (a (n + 1) - a n) * b n) =
      A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n) := by
  have hhasSumForward :
      HasSum (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))
        (∑' n : ℕ, a (n + 1) * (b (n + 1) - b n)) :=
    helperForLemma_4_3_1_hasSumForwardDifference_of_summable a b hsummableForward
  exact helperForLemma_4_3_1_identity_of_hasSumForwardDifference
    a b A B (∑' n : ℕ, a (n + 1) * (b (n + 1) - b n)) ha hb hconv hhasSumForward

/-- Helper for Lemma 4.3.1: if forward-difference summability is given explicitly,
the full summation-by-parts conclusion follows. -/
lemma helperForLemma_4_3_1_formula_with_forwardSummable
    (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n))
    (hsummableForward : Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) :
    Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
      (∑' n : ℕ, (a (n + 1) - a n) * b n) =
        A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n) := by
  refine ⟨hsummableForward, ?_⟩
  exact helperForLemma_4_3_1_identity_of_summableForwardDifference
    a b A B ha hb hconv hsummableForward

/-- Helper for Lemma 4.3.1: the alternating harmonic sequence tends to `0`. -/
lemma helperForLemma_4_3_1_tendsto_alternatingHarmonic :
    Filter.Tendsto (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  have hEq : ‖(-1 : ℝ) ^ n / (n + 1)‖ = (1 : ℝ) / (n + 1) := by
    calc
      ‖(-1 : ℝ) ^ n / (n + 1)‖ = ‖(-1 : ℝ) ^ n‖ / ‖(n + 1 : ℝ)‖ := norm_div _ _
      _ = (1 : ℝ) / (n + 1) := by
            have hnonneg : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
            simp [abs_of_nonneg hnonneg]
  exact hEq.le

/-- Helper for Lemma 4.3.1: the forward difference of the alternating harmonic sequence is not
unconditionally summable in `ℝ`. -/
lemma helperForLemma_4_3_1_notSummable_alternatingHarmonicForwardDifference :
    ¬ Summable (fun n : ℕ => ((-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1))) := by
  intro hs
  have hsNorm : Summable (fun n : ℕ =>
      ‖(-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1)‖) :=
    hs.norm
  have hsHarmonicShift : Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
    refine Summable.of_nonneg_of_le ?hNonneg ?hLe hsNorm
    · intro n
      positivity
    · intro n
      have hEqNorm :
          ‖(-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1)‖
            = (1 : ℝ) / (n + 1) + 1 / (n + 2) := by
        calc
          ‖(-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1)‖
              = ‖(-1 : ℝ) ^ n * (-(1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ)))‖ := by
                  congr 1
                  ring_nf
          _ = ‖(-1 : ℝ) ^ n‖ * ‖-(1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ))‖ := norm_mul _ _
          _ = ‖-(1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ))‖ := by simp
          _ = |1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ)| := by rw [Real.norm_eq_abs, abs_neg]
          _ = (1 : ℝ) / (n + 1) + 1 / (n + 2) := by
                have hnonneg : (0 : ℝ) ≤ (1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ)) := by positivity
                have habs : |1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ)| =
                    1 / (n + 2 : ℝ) + 1 / (n + 1 : ℝ) := abs_of_nonneg hnonneg
                simpa [add_comm, add_left_comm, add_assoc] using habs
      rw [hEqNorm]
      have hnonnegSecond : (0 : ℝ) ≤ 1 / (n + 2 : ℝ) := by positivity
      linarith
  have hsHarmonic : Summable (fun n : ℕ => (1 : ℝ) / n) := by
    have hsShift' : Summable (fun n : ℕ => (1 : ℝ) / (↑(n + 1) : ℝ)) := by
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hsHarmonicShift
    exact (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / n) 1).1 hsShift'
  exact Real.not_summable_one_div_natCast hsHarmonic

/-- Helper for Lemma 4.3.1: for `b n = (-1)^n/(n+1)`, the forward-difference
series `∑ (b (n+1) - b n)` is not summable. -/
lemma helperForLemma_4_3_1_notSummable_forwardDifference_of_explicitB :
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬ Summable (fun n : ℕ => b (n + 1) - b n) := by
  intro b
  have hnotBase :
      ¬ Summable (fun n : ℕ =>
        ((-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1))) :=
    helperForLemma_4_3_1_notSummable_alternatingHarmonicForwardDifference
  have hEqSeq :
      (fun n : ℕ =>
        b (n + 1) - b n) =
        (fun n : ℕ =>
          ((-1 : ℝ) ^ (n + 1) / (n + 2) - (-1 : ℝ) ^ n / (n + 1))) := by
    funext n
    have hcast : ((n : ℝ) + 1 + 1) = ((n : ℝ) + 2) := by ring
    simp [b, Nat.cast_add, Nat.cast_one, hcast]
  simpa [hEqSeq] using hnotBase

/-- Helper for Lemma 4.3.1: for the explicit constant-one and alternating-harmonic
data, the weighted forward-difference series is not summable. -/
lemma helperForLemma_4_3_1_notSummable_weightedForwardDifference_of_explicitData :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
  intro a b
  have hnot : ¬ Summable (fun n : ℕ => b (n + 1) - b n) := by
    simpa [b] using helperForLemma_4_3_1_notSummable_forwardDifference_of_explicitB
  intro hsummableForward
  apply hnot
  simpa [a, b] using hsummableForward

/-- Helper for Lemma 4.3.1: the explicit constant-one and alternating-harmonic
data with concrete limits `A = 1`, `B = 0` satisfy the hypotheses while
the weighted forward-difference series is not summable. -/
lemma helperForLemma_4_3_1_explicitDataWithConcreteLimits :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
  intro a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [a]
  · simpa [b] using helperForLemma_4_3_1_tendsto_alternatingHarmonic
  · simpa [a, b] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · simpa [a, b] using
      helperForLemma_4_3_1_notSummable_weightedForwardDifference_of_explicitData

/-- Helper for Lemma 4.3.1: for the explicit constant-one and alternating-harmonic data,
the ordered partial sums of the weighted forward-difference series converge to `-1`. -/
lemma helperForLemma_4_3_1_explicitWeightedForwardDifference_partialSums_tendsto :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
      Filter.atTop
      (nhds (-1 : ℝ)) := by
  intro a b
  have hData :
      Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using helperForLemma_4_3_1_explicitDataWithConcreteLimits
  rcases hData with ⟨ha, hb, hconv, _⟩
  have hpartial :
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
        Filter.atTop
        (nhds (1 * 0 - a 0 * b 0 - ∑' n : ℕ, (a (n + 1) - a n) * b n)) :=
    helperForLemma_4_3_1_tendsto_partialSums a b 1 0 ha hb hconv
  have hsumZero : (∑' n : ℕ, (a (n + 1) - a n) * b n) = 0 := by
    simp [a]
  have ha0 : a 0 = (1 : ℝ) := by
    simp [a]
  have hb0 : b 0 = (1 : ℝ) := by
    simp [b]
  have hLimitEq :
      (-(a 0 * b 0) - ∑' n : ℕ, (a (n + 1) - a n) * b n) = (-1 : ℝ) := by
    rw [ha0, hb0, hsumZero]
    norm_num
  simpa [hLimitEq] using hpartial

/-- Helper for Lemma 4.3.1: there exists an explicit sequence whose ordered
partial sums converge, while the sequence is not `Summable` in Lean's
finite-subset summability sense. -/
lemma helperForLemma_4_3_1_existsOrderedPartialSumsLimitWithoutSummable :
    ∃ (f : ℕ → ℝ) (L : ℝ),
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds L) ∧
      ¬ Summable f := by
  let a : ℕ → ℝ := fun _ => 1
  let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
  let f : ℕ → ℝ := fun n => a (n + 1) * (b (n + 1) - b n)
  have hTendstoRaw :
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
        Filter.atTop
        (nhds (-1 : ℝ)) := by
    simpa [a, b] using
      helperForLemma_4_3_1_explicitWeightedForwardDifference_partialSums_tendsto
  have hNotSummableRaw :
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using
      helperForLemma_4_3_1_notSummable_weightedForwardDifference_of_explicitData
  have hTendstoF :
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds (-1 : ℝ)) := by
    simpa [f] using hTendstoRaw
  have hNotSummableF : ¬ Summable f := by
    simpa [f] using hNotSummableRaw
  exact ⟨f, -1, hTendstoF, hNotSummableF⟩

/-- Helper for Lemma 4.3.1: explicit data satisfy the hypotheses while the
forward-difference series fails to be unconditionally summable. -/
lemma helperForLemma_4_3_1_existsForwardCounterexample :
    ∃ (a b : ℕ → ℝ) (A B : ℝ),
      Filter.Tendsto a Filter.atTop (nhds A) ∧
      Filter.Tendsto b Filter.atTop (nhds B) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
  let a : ℕ → ℝ := fun _ => 1
  let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
  have hData :
      Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using helperForLemma_4_3_1_explicitDataWithConcreteLimits
  rcases hData with ⟨ha, hb, hconv, hnotForward⟩
  exact ⟨a, b, 1, 0, ha, hb, hconv, hnotForward⟩

/-- Helper for Lemma 4.3.1: the stated hypotheses do not force unconditional
summability of the forward-difference series in Lean's `Summable` sense. -/
lemma helperForLemma_4_3_1_universalForwardSummableFalse :
    ¬
      (∀ (a b : ℕ → ℝ) (A B : ℝ),
        Filter.Tendsto a Filter.atTop (nhds A) →
        Filter.Tendsto b Filter.atTop (nhds B) →
        Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) := by
  intro hUniversal
  rcases helperForLemma_4_3_1_existsForwardCounterexample with
    ⟨a, b, A, B, ha, hb, hconv, hnotForward⟩
  have hsummableForward :
      Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) :=
    hUniversal a b A B ha hb hconv
  exact hnotForward hsummableForward

/-- Helper for Lemma 4.3.1: for the explicit constant-one and alternating-harmonic
data at concrete limits, even the forward-summability implication alone is false. -/
lemma helperForLemma_4_3_1_explicitForwardImplicationFalseAtConcreteLimits :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬
      (Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) →
        Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) →
        Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) := by
  intro a b hImp
  have hdata :
      Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using helperForLemma_4_3_1_explicitDataWithConcreteLimits
  rcases hdata with ⟨ha, hb, hconv, hnotForward⟩
  exact hnotForward (hImp ha hb hconv)

/-- Helper for Lemma 4.3.1: the full universal statement of the textbook conclusion
would imply a universal forward-summability implication, which is false. -/
lemma helperForLemma_4_3_1_universalConclusionFalse :
    ¬
      (∀ (a b : ℕ → ℝ) (A B : ℝ),
        Filter.Tendsto a Filter.atTop (nhds A) →
        Filter.Tendsto b Filter.atTop (nhds B) →
        Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        (Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
          (∑' n : ℕ, (a (n + 1) - a n) * b n) =
            A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n))) := by
  intro hUniversal
  apply helperForLemma_4_3_1_universalForwardSummableFalse
  intro a b A B ha hb hconv
  exact (hUniversal a b A B ha hb hconv).1

/-- Helper for Lemma 4.3.1: there exists explicit data satisfying the hypotheses
for which the full textbook conclusion fails in Lean's unconditional `Summable` sense. -/
lemma helperForLemma_4_3_1_existsCounterexampleToConclusion :
    ∃ (a b : ℕ → ℝ) (A B : ℝ),
      Filter.Tendsto a Filter.atTop (nhds A) ∧
      Filter.Tendsto b Filter.atTop (nhds B) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬
        (Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
          (∑' n : ℕ, (a (n + 1) - a n) * b n) =
            A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n)) := by
  rcases helperForLemma_4_3_1_existsForwardCounterexample with
    ⟨a, b, A, B, ha, hb, hconv, hnotForward⟩
  refine ⟨a, b, A, B, ha, hb, hconv, ?_⟩
  intro hConclusion
  exact hnotForward hConclusion.1

/-- Helper for Lemma 4.3.1: the explicit constant-one and alternating-harmonic
data at concrete limits `A = 1`, `B = 0` refute the full textbook conclusion. -/
lemma helperForLemma_4_3_1_explicitDataRefutesConclusionAtConcreteLimits :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬
      (Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
        (∑' n : ℕ, (a (n + 1) - a n) * b n) =
          (1 : ℝ) * 0 - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n)) := by
  intro a b hConclusion
  have hnotForward :
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using
      helperForLemma_4_3_1_notSummable_weightedForwardDifference_of_explicitData
  exact hnotForward hConclusion.1

/-- Helper for Lemma 4.3.1: for the explicit constant-one and alternating-harmonic
data, convergence of `∑ (a_{n+1} - a_n)b_n` does not imply unconditional
summability of `∑ a_{n+1}(b_{n+1} - b_n)` in Lean. -/
lemma helperForLemma_4_3_1_explicitForwardSummableImplicationFalse :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬
      (Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n))) := by
  intro a b hImp
  have hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n) := by
    simpa [a, b] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hnotForward :
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using
      helperForLemma_4_3_1_notSummable_weightedForwardDifference_of_explicitData
  exact hnotForward (hImp hconv)

/-- Helper for Lemma 4.3.1: any universal proof of the textbook conclusion
contradicts the explicit counterexample already established above. -/
lemma helperForLemma_4_3_1_universalProofLeadsToFalse
    (hUniversal :
      ∀ (a b : ℕ → ℝ) (A B : ℝ),
        Filter.Tendsto a Filter.atTop (nhds A) →
        Filter.Tendsto b Filter.atTop (nhds B) →
        Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        (Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
          (∑' n : ℕ, (a (n + 1) - a n) * b n) =
            A * B - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n))) :
    False := by
  exact helperForLemma_4_3_1_universalConclusionFalse hUniversal

/-- Helper for Lemma 4.3.1: for the explicit constant-one and alternating-harmonic
data at concrete limits, the implication from the stated hypotheses to the full
textbook conclusion is false. -/
lemma helperForLemma_4_3_1_explicitImplicationFalseAtConcreteLimits :
    let a : ℕ → ℝ := fun _ => 1
    let b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n + 1)
    ¬
      (Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) →
        Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) →
        Summable (fun n : ℕ => (a (n + 1) - a n) * b n) →
        (Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) ∧
          (∑' n : ℕ, (a (n + 1) - a n) * b n) =
            (1 : ℝ) * 0 - a 0 * b 0 - ∑' n : ℕ, a (n + 1) * (b (n + 1) - b n))) := by
  intro a b hImp
  have hdata :
      Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) ∧
      Summable (fun n : ℕ => (a (n + 1) - a n) * b n) ∧
      ¬ Summable (fun n : ℕ => a (n + 1) * (b (n + 1) - b n)) := by
    simpa [a, b] using helperForLemma_4_3_1_explicitDataWithConcreteLimits
  rcases hdata with ⟨ha, hb, hconv, hnotForward⟩
  have hConclusion := hImp ha hb hconv
  exact hnotForward hConclusion.1

/-- Lemma 4.3.1 (Summation by parts formula): Let a, b : ℕ → ℝ with
Tendsto a atTop (𝓝 A) and Tendsto b atTop (𝓝 B). If the series
∑' n, (a (n + 1) - a n) * b n converges, then the ordered partial sums
of ∑ a (n + 1) * (b (n + 1) - b n) converge to
A * B - a 0 * b 0 - ∑' n, (a (n + 1) - a n) * b n.
-/
lemma summation_by_parts_formula
    (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds A))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hconv : Summable (fun n : ℕ => (a (n + 1) - a n) * b n)) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, a (n + 1) * (b (n + 1) - b n))
      Filter.atTop
      (nhds (A * B - a 0 * b 0 - ∑' n : ℕ, (a (n + 1) - a n) * b n)) := by
  exact helperForLemma_4_3_1_tendsto_partialSums a b A B ha hb hconv

/-- Helper for Theorem 4.3.1: the right-endpoint affine normalization
`x ↦ (x-a)/R` tends to `1` from below when `x → a+R` inside `(a-R,a+R)`. -/
lemma helperForTheorem_4_3_1_tendsto_affineToUnit_right {a R : ℝ}
    (hRpos : 0 < R) :
    Filter.Tendsto (fun x : ℝ => (x - a) / R)
      (nhdsWithin (a + R) (Set.Ioo (a - R) (a + R)))
      (nhdsWithin 1 (Set.Iio 1)) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => (x - a) / R)
      (Set.Ioo (a - R) (a + R)) (a + R) := by
    exact ((continuous_id.sub continuous_const).div_const R).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : ℝ => (x - a) / R)
      (Set.Ioo (a - R) (a + R)) (Set.Iio 1) := by
    intro x hx
    have hxsub : x - a < R := by
      linarith [hx.2]
    exact (div_lt_iff₀ hRpos).2 (by simpa using hxsub)
  simpa [hRpos.ne'] using hcont.tendsto_nhdsWithin hmaps

/-- Helper for Theorem 4.3.1: the left-endpoint affine normalization
`x ↦ (a-x)/R` tends to `1` from below when `x → a-R` inside `(a-R,a+R)`. -/
lemma helperForTheorem_4_3_1_tendsto_affineToUnit_left {a R : ℝ}
    (hRpos : 0 < R) :
    Filter.Tendsto (fun x : ℝ => (a - x) / R)
      (nhdsWithin (a - R) (Set.Ioo (a - R) (a + R)))
      (nhdsWithin 1 (Set.Iio 1)) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => (a - x) / R)
      (Set.Ioo (a - R) (a + R)) (a - R) := by
    exact ((continuous_const.sub continuous_id).div_const R).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : ℝ => (a - x) / R)
      (Set.Ioo (a - R) (a + R)) (Set.Iio 1) := by
    intro x hx
    have hxsub : a - x < R := by
      linarith [hx.1]
    exact (div_lt_iff₀ hRpos).2 (by simpa using hxsub)
  simpa [hRpos.ne'] using hcont.tendsto_nhdsWithin hmaps

/-- Helper for Theorem 4.3.1: right-endpoint term normalization identity. -/
lemma helperForTheorem_4_3_1_termRewrite_right {a R : ℝ}
    (hRpos : 0 < R) (f : FormalPowerSeriesCenteredAt a) (x : ℝ) (n : ℕ) :
    f.coeff n * R ^ n * (((x - a) / R) ^ n) = f.coeff n * (x - a) ^ n := by
  have hRne : R ≠ 0 := ne_of_gt hRpos
  calc
    f.coeff n * R ^ n * (((x - a) / R) ^ n)
        = f.coeff n * (R ^ n * (((x - a) / R) ^ n)) := by
          ring
    _ = f.coeff n * ((R * ((x - a) / R)) ^ n) := by
          rw [mul_pow]
    _ = f.coeff n * (x - a) ^ n := by
          congr 1
          field_simp [hRne]

/-- Helper for Theorem 4.3.1: left-endpoint term normalization identity. -/
lemma helperForTheorem_4_3_1_termRewrite_left {a R : ℝ}
    (hRpos : 0 < R) (f : FormalPowerSeriesCenteredAt a) (x : ℝ) (n : ℕ) :
    f.coeff n * (-R) ^ n * (((a - x) / R) ^ n) = f.coeff n * (x - a) ^ n := by
  have hRne : R ≠ 0 := ne_of_gt hRpos
  calc
    f.coeff n * (-R) ^ n * (((a - x) / R) ^ n)
        = f.coeff n * ((-R) ^ n * (((a - x) / R) ^ n)) := by
          ring
    _ = f.coeff n * (((-R) * ((a - x) / R)) ^ n) := by
          rw [mul_pow]
    _ = f.coeff n * ((-(a - x)) ^ n) := by
          congr 1
          field_simp [hRne]
    _ = f.coeff n * (x - a) ^ n := by
          congr 1
          ring

/-- Theorem 4.3.1 (Abel's theorem): let `f(x) = ∑' n, c_n (x-a)^n` be a real
power series centered at `a` with radius of convergence `R` and `0 < R`.
(1) If `∑' n, c_n R^n` converges, then `x ↦ ∑' n, c_n (x-a)^n` tends to
`∑' n, c_n R^n` as `x → a + R` within `(a - R, a + R)`.
(2) If `∑' n, c_n (-R)^n` converges, then `x ↦ ∑' n, c_n (x-a)^n` tends to
`∑' n, c_n (-R)^n` as `x → a - R` within `(a - R, a + R)`. -/
theorem FormalPowerSeriesCenteredAt.abel_theorem {a R : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hRpos : 0 < R)
    (hRadius : f.radiusOfConvergence = ENNReal.ofReal R) :
    (Summable (fun n : ℕ => f.coeff n * R ^ n) →
      Filter.Tendsto (fun x : ℝ => ∑' n : ℕ, f.coeff n * (x - a) ^ n)
        (nhdsWithin (a + R) (Set.Ioo (a - R) (a + R)))
        (nhds (∑' n : ℕ, f.coeff n * R ^ n))) ∧
    (Summable (fun n : ℕ => f.coeff n * (-R) ^ n) →
      Filter.Tendsto (fun x : ℝ => ∑' n : ℕ, f.coeff n * (x - a) ^ n)
        (nhdsWithin (a - R) (Set.Ioo (a - R) (a + R)))
        (nhds (∑' n : ℕ, f.coeff n * (-R) ^ n))) := by
  constructor
  · intro hSummableRight
    let d : ℕ → ℝ := fun n => f.coeff n * R ^ n
    have hd :
        Filter.Tendsto
          (fun n : ℕ => ∑ i ∈ Finset.range n, d i)
          Filter.atTop
          (nhds (∑' n : ℕ, d n)) :=
      hSummableRight.hasSum.tendsto_sum_nat
    have hAbel :
        Filter.Tendsto (fun y : ℝ => ∑' n : ℕ, d n * y ^ n)
          (nhdsWithin 1 (Set.Iio 1))
          (nhds (∑' n : ℕ, d n)) :=
      Real.tendsto_tsum_powerSeries_nhdsWithin_lt hd
    have hComp :
        Filter.Tendsto (fun x : ℝ => ∑' n : ℕ, d n * (((x - a) / R) ^ n))
          (nhdsWithin (a + R) (Set.Ioo (a - R) (a + R)))
          (nhds (∑' n : ℕ, d n)) :=
      hAbel.comp (helperForTheorem_4_3_1_tendsto_affineToUnit_right (a := a) (R := R) hRpos)
    have hRewriteFun :
        (fun x : ℝ => ∑' n : ℕ, d n * (((x - a) / R) ^ n))
          = (fun x : ℝ => ∑' n : ℕ, f.coeff n * (x - a) ^ n) := by
      funext x
      apply tsum_congr
      intro n
      dsimp [d]
      exact helperForTheorem_4_3_1_termRewrite_right (a := a) (R := R) hRpos f x n
    simpa [d, hRewriteFun] using hComp
  · intro hSummableLeft
    let d : ℕ → ℝ := fun n => f.coeff n * (-R) ^ n
    have hd :
        Filter.Tendsto
          (fun n : ℕ => ∑ i ∈ Finset.range n, d i)
          Filter.atTop
          (nhds (∑' n : ℕ, d n)) :=
      hSummableLeft.hasSum.tendsto_sum_nat
    have hAbel :
        Filter.Tendsto (fun y : ℝ => ∑' n : ℕ, d n * y ^ n)
          (nhdsWithin 1 (Set.Iio 1))
          (nhds (∑' n : ℕ, d n)) :=
      Real.tendsto_tsum_powerSeries_nhdsWithin_lt hd
    have hComp :
        Filter.Tendsto (fun x : ℝ => ∑' n : ℕ, d n * (((a - x) / R) ^ n))
          (nhdsWithin (a - R) (Set.Ioo (a - R) (a + R)))
          (nhds (∑' n : ℕ, d n)) :=
      hAbel.comp (helperForTheorem_4_3_1_tendsto_affineToUnit_left (a := a) (R := R) hRpos)
    have hRewriteFun :
        (fun x : ℝ => ∑' n : ℕ, d n * (((a - x) / R) ^ n))
          = (fun x : ℝ => ∑' n : ℕ, f.coeff n * (x - a) ^ n) := by
      funext x
      apply tsum_congr
      intro n
      dsimp [d]
      exact helperForTheorem_4_3_1_termRewrite_left (a := a) (R := R) hRpos f x n
    simpa [d, hRewriteFun] using hComp

/-- Lemma 4.3.2: For all `z₁, z₂ ∈ ℂ`, we have `z₁ * z₂ = z₂ * z₁` (equation (4.230)). -/
lemma complex_mul_comm (z₁ z₂ : ℂ) : z₁ * z₂ = z₂ * z₁ := by
  simpa using mul_comm z₁ z₂

/-- Lemma 4.3.3: For all `z₁, z₂, z₃ ∈ ℂ`, we have `(z₁ * z₂) * z₃ = z₁ * (z₂ * z₃)` (equation (4.u230)). -/
lemma complex_mul_assoc (z₁ z₂ z₃ : ℂ) : (z₁ * z₂) * z₃ = z₁ * (z₂ * z₃) := by
  simpa using mul_assoc z₁ z₂ z₃

/-- Lemma 4.3.4: For all `z ∈ ℂ`, we have `z * 1_ℂ = z` and `1_ℂ * z = z` (equation (4.u230)). -/
lemma complex_mul_one_and_one_mul (z : ℂ) : z * (1 : ℂ) = z ∧ (1 : ℂ) * z = z := by
  constructor
  · simpa using mul_one z
  · simpa using one_mul z

/-- Lemma 4.3.5: For all `z₁, z₂, z₃ ∈ ℂ`, we have
`z₁ * (z₂ + z₃) = z₁ * z₂ + z₁ * z₃` (equation (4.u230)). -/
lemma complex_mul_add_left_distrib (z₁ z₂ z₃ : ℂ) :
    z₁ * (z₂ + z₃) = z₁ * z₂ + z₁ * z₃ := by
  simpa using mul_add z₁ z₂ z₃

/-- Lemma 4.3.6: For all `z₁, z₂, z₃ ∈ ℂ`, we have
`(z₂ + z₃) * z₁ = z₂ * z₁ + z₃ * z₁` (equation (4.u230)). -/
lemma complex_add_mul_right_distrib (z₁ z₂ z₃ : ℂ) :
    (z₂ + z₃) * z₁ = z₂ * z₁ + z₃ * z₁ := by
  simpa using add_mul z₂ z₃ z₁

end Section03
end Chap04
