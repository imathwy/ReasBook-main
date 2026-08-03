import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Real

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators

/- Source/core/bridge triage:
- `source-facing`: Lemma 30.6 is the liminf statement for the shifted partial-sum expression
  attached to a nonnegative square-summable real series.
- `core/canonical`: the partial sums are already canonically expressed by
  `∑ k ∈ Finset.range (n + 1), ρ k`; a separate local owner adds no mathematical data.
- `bridge/view`: `Filter.liminf_nat_add` is the canonical shift-invariance bridge behind the
  textbook reindexing `σ_n * (σ_n - σ_(n - m - 1))`.

Primitive data: a real series `ρ` together with nonnegativity and square-summability.
Derived API: the shifted partial-sum expression and its liminf conclusion. -/

-- Semantic recall note: `lean_leansearch` surfaced only generic `Filter.liminf` owners, so the
-- source lemma is stated directly with explicit partial sums and an `atTop`-equivalent shift that
-- avoids truncated natural subtraction in `σ_(n - m - 1)`.

/-- Helper for Lemma 30.6: the difference of the two shifted partial sums is the fixed-length
window sum over the last `m + 1` terms. -/
private theorem shiftedPartialSumDifference_eq_windowSum
    (ρ : ℕ → ℝ) (n m : ℕ) :
    ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k) =
      ∑ j < m + 1, ρ (n + j + 1) := by
  -- Split the long partial sum into the prefix up to `n + 1` and the following `Ico` window.
  have hsplit :
      (∑ k < n + m + 2, ρ k) =
        (∑ k < n + 1, ρ k) + Finset.sum (Finset.Ico (n + 1) (n + m + 2)) ρ := by
    simpa [Nat.Iio_eq_range, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_add_sum_Ico (f := ρ) (Nat.le_add_right (n + 1) (m + 1))).symm
  calc
    ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k)
        = Finset.sum (Finset.Ico (n + 1) (n + m + 2)) ρ := by
            rw [hsplit]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ∑ j < m + 1, ρ (n + j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hlen : n + m + 2 - (n + 1) = m + 1 := by
        omega
      rw [hlen]
      simp [Nat.Iio_eq_range, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Lemma 30.6: every shifted partial sum is controlled by the global square-sum bound
via the finite Cauchy-Schwarz inequality. -/
private theorem partialSumSq_le_length_mul_squareTsumBound
    (ρ : ℕ → ℝ) (hρ_sq_summable : Summable (fun n ↦ (ρ n) ^ 2)) (m n : ℕ) :
    (∑ k < n + m + 2, ρ k) ^ 2 ≤
      (n + m + 2 : ℝ) * max 1 (∑' k, (ρ k) ^ 2) := by
  -- First bound the square of the sum by the sum of squares on the finite range.
  have hcs :
      (∑ k < n + m + 2, ρ k) ^ 2 ≤
        (n + m + 2 : ℝ) * ∑ k < n + m + 2, (ρ k) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.Iio (n + m + 2)) (f := ρ) :
        (∑ k < n + m + 2, ρ k) ^ 2 ≤
          (Finset.Iio (n + m + 2)).card * ∑ k < n + m + 2, (ρ k) ^ 2)
  -- Then compare the finite square sum with the full square-summable series.
  have hsum_le :
      ∑ k < n + m + 2, (ρ k) ^ 2 ≤ max 1 (∑' k, (ρ k) ^ 2) := by
    exact le_trans
      (Summable.sum_le_tsum (Finset.Iio (n + m + 2)) (fun _ _ ↦ sq_nonneg _) hρ_sq_summable)
      (le_max_right 1 (∑' k, (ρ k) ^ 2))
  have hlen_nonneg : 0 ≤ (n + m + 2 : ℝ) := by
    positivity
  exact le_trans hcs (mul_le_mul_of_nonneg_left hsum_le hlen_nonneg)

/-- Helper for Lemma 30.6: the sequence of fixed-window square sums stays summable because it is
a finite sum of shifted copies of the square-summable series `n ↦ (ρ n)^2`. -/
private theorem windowSquaresSummable
    (ρ : ℕ → ℝ) (hρ_sq_summable : Summable (fun n ↦ (ρ n) ^ 2)) (m : ℕ) :
    Summable (fun n ↦ ∑ j < m + 1, (ρ (n + j + 1)) ^ 2) := by
  induction m with
  | zero =>
      -- The one-term window is just the shifted square sequence.
      have hshift : Summable (fun n ↦ (ρ (n + 1)) ^ 2) :=
        (summable_nat_add_iff (f := fun n ↦ (ρ n) ^ 2) 1).2 hρ_sq_summable
      simpa [Nat.Iio_eq_range] using hshift
  | succ m hm =>
      -- Extend the window by one term and add the corresponding shifted summable sequence.
      have hmRange :
          Summable (fun n ↦ Finset.sum (Finset.range (m + 1)) (fun j ↦ (ρ (n + j + 1)) ^ 2)) := by
        simpa [Nat.Iio_eq_range] using hm
      have hshift : Summable (fun n ↦ (ρ (n + m + 2)) ^ 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (summable_nat_add_iff (f := fun n ↦ (ρ n) ^ 2) (m + 2)).2 hρ_sq_summable
      simpa [Nat.Iio_eq_range, Finset.sum_range_succ, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hmRange.add hshift

/-- Helper for Lemma 30.6: any eventual lower bound for the shifted partial-sum product must be
nonpositive. -/
private theorem eventualLowerBound_nonpos
    (ρ : ℕ → ℝ) (hρ_nonneg : ∀ n, 0 ≤ ρ n)
    (hρ_sq_summable : Summable (fun n ↦ (ρ n) ^ 2)) (m : ℕ) {b : ℝ}
    (hb :
      ∀ᶠ n in atTop,
        b ≤
          (∑ k < n + m + 2, ρ k) *
            ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k)) :
    b ≤ 0 := by
  by_contra hb_nonpos
  have hb_pos : 0 < b := lt_of_not_ge hb_nonpos
  let B : ℝ := max 1 (∑' k, (ρ k) ^ 2)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (∑' k, (ρ k) ^ 2))
  have hwindowSquaresSummable : Summable (fun n ↦ ∑ j < m + 1, (ρ (n + j + 1)) ^ 2) :=
    windowSquaresSummable ρ hρ_sq_summable m
  -- Rewrite the eventual lower bound using the window-sum identity and pass to a tail.
  have hb_window :
      ∀ᶠ n in atTop,
        b ≤
          (∑ k < n + m + 2, ρ k) * (∑ j < m + 1, ρ (n + j + 1)) := by
    refine hb.mono ?_
    intro n hn
    simpa [shiftedPartialSumDifference_eq_windowSum ρ n m] using hn
  rcases Filter.eventually_atTop.1 hb_window with ⟨N, hN⟩
  have htailSummable :
      Summable (fun n ↦ ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun n ↦ ∑ j < m + 1, (ρ (n + j + 1)) ^ 2) N).2 hwindowSquaresSummable
  -- A positive eventual lower bound forces a shifted harmonic minorant for the square-window sum.
  have hscaledHarmonicSummable :
      Summable
        (fun n : ℕ ↦ b ^ 2 / (((m + 1 : ℝ) * B) * (n + N + m + 2 : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (f := fun n ↦ ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2)
      (g := fun n : ℕ ↦ b ^ 2 / (((m + 1 : ℝ) * B) * (n + N + m + 2 : ℝ)))
      (fun n ↦ by positivity) ?_ htailSummable
    intro n
    have hb_index :
        b ≤
          (∑ k < n + N + m + 2, ρ k) * (∑ j < m + 1, ρ (n + N + j + 1)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hN (n + N) (Nat.le_add_left N n)
    have hprefix_nonneg : 0 ≤ ∑ k < n + N + m + 2, ρ k := by
      exact Finset.sum_nonneg fun k hk ↦ hρ_nonneg k
    have hwindow_nonneg : 0 ≤ ∑ j < m + 1, ρ (n + N + j + 1) := by
      exact Finset.sum_nonneg fun j hj ↦ hρ_nonneg (n + N + j + 1)
    have hwindowSq_nonneg : 0 ≤ ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2 := by
      exact Finset.sum_nonneg fun j hj ↦ sq_nonneg (ρ (n + N + j + 1))
    have hprefix_sq :
        (∑ k < n + N + m + 2, ρ k) ^ 2 ≤ (n + N + m + 2 : ℝ) * B := by
      simpa [B, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc, add_left_comm,
        add_comm] using
        partialSumSq_le_length_mul_squareTsumBound ρ hρ_sq_summable m (n + N)
    have hwindow_sq :
        (∑ j < m + 1, ρ (n + N + j + 1)) ^ 2 ≤
          (m + 1 : ℝ) * ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := Finset.Iio (m + 1))
          (f := fun j ↦ ρ (n + N + j + 1)) :
          (∑ j < m + 1, ρ (n + N + j + 1)) ^ 2 ≤
            (Finset.Iio (m + 1)).card * ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2)
    have hproduct_sq :
        b ^ 2 ≤
          ((n + N + m + 2 : ℝ) * B) * ((m + 1 : ℝ) * ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2) := by
      have hsq_mul :
          b ^ 2 ≤
            (∑ k < n + N + m + 2, ρ k) ^ 2 * (∑ j < m + 1, ρ (n + N + j + 1)) ^ 2 := by
        have :
            b ^ 2 ≤
              ((∑ k < n + N + m + 2, ρ k) * (∑ j < m + 1, ρ (n + N + j + 1))) ^ 2 := by
          nlinarith
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
      have hindex_nonneg : 0 ≤ (n + N + m + 2 : ℝ) := by
        positivity
      have hm_nonneg : 0 ≤ (m + 1 : ℝ) := by
        positivity
      have hB_nonneg : 0 ≤ B := hB_pos.le
      nlinarith
    have hdenom_pos : 0 < ((m + 1 : ℝ) * B) * (n + N + m + 2 : ℝ) := by
      positivity
    refine (div_le_iff₀ hdenom_pos).2 ?_
    calc
      b ^ 2 ≤
          ((n + N + m + 2 : ℝ) * B) * ((m + 1 : ℝ) * ∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2) :=
        hproduct_sq
      _ = (∑ j < m + 1, (ρ (n + N + j + 1)) ^ 2) * (((m + 1 : ℝ) * B) * (n + N + m + 2 : ℝ)) := by
        ac_rfl
  have hconst_ne_zero : b ^ 2 / ((m + 1 : ℝ) * B) ≠ 0 := by
    refine div_ne_zero ?_ ?_
    · exact pow_ne_zero 2 (ne_of_gt hb_pos)
    · positivity
  have hshiftedHarmonicSummable : Summable (fun n : ℕ ↦ 1 / (n + N + m + 2 : ℝ)) := by
    -- Remove the positive constant factor from the summable comparison sequence.
    refine (summable_mul_left_iff hconst_ne_zero).1 ?_
    simpa [div_eq_mul_inv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      mul_assoc, mul_left_comm, mul_comm] using hscaledHarmonicSummable
  -- This contradicts the divergence of the harmonic series after the finite shift.
  exact
    Real.not_summable_one_div_natCast <|
      (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) (N + m + 2)).1 <|
        by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc, add_left_comm,
            add_comm] using hshiftedHarmonicSummable

/-- Lemma 30.6: if `ρ : ℕ → ℝ` is nonnegative and square-summable, then for the partial sums
`σ n = ∑ k < n + 1, ρ k`, the shifted source sequence
`σ (n + m + 1) * (σ (n + m + 1) - σ n)` has limit inferior `0`. This is the `atTop` reindexing
of the textbook quantity `σ_n * (σ_n - σ_(n - m - 1))`. -/
theorem liminf_partialSums_mul_sub_partialSums_eq_zero
    (ρ : ℕ → ℝ) (hρ_nonneg : ∀ n, 0 ≤ ρ n)
    (hρ_sq_summable : Summable (fun n ↦ (ρ n) ^ 2)) (m : ℕ) :
    Filter.liminf
      (fun n ↦
        (∑ k < n + m + 2, ρ k) * ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k))
      atTop = 0 := by
  -- Route correction: keep the liminf proof short and push the contradiction argument into a
  -- separate eventual-lower-bound lemma matching the order API for `Filter.liminf`.
  let u : ℕ → ℝ := fun n ↦
    (∑ k < n + m + 2, ρ k) * ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k)
  have hnonneg : ∀ n, 0 ≤ u n := by
    intro n
    -- Both factors are nonnegative: the first is a partial sum, the second is the window sum.
    have hprefix_nonneg : 0 ≤ ∑ k < n + m + 2, ρ k := by
      exact Finset.sum_nonneg fun k hk ↦ hρ_nonneg k
    have hwindow_nonneg : 0 ≤ ∑ j < m + 1, ρ (n + j + 1) := by
      exact Finset.sum_nonneg fun j hj ↦ hρ_nonneg (n + j + 1)
    simpa [u, shiftedPartialSumDifference_eq_windowSum ρ n m] using
      mul_nonneg hprefix_nonneg hwindow_nonneg
  let S : Set ℝ := {b | ∀ᶠ n in atTop, b ≤ u n}
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [S] using (Eventually.of_forall hnonneg : ∀ᶠ n in atTop, 0 ≤ u n)
  have hS_bddAbove : BddAbove S := by
    refine ⟨0, ?_⟩
    intro b hb
    exact eventualLowerBound_nonpos ρ hρ_nonneg hρ_sq_summable m (by simpa [S] using hb)
  rw [Filter.liminf_eq]
  refine le_antisymm ?_ ?_
  · exact csSup_le hS_nonempty fun b hb ↦
      eventualLowerBound_nonpos ρ hρ_nonneg hρ_sq_summable m (by simpa [S] using hb)
  · exact le_csSup hS_bddAbove <|
      by
        simpa [S] using (Eventually.of_forall hnonneg : ∀ᶠ n in atTop, 0 ≤ u n)

/-- Helper for Theorem 30.7: every positive threshold is attained frequently by the shifted
partial-sum product from Lemma 30.6. -/
theorem partialSumsMulSubPartialSums_frequently_lt_of_pos
    (ρ : ℕ → ℝ) (hρ_nonneg : ∀ n, 0 ≤ ρ n)
    (hρ_sq_summable : Summable (fun n ↦ (ρ n) ^ 2)) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop,
      (∑ k < n + m + 2, ρ k) * ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k) < ε := by
  by_contra hε_small
  have hε_eventually_not :
      ∀ᶠ n in atTop,
        ¬ (∑ k < n + m + 2, ρ k) * ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k) < ε := by
    simpa [Filter.Frequently] using hε_small
  have hε_lower :
      ∀ᶠ n in atTop,
        ε ≤ (∑ k < n + m + 2, ρ k) * ((∑ k < n + m + 2, ρ k) - ∑ k < n + 1, ρ k) := by
    refine hε_eventually_not.mono ?_
    intro n hn
    exact not_lt.mp hn
  -- Route correction: use the owner contradiction from Lemma 30.6 directly instead of
  -- re-extracting threshold frequent-smallness from an order-theoretic `liminf` normal form.
  have hε_nonpos :=
    eventualLowerBound_nonpos ρ hρ_nonneg hρ_sq_summable m hε_lower
  linarith
