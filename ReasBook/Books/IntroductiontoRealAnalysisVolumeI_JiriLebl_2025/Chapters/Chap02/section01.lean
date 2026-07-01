/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open scoped BigOperators
open Metric

section Chap02
section Section01

/-- Definition 2.1.1: A sequence of real numbers is a function `x : ℕ → ℝ`,
whose `n`-th term is denoted `x n` (often written `xₙ`), and also denoted
`{x_n}_{n=1}^{\infty}`. The sequence is bounded if there exists `B : ℝ` with
`|x n| ≤ B` for all `n`. It is bounded below if there is `B` with `B ≤ x n`
for all `n`, and bounded above if there is `B` with `x n ≤ B` for all `n`. -/
abbrev RealSequence : Type :=
  ℕ → ℝ

/-- A real sequence admitting a uniform bound on absolute values. -/
def BoundedSequence (x : RealSequence) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, |x n| ≤ B

/-- A real sequence with a uniform lower bound. -/
def BoundedBelowSequence (x : RealSequence) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, B ≤ x n

/-- A real sequence with a uniform upper bound. -/
def BoundedAboveSequence (x : RealSequence) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, x n ≤ B

/-- Closed balls at the origin are described by absolute values. -/
lemma real_mem_closedBall_0_iff_abs_le (x B : ℝ) :
    x ∈ closedBall (0 : ℝ) B ↔ |x| ≤ B := by
  simp

/-- Range inclusion in a closed ball is equivalent to a uniform absolute bound. -/
lemma range_subset_closedBall_iff_abs_bound (x : ℕ → ℝ) (B : ℝ) :
    Set.range x ⊆ closedBall (0 : ℝ) B ↔ ∀ n, |x n| ≤ B := by
  constructor
  · intro h n
    have : x n ∈ closedBall (0 : ℝ) B := h ⟨n, rfl⟩
    exact (real_mem_closedBall_0_iff_abs_le (x n) B).1 this
  · intro h y hy
    rcases hy with ⟨n, rfl⟩
    exact (real_mem_closedBall_0_iff_abs_le (x n) B).2 (h n)

/-- A bounded real sequence in the book's sense is equivalent to the image of
the sequence being bounded as a subset of `ℝ`. -/
lemma boundedSequence_iff_isBounded_range (x : RealSequence) :
    BoundedSequence x ↔ Bornology.IsBounded (Set.range x) := by
  constructor
  · rintro ⟨B, hB⟩
    refine (isBounded_iff_subset_closedBall (s := Set.range x) (c := (0 : ℝ))).2 ?_
    refine ⟨B, ?_⟩
    exact (range_subset_closedBall_iff_abs_bound (x := x) (B := B)).2 hB
  · intro h
    rcases (isBounded_iff_subset_closedBall (s := Set.range x) (c := (0 : ℝ))).1 h with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact (range_subset_closedBall_iff_abs_bound (x := x) (B := B)).1 hB

/-- A sequence is bounded above exactly when its range is bounded above as a
subset of `ℝ`. -/
lemma boundedAboveSequence_iff_bddAbove_range (x : RealSequence) :
    BoundedAboveSequence x ↔ BddAbove (Set.range x) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    exact hB ⟨n, rfl⟩

/-- A sequence is bounded below exactly when its range is bounded below as a
subset of `ℝ`. -/
lemma boundedBelowSequence_iff_bddBelow_range (x : RealSequence) :
    BoundedBelowSequence x ↔ BddBelow (Set.range x) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    exact hB ⟨n, rfl⟩

/-- Definition 2.1.2: A real sequence `x` converges to `l` if for every
`ε > 0` there is an `M : ℕ` such that `|x n - l| < ε` whenever `n ≥ M`.
Such an `l` is called a limit of the sequence, and a sequence with some
limit is called convergent (otherwise divergent). -/
def ConvergesTo (x : RealSequence) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, |x n - l| < ε

/-- A real sequence is convergent if it admits a (necessarily unique) limit. -/
def ConvergentSequence (x : RealSequence) : Prop :=
  ∃ l : ℝ, ConvergesTo x l

/-- The book's ε–`M` definition of convergence agrees with the standard
`Filter.Tendsto` formulation in mathlib. -/
lemma convergesTo_iff_tendsto (x : RealSequence) (l : ℝ) :
    ConvergesTo x l ↔ Filter.Tendsto x Filter.atTop (nhds l) := by
  unfold ConvergesTo
  simpa [Real.dist_eq] using (Metric.tendsto_atTop (u := x) (a := l)).symm

/-- A constant real sequence converges to its constant value. -/
lemma constant_seq_converges (a : ℝ) :
    ConvergesTo (fun _ : ℕ => a) a := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n hn
  simpa using hε

/-- Example 2.1.3: The constant sequence `1, 1, 1, …` converges to `1`; for any
`ε > 0` one may take `M = 1`, giving `|x n - x| = |1 - 1| < ε` for every `n`. -/
lemma constant_one_converges : ConvergesTo (fun _ : ℕ => (1 : ℝ)) 1 := by
  simpa using (constant_seq_converges (1 : ℝ))

/-- Example 2.1.4: The sequence `x n = 1 / n` (starting at `n = 1`) is
convergent with limit `0`; the proof picks `M` with `1 / M < ε` by the
Archimedean property and then estimates `|x n - 0| ≤ 1 / M` for all `n ≥ M`. -/
lemma tendsto_inv_nat_succ :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
  -- mathlib limit `1 / (n + 1) → 0`
  simpa [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma inv_nat_converges_to_zero :
    ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0 := by
  -- translate to the filter-based statement and apply the standard limit
  simpa using (convergesTo_iff_tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) 0).2
    tendsto_inv_nat_succ

/-- Example 2.1.5: The alternating sign sequence `{(-1)^n}` is divergent. If it
had a limit `x`, then taking `ε = 1/2` and comparing an even term and the next
odd term would force both `|1 - x| < 1/2` and `|-1 - x| < 1/2`, which is
impossible. -/
lemma alternating_signs_diverges :
    ¬ ConvergentSequence (fun n : ℕ => (-1 : ℝ) ^ n) := by
  intro hconv
  rcases hconv with ⟨l, hl⟩
  rcases hl (1 / 2) (by norm_num) with ⟨M, hM⟩
  have h_even := hM (2 * M) (by nlinarith)
  have h_odd := hM (2 * M + 1) (by nlinarith)
  have h1 : |1 - l| < (1 / 2 : ℝ) := by
    simpa [pow_mul] using h_even
  have h2 : |-1 - l| < (1 / 2 : ℝ) := by
    simpa [pow_succ, pow_mul] using h_odd
  have hsum : (2 : ℝ) ≤ |1 - l| + |-1 - l| := by
    have hadd : |(1 - l) + (1 + l)| ≤ |1 - l| + |1 + l| := by
      simpa using (abs_add_le (1 - l) (1 + l))
    have hsum_eq : |(1 - l) + (1 + l)| = (2 : ℝ) := by
      have hinner : (1 - l) + (1 + l) = (2 : ℝ) := by ring
      have hstep : |(1 - l) + (1 + l)| = |(2 : ℝ)| := by
        simp [hinner]
      have habs : |(2 : ℝ)| = (2 : ℝ) := by norm_num
      exact hstep.trans habs
    have hrewrite : |1 + l| = |-1 - l| := by
      have hinner : -(1 + l) = -1 - l := by ring
      calc
        |1 + l| = |-(1 + l)| := by
          simpa using (abs_neg (1 + l)).symm
        _ = |-1 - l| := by
          simp [hinner]
    have : (2 : ℝ) ≤ |1 - l| + |1 + l| := by linarith
    simpa [hrewrite] using this
  have hlt : |1 - l| + |-1 - l| < (1 : ℝ) := by linarith
  linarith

/-- Proposition 2.1.6: A convergent sequence has a unique limit. If a real
sequence converges to both `l` and `l'`, then `l = l'`. -/
lemma convergesTo_unique {x : RealSequence} {l l' : ℝ}
    (h₁ : ConvergesTo x l) (h₂ : ConvergesTo x l') : l = l' := by
  classical
  have hε : ∀ ε > 0, |l - l'| < ε := by
    intro ε hε
    rcases h₁ (ε / 2) (by linarith) with ⟨M₁, hM₁⟩
    rcases h₂ (ε / 2) (by linarith) with ⟨M₂, hM₂⟩
    let M := max M₁ M₂
    have hx1 : |x M - l| < ε / 2 := by
      dsimp [M] at *
      exact hM₁ M (Nat.le_max_left _ _)
    have hx2 : |x M - l'| < ε / 2 := by
      dsimp [M] at *
      exact hM₂ M (Nat.le_max_right _ _)
    have htriangle : |l - l'| ≤ |x M - l| + |x M - l'| := by
      have h := abs_sub_le l (x M) l'
      have hswap : |l - x M| = |x M - l| := by
        simpa using (abs_sub_comm l (x M))
      simpa [hswap] using h
    have hsum : |x M - l| + |x M - l'| < ε := by linarith
    exact lt_of_le_of_lt htriangle hsum
  by_contra hneq
  have hpos : |l - l'| > 0 := abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hcontra := hε (|l - l'| / 2) (by linarith)
  linarith

/-- Proposition 2.1.7: Every convergent real sequence is bounded. -/
lemma convergentSequence_bounded {x : RealSequence}
    (hx : ConvergentSequence x) : BoundedSequence x := by
  classical
  rcases hx with ⟨l, hl⟩
  rcases hl 1 (by norm_num) with ⟨M, hM⟩
  -- choose a bound for the initial segment and the tail
  let s : Finset ℝ := (Finset.range (M + 1)).image (fun n => |x n|)
  have hs_nonempty : s.Nonempty := by
    refine ⟨|x 0|, ?_⟩
    have h0 : 0 ∈ Finset.range (M + 1) := by simp
    exact Finset.mem_image.mpr ⟨0, h0, by simp⟩
  refine ⟨max (|l| + 1) (s.max' hs_nonempty), ?_⟩
  intro n
  by_cases hlt : n < M
  · -- the initial segment is bounded by the finite supremum
    have hmem_range : n ∈ Finset.range (M + 1) :=
      Finset.mem_range.mpr (Nat.lt_trans hlt (Nat.lt_succ_self _))
    have hmem : |x n| ∈ s := by
      refine Finset.mem_image.mpr ?_
      exact ⟨n, hmem_range, rfl⟩
    have hmax' : |x n| ≤ s.max' ⟨|x n|, hmem⟩ :=
      Finset.le_max' (s := s) (x := |x n|) hmem
    have hmax : |x n| ≤ s.max' hs_nonempty := by
      simpa using hmax'
    exact le_trans hmax (le_max_right _ _)
  · -- the tail is bounded by `|l| + 1`
    have hge : n ≥ M := Nat.le_of_not_lt hlt
    have hlt1 : |x n - l| < 1 := hM n hge
    have htriangle : |x n| ≤ |x n - l| + |l| := by
      -- triangle inequality `|x n| ≤ |x n - l| + |l|`
      simpa using (abs_sub_le (x n) l 0)
    have hbound : |x n| ≤ |l| + 1 := by
      have hsum : |x n - l| + |l| < |l| + 1 := by linarith
      have hlt' : |x n| < |l| + 1 := lt_of_le_of_lt htriangle hsum
      exact le_of_lt hlt'
    exact le_trans hbound (le_max_left _ _)

lemma quadratic_fraction_abs_sub_eq (n : ℕ) :
    |((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1| =
      (n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) := by
  have hpos : 0 < ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) := by
    have hpos' : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hnonneg : 0 ≤ (n + 1 : ℝ) ^ 2 := sq_nonneg _
    exact add_pos_of_nonneg_of_pos hnonneg hpos'
  have hden_ne : ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) ≠ 0 := ne_of_gt hpos
  have hrewrite :
      ((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1 =
        -((n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ))) := by
    have hnum :
        ((n + 1 : ℝ) ^ 2 + 1) - ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) =
          -(n : ℝ) := by ring
    calc
      ((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1
          = (((n + 1 : ℝ) ^ 2 + 1) - ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ))) /
              ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) := by
              field_simp [hden_ne]
      _ = -(n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) := by simp [hnum]
      _ = -((n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ))) := by ring
  have hnonneg :
      0 ≤ (n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) :=
    div_nonneg (by exact_mod_cast Nat.zero_le n) hpos.le
  calc
    |((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1|
        = |-((n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)))| := by
            simp [hrewrite]
    _ = (n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) := by
      simp [abs_of_nonneg hnonneg]

lemma quadratic_fraction_abs_le_inv (n : ℕ) :
    |((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1| ≤
      (1 : ℝ) / (n + 1) := by
  have hpos1 : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hpos2 : 0 < (n + 2 : ℝ) := by nlinarith
  have hpos_mul : 0 < (n + 1 : ℝ) * (n + 2) := mul_pos hpos1 hpos2
  have hden_eq :
      ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) = (n + 1 : ℝ) * (n + 2) := by ring
  have hbound :
      (n : ℝ) / ((n + 1 : ℝ) * (n + 2)) ≤ (1 : ℝ) / (n + 1) := by
    have hnonzero1 : (n + 1 : ℝ) ≠ 0 := by nlinarith
    have hnonzero2 : (n + 2 : ℝ) ≠ 0 := by nlinarith
    field_simp [hnonzero1, hnonzero2]
    nlinarith
  calc
    |((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) - 1|
        = (n : ℝ) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ)) :=
      quadratic_fraction_abs_sub_eq n
    _ = (n : ℝ) / ((n + 1 : ℝ) * (n + 2)) := by simp [hden_eq]
    _ ≤ (1 : ℝ) / (n + 1) := hbound

/-- Example 2.1.8: The sequence `((n^2 + 1) / (n^2 + n))` (starting at `n = 1`)
converges to `1`; choosing `M` with `1 / M < ε` yields
`| (n^2 + 1) / (n^2 + n) - 1 | < ε` for all `n ≥ M`. -/
lemma quadratic_fraction_converges_to_one :
    ConvergesTo
      (fun n : ℕ =>
        ((n + 1 : ℝ) ^ 2 + 1) / ((n + 1 : ℝ) ^ 2 + (n + 1 : ℝ))) 1 := by
  intro ε hε
  rcases inv_nat_converges_to_zero ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hnonneg : 0 ≤ (1 : ℝ) / (n + 1) := by
    have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact div_nonneg (by norm_num) hpos.le
  have hM' : (1 : ℝ) / (n + 1) < ε := by
    have hbound : |(n + 1 : ℝ)⁻¹| < ε := by
      simpa [one_div] using hM n hn
    have hpos_inv : 0 ≤ (n + 1 : ℝ)⁻¹ := by
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact inv_nonneg.mpr hpos.le
    have hbound' : (n + 1 : ℝ)⁻¹ < ε := by
      have habs : |(n + 1 : ℝ)⁻¹| = (n + 1 : ℝ)⁻¹ := abs_of_nonneg hpos_inv
      simpa [habs] using hbound
    simpa [one_div] using hbound'
  have hbound := quadratic_fraction_abs_le_inv n
  exact lt_of_le_of_lt hbound hM'

/-- Definition 2.1.9: A sequence `{x_n}` is monotone increasing if
`x n ≤ x (n + 1)` for every `n`, monotone decreasing if `x n ≥ x (n + 1)` for
every `n`, and monotone if it is either monotone increasing or monotone
decreasing. -/
def MonotoneIncreasingSequence (x : RealSequence) : Prop :=
  ∀ n : ℕ, x n ≤ x (n + 1)

/-- A real sequence with nonincreasing successive terms. -/
def MonotoneDecreasingSequence (x : RealSequence) : Prop :=
  ∀ n : ℕ, x n ≥ x (n + 1)

/-- A real sequence that is either increasing or decreasing. -/
def MonotoneSequence (x : RealSequence) : Prop :=
  MonotoneIncreasingSequence x ∨ MonotoneDecreasingSequence x

/-- A bounded monotone increasing real sequence converges to the supremum of
its range. -/
theorem monotoneIncreasingSequence_tendsto_sup {x : RealSequence}
    (hx : MonotoneIncreasingSequence x) (hB : BoundedSequence x) :
    ConvergesTo x (sSup (Set.range x)) := by
  classical
  let S : Set ℝ := Set.range x
  have hne : S.Nonempty := ⟨x 0, ⟨0, rfl⟩⟩
  obtain ⟨B, hBabs⟩ := hB
  have hBddAbove : BddAbove S := by
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hle : x n ≤ |x n| := le_abs_self _
    exact hle.trans (hBabs n)
  have hLub : IsLUB S (sSup S) := Real.isLUB_sSup hne hBddAbove
  have hUpper : ∀ n, x n ≤ sSup S := fun n => hLub.1 ⟨n, rfl⟩
  have hmono : Monotone x := monotone_nat_of_le_succ hx
  intro ε hε
  have hεpos : 0 < ε := hε
  have hExist : ∃ M : ℕ, sSup S - ε < x M := by
    classical
    by_contra hcontra
    have hupperBound : sSup S - ε ∈ upperBounds S := by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      have hxle : ¬ sSup S - ε < x n := (not_exists.mp hcontra) n
      exact le_of_not_gt hxle
    have hle : sSup S ≤ sSup S - ε := hLub.2 hupperBound
    have hneg : ε ≤ 0 := by linarith
    exact (not_lt_of_ge hneg) hεpos
  rcases hExist with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hx_ge : x M ≤ x n := hmono hn
  have hgt : sSup S - ε < x n := lt_of_lt_of_le hM hx_ge
  have hleSup : x n ≤ sSup S := hUpper n
  have hdist : |x n - sSup S| = sSup S - x n := by
    have hnonpos : x n - sSup S ≤ 0 := sub_nonpos.mpr hleSup
    calc
      |x n - sSup S| = -(x n - sSup S) := by simpa using (abs_of_nonpos hnonpos)
      _ = sSup S - x n := by ring
  have hlt : sSup S - x n < ε := by linarith
  have : |x n - sSup S| < ε := by simpa [hdist] using hlt
  simpa [S] using this

/-- A bounded monotone decreasing real sequence converges to the infimum of
its range. -/
theorem monotoneDecreasingSequence_tendsto_inf {x : RealSequence}
    (hx : MonotoneDecreasingSequence x) (hB : BoundedSequence x) :
    ConvergesTo x (sInf (Set.range x)) := by
  classical
  let S : Set ℝ := Set.range x
  have hne : S.Nonempty := ⟨x 0, ⟨0, rfl⟩⟩
  obtain ⟨B, hBabs⟩ := hB
  have hBddBelow : BddBelow S := by
    refine ⟨-B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hpair := abs_le.mp (hBabs n)
    exact hpair.1
  have hGlb : IsGLB S (sInf S) := Real.isGLB_sInf hne hBddBelow
  have hLower : ∀ n, sInf S ≤ x n := fun n => hGlb.1 ⟨n, rfl⟩
  have hmono : Antitone x := antitone_nat_of_succ_le (by
    intro n
    simpa using hx n)
  intro ε hε
  have hεpos : 0 < ε := hε
  have hExist : ∃ M : ℕ, x M < sInf S + ε := by
    classical
    by_contra hcontra
    have hlowerBound : sInf S + ε ∈ lowerBounds S := by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      have hxge : ¬ x n < sInf S + ε := (not_exists.mp hcontra) n
      exact le_of_not_gt hxge
    have hle : sInf S + ε ≤ sInf S := hGlb.2 hlowerBound
    have hneg : ε ≤ 0 := by linarith
    exact (not_lt_of_ge hneg) hεpos
  rcases hExist with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hx_le : x n ≤ x M := hmono hn
  have hlt : x n < sInf S + ε := lt_of_le_of_lt hx_le hM
  have hge : sInf S ≤ x n := hLower n
  have hdist : |x n - sInf S| = x n - sInf S := by
    have hnonneg : 0 ≤ x n - sInf S := sub_nonneg.mpr hge
    simpa using (abs_of_nonneg hnonneg)
  have hlt' : x n - sInf S < ε := by linarith
  have : |x n - sInf S| < ε := by simpa [hdist] using hlt'
  simpa [S] using this

/-- Theorem 2.1.10 (monotone convergence theorem): A monotone sequence
`{x_n}` is bounded if and only if it is convergent. If `{x_n}` is monotone
increasing and bounded, then its limit equals `sup {x_n : n ∈ ℕ}`; if
monotone decreasing and bounded, then its limit equals `inf {x_n : n ∈ ℕ}`. -/
theorem monotone_sequence_bounded_iff_convergent {x : RealSequence}
    (hx : MonotoneSequence x) :
    BoundedSequence x ↔ ConvergentSequence x := by
  constructor
  · intro hB
    rcases hx with hinc | hdec
    · refine ⟨sSup (Set.range x), ?_⟩
      exact monotoneIncreasingSequence_tendsto_sup hinc hB
    · refine ⟨sInf (Set.range x), ?_⟩
      exact monotoneDecreasingSequence_tendsto_inf hdec hB
  · intro hconv
    exact convergentSequence_bounded hconv

/-- The book's notion of a monotone increasing sequence agrees with `Monotone`
on `ℕ`. -/
lemma monotoneIncreasingSequence_iff_monotone (x : RealSequence) :
    MonotoneIncreasingSequence x ↔ Monotone x := by
  constructor
  · intro hx
    exact monotone_nat_of_le_succ hx
  · intro hmono n
    exact hmono (Nat.le_succ n)

/-- The book's notion of a monotone decreasing sequence agrees with `Antitone`
on `ℕ`. -/
lemma monotoneDecreasingSequence_iff_antitone (x : RealSequence) :
    MonotoneDecreasingSequence x ↔ Antitone x := by
  constructor
  · intro hx
    refine antitone_nat_of_succ_le ?_
    intro n
    simpa using hx n
  · intro hanti n
    simpa using hanti (Nat.le_succ n)

/-- Example 2.1.11: The sequence `x n = 1 / √(n + 1)` is bounded below by `0`,
monotone decreasing since `√(n + 2) ≥ √(n + 1)`, and hence bounded. By the
monotone convergence theorem its limit equals its infimum, which is `0`, so
`lim_{n → ∞} 1 / √(n + 1) = 0`. -/
lemma inv_sqrt_sequence_converges :
    MonotoneDecreasingSequence (fun n : ℕ => (1 : ℝ) / Real.sqrt (n + 1)) ∧
      BoundedBelowSequence (fun n : ℕ => (1 : ℝ) / Real.sqrt (n + 1)) ∧
        ConvergesTo (fun n : ℕ => (1 : ℝ) / Real.sqrt (n + 1)) 0 := by
  classical
  set x : RealSequence := fun n : ℕ => (1 : ℝ) / Real.sqrt (n + 1)
  have hx_mono : MonotoneDecreasingSequence x := by
    intro n
    have hle : (n + 1 : ℝ) ≤ n + (1 + 1) := by nlinarith
    have hsqrt : Real.sqrt (n + 1) ≤ Real.sqrt (n + (1 + 1)) :=
      Real.sqrt_le_sqrt hle
    have hpos : 0 < Real.sqrt (n + 1) := by
      have hpos' : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact Real.sqrt_pos.2 hpos'
    have hdiv := one_div_le_one_div_of_le hpos hsqrt
    -- `one_div_le_one_div_of_le` gives the desired monotonicity
    simpa [x, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hdiv
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n
    dsimp [x]
    have hnonneg : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
    have hpos : 0 ≤ (1 : ℝ) := by norm_num
    exact div_nonneg hpos hnonneg
  have hx_lower : BoundedBelowSequence x := by
    refine ⟨0, ?_⟩
    intro n
    simpa using hx_nonneg n
  have hx_antitone : Antitone x :=
    (monotoneDecreasingSequence_iff_antitone x).1 hx_mono
  have hx_bdd : BoundedSequence x := by
    refine ⟨1, ?_⟩
    intro n
    have hle : x n ≤ x 0 := hx_antitone (Nat.zero_le n)
    have hnonneg := hx_nonneg n
    calc
      |x n| = x n := abs_of_nonneg hnonneg
      _ ≤ x 0 := hle
      _ = (1 : ℝ) := by dsimp [x]; norm_num
  have hconv_inf : ConvergesTo x (sInf (Set.range x)) :=
    monotoneDecreasingSequence_tendsto_inf hx_mono hx_bdd
  -- show `sInf (range x) = 0`
  have hne : (Set.range x).Nonempty := ⟨x 0, ⟨0, rfl⟩⟩
  have hbddBelow : BddBelow (Set.range x) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    simpa using hx_nonneg n
  have hInf := Real.isGLB_sInf hne hbddBelow
  have hLower : 0 ∈ lowerBounds (Set.range x) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact hx_nonneg n
  have hge : 0 ≤ sInf (Set.range x) := hInf.2 hLower
  -- Elements of `range x` get arbitrarily small, so the infimum is at most `0`.
  have hsmall : ∀ ε > 0, ∃ n : ℕ, x n < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
    have hposεsq : 0 < ε ^ 2 := by nlinarith
    have hpos_div : 0 < (1 / ε ^ 2 : ℝ) := by
      have hpos : 0 < ε ^ 2 := by nlinarith
      have h := inv_pos.mpr hpos
      simpa [one_div] using h
    have hN' : (1 / ε ^ 2 : ℝ) < N + 1 := by
      have hNreal : (1 / ε ^ 2 : ℝ) < N := by exact_mod_cast hN
      linarith
    have hposN1 : 0 < (N + 1 : ℝ) := by exact_mod_cast Nat.succ_pos N
    have hdiv_lt : (1 : ℝ) / (N + 1) < ε ^ 2 := by
      have h := one_div_lt_one_div_of_lt hpos_div hN'
      have hne : (ε ^ 2 : ℝ) ≠ 0 := by nlinarith
      have hrewrite : (1 : ℝ) / (1 / ε ^ 2) = ε ^ 2 := by
        field_simp [hne]
      simpa [hrewrite] using h
    have hxN_sq : (x N) ^ 2 = (1 : ℝ) / (N + 1 : ℝ) := by
      dsimp [x]
      have hnonneg : 0 ≤ (N + 1 : ℝ) := by nlinarith
      have hsqrt_sq : (Real.sqrt (N + 1)) ^ 2 = (N + 1 : ℝ) := by
        simpa using (Real.sq_sqrt hnonneg)
      calc
        ((1 : ℝ) / Real.sqrt (N + 1)) ^ 2
            = (1 : ℝ) ^ 2 / (Real.sqrt (N + 1)) ^ 2 := by
                exact div_pow (1 : ℝ) (Real.sqrt (N + 1)) 2
        _ = (1 : ℝ) / (N + 1 : ℝ) := by
              simp [hsqrt_sq]
    have hsq_lt : (x N) ^ 2 < ε ^ 2 := by simpa [hxN_sq] using hdiv_lt
    have hxN_nonneg := hx_nonneg N
    have hxN_lt : x N < ε := by
      have habs_lt : |x N| < |ε| := (sq_lt_sq).1 hsq_lt
      have hxN_abs : |x N| = x N := abs_of_nonneg hxN_nonneg
      have hε_abs : |ε| = ε := abs_of_nonneg hε.le
      simpa [hxN_abs, hε_abs] using habs_lt
    exact ⟨N, hxN_lt⟩
  have hle : sInf (Set.range x) ≤ 0 := by
    by_contra hpos
    have hεpos : 0 < sInf (Set.range x) / 2 := by linarith
    rcases hsmall _ hεpos with ⟨n, hn⟩
    have hsInf_le : sInf (Set.range x) ≤ x n := (hInf.1) ⟨n, rfl⟩
    have hlt : sInf (Set.range x) < sInf (Set.range x) / 2 :=
      lt_of_le_of_lt hsInf_le hn
    linarith
  have hsInf_eq : sInf (Set.range x) = 0 := le_antisymm hle hge
  have hconv0 : ConvergesTo x 0 := by
    simpa [hsInf_eq] using hconv_inf
  refine ⟨?_, ?_, ?_⟩
  · simpa [x] using hx_mono
  · simpa [x] using hx_lower
  · simpa [x] using hconv0

/-- Example 2.1.12: The harmonic partial sums `1 + 1/2 + … + 1/n` form a
monotone increasing sequence. Although the growth is slow, the sequence is not
bounded above and therefore does not converge; this unboundedness will be
proved later using series. -/
lemma harmonic_partial_sums_unbounded :
    MonotoneIncreasingSequence
        (fun n : ℕ =>
          Finset.sum (Finset.range (n + 1)) (fun k : ℕ => (1 : ℝ) / (k + 1))) ∧
      ¬ BoundedAboveSequence
        (fun n : ℕ =>
          Finset.sum (Finset.range (n + 1)) (fun k : ℕ => (1 : ℝ) / (k + 1))) := by
  classical
  set s : ℕ → ℝ :=
    fun n => Finset.sum (Finset.range (n + 1)) (fun k : ℕ => (1 : ℝ) / (k + 1))
  have hs_mono : MonotoneIncreasingSequence s := by
    intro n
    have hsucc :
        s (n + 1) = s n + (1 : ℝ) / (n + 2) := by
      have h :=
        (Finset.sum_range_succ (n := n + 1)
          (f := fun k : ℕ => (1 : ℝ) / (k + 1)))
      -- rewrite the sums in terms of `s`
      have hrewrite : (↑n + 1 + 1 : ℝ) = n + 2 := by ring
      simpa [s, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        one_div, hrewrite] using h
    have hpos : 0 ≤ (1 : ℝ) / (n + 2) := by
      have hpos' : 0 < (n + 2 : ℝ) := by exact_mod_cast Nat.succ_pos (n + 1)
      exact div_nonneg (by norm_num) hpos'.le
    have hle : s n ≤ s n + (1 : ℝ) / (n + 2) := by linarith
    simpa [hsucc] using hle
  refine ⟨?_, ?_⟩
  · simpa [s] using hs_mono
  · intro hB
    rcases hB with ⟨B, hB⟩
    -- consider the unshifted partial sums
    let t : ℕ → ℝ :=
      fun n => Finset.sum (Finset.range n) (fun k : ℕ => (1 : ℝ) / (k + 1))
    have ht : Filter.Tendsto t Filter.atTop Filter.atTop :=
      Real.tendsto_sum_range_one_div_nat_succ_atTop
    have hB1 := (Filter.tendsto_atTop.1 ht) (B + 1)
    rcases (Filter.eventually_atTop.1 hB1) with ⟨N, hN⟩
    have hge_t : B + 1 ≤ t N := hN N (le_rfl)
    have hsum_s :
        s N = t N + (1 : ℝ) / (N + 1) := by
      have h :=
        (Finset.sum_range_succ (n := N)
          (f := fun k : ℕ => (1 : ℝ) / (k + 1)))
      simpa [s, t, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    have hpos : 0 ≤ (1 : ℝ) / (N + 1) := by
      have hpos' : 0 < (N + 1 : ℝ) := by exact_mod_cast Nat.succ_pos N
      exact div_nonneg (by norm_num) hpos'.le
    have hge_s : B + 1 ≤ s N := by
      have hle : t N ≤ s N := by linarith [hsum_s]
      exact le_trans hge_t hle
    have hcontr := hB N
    linarith

/-- Proposition 2.1.13: For a nonempty bounded subset `S ⊆ ℝ` there are
monotone sequences `{x_n}` and `{y_n}` with terms in `S` such that
`lim_{n → ∞} x_n = sup S` and `lim_{n → ∞} y_n = inf S`. -/
lemma exists_monotone_sequences_tendsto_sup_inf {S : Set ℝ}
    (hS : S.Nonempty) (hbounded : Bornology.IsBounded S) :
    ∃ x y : RealSequence,
      (∀ n : ℕ, x n ∈ S) ∧ (∀ n : ℕ, y n ∈ S) ∧
        MonotoneIncreasingSequence x ∧ MonotoneDecreasingSequence y ∧
          ConvergesTo x (sSup S) ∧ ConvergesTo y (sInf S) := by
  classical
  have hBddAbove : BddAbove S := hbounded.bddAbove
  have hBddBelow : BddBelow S := hbounded.bddBelow
  rcases exists_seq_tendsto_sSup (α := ℝ) hS hBddAbove with ⟨x, hx_mono, hx_tendsto, hx_mem⟩
  rcases exists_seq_tendsto_sInf (α := ℝ) hS hBddBelow with ⟨y, hy_anti, hy_tendsto, hy_mem⟩
  refine ⟨x, y, hx_mem, hy_mem, ?_, ?_, ?_, ?_⟩
  · exact (monotoneIncreasingSequence_iff_monotone x).2 hx_mono
  · exact (monotoneDecreasingSequence_iff_antitone y).2 hy_anti
  · exact (convergesTo_iff_tendsto x (sSup S)).2 hx_tendsto
  · exact (convergesTo_iff_tendsto y (sInf S)).2 hy_tendsto

/-- Definition 2.1.14: For a real sequence `x` and `K ∈ ℕ`, the `K`-tail
(`tail`) is the sequence starting at the `(K+1)`-st term, written
`{x_{n+K}}_{n=1}^{∞}` or `{x_n}_{n=K+1}^{∞}`. -/
def sequenceTail (x : RealSequence) (K : ℕ) : RealSequence :=
  fun n : ℕ => x (n + (K + 1))

/-- A convergent sequence remains convergent after removing finitely many
initial terms; the limit is unchanged. -/
lemma convergesTo_tail_of_converges {x : RealSequence} {l : ℝ} (K : ℕ)
    (hx : ConvergesTo x l) : ConvergesTo (sequenceTail x K) l := by
  intro ε hε
  rcases hx ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hle : n ≤ n + (K + 1) := Nat.le_add_right _ _
  have hge : M ≤ n + (K + 1) := le_trans hn hle
  have h := hM (n + (K + 1)) hge
  simpa [sequenceTail] using h

/-- If a tail of a sequence converges, then so does the whole sequence, with
the same limit. -/
lemma convergesTo_of_tail_converges {x : RealSequence} {l : ℝ} (K : ℕ)
    (hK : ConvergesTo (sequenceTail x K) l) : ConvergesTo x l := by
  intro ε hε
  rcases hK ε hε with ⟨M', hM'⟩
  refine ⟨M' + (K + 1), ?_⟩
  intro n hn
  have hKle : K + 1 ≤ n := le_trans (Nat.le_add_left _ _) hn
  have htail : M' ≤ n - (K + 1) := (Nat.le_sub_iff_add_le hKle).2 hn
  have h := hM' (n - (K + 1)) htail
  have hrewrite : n - (K + 1) + (K + 1) = n := Nat.sub_add_cancel hKle
  simpa [sequenceTail, hrewrite] using h

/-- Proposition 2.1.15: For a real sequence `{x_n}`, the following are
equivalent: (i) the sequence converges; (ii) every `K`-tail
`{x_{n+K}}_{n=1}^{∞}` converges for all `K ∈ ℕ`; (iii) some `K`-tail converges.
Moreover, whenever these limits exist, they agree for all `K`, so
`lim_{n → ∞} x_n = lim_{n → ∞} x_{n+K}`. -/
lemma convergentSequence_iff_all_tails_converge (x : RealSequence) :
    ConvergentSequence x ↔
      ∀ K : ℕ, ConvergentSequence (sequenceTail x K) := by
  constructor
  · rintro ⟨l, hl⟩ K
    exact ⟨l, convergesTo_tail_of_converges K hl⟩
  · intro h
    have h0 := h 0
    rcases h0 with ⟨l, hl⟩
    exact ⟨l, convergesTo_of_tail_converges 0 hl⟩

/-- If some tail of a real sequence converges, then the entire sequence
converges, and conversely a convergent sequence has a convergent tail. -/
lemma convergentSequence_iff_exists_tail_converges (x : RealSequence) :
    ConvergentSequence x ↔ ∃ K : ℕ, ConvergentSequence (sequenceTail x K) := by
  constructor
  · intro hx
    rcases hx with ⟨l, hl⟩
    exact ⟨0, ⟨l, convergesTo_tail_of_converges 0 hl⟩⟩
  · rintro ⟨K, hK⟩
    rcases hK with ⟨l, hl⟩
    exact ⟨l, convergesTo_of_tail_converges K hl⟩

/-- Any limit of a sequence agrees with the limit of each of its tails. -/
lemma convergesTo_tail_limit_eq {x : RealSequence} {l l' : ℝ} (K : ℕ)
    (hx : ConvergesTo x l) (hK : ConvergesTo (sequenceTail x K) l') :
    l = l' := by
  have htail := convergesTo_tail_of_converges K hx
  exact convergesTo_unique htail hK

/-- Definition 2.1.16: Given a real sequence `{x_n}` and a strictly increasing
sequence of indices `n₁ < n₂ < n₃ < …`, the extracted sequence `i ↦ x (n i)` is
called a subsequence of `{x_n}`. -/
structure RealSubsequence (x : RealSequence) where
  /-- the strictly increasing indexing function `n_i` selecting terms of the
  original sequence -/
  indices : ℕ → ℕ
  strictlyIncreasing : StrictMono indices

/-- The indices of a subsequence eventually dominate their position:
`i ≤ n_i` for all `i`. -/
lemma subsequence_indices_ge_self {x : RealSequence} (s : RealSubsequence x) :
    ∀ i, i ≤ s.indices i := by
  intro i
  induction' i with i ih
  · exact Nat.zero_le _
  · have hlt : s.indices i < s.indices i.succ :=
      s.strictlyIncreasing (Nat.lt_succ_self i)
    have hle_succ : (s.indices i).succ ≤ s.indices i.succ :=
      Nat.succ_le_of_lt hlt
    have hle_step : i.succ ≤ (s.indices i).succ := Nat.succ_le_succ ih
    exact le_trans hle_step hle_succ

/-- The subsequence of `x` determined by the index data `s`. -/
def RealSubsequence.asSequence {x : RealSequence} (s : RealSubsequence x) :
    RealSequence :=
  fun i : ℕ => x (s.indices i)

/-- A real sequence `y` is a subsequence of `x` if it arises by composing `x`
with a strictly increasing index map. -/
def IsRealSubsequence (x y : RealSequence) : Prop :=
  ∃ s : RealSubsequence x, y = s.asSequence

/-- Proposition 2.1.17: If a real sequence `{x_n}` converges, then every
strictly increasing subsequence `{x_{n_i}}` also converges, with the same
limit as the original sequence: `lim_{n → ∞} x_n = lim_{i → ∞} x_{n_i}`. -/
lemma convergesTo_subsequence {x : RealSequence} {l : ℝ}
    (hx : ConvergesTo x l) (s : RealSubsequence x) :
    ConvergesTo (s.asSequence) l := by
  intro ε hε
  rcases hx ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro i hi
  have hindex : i ≤ s.indices i := subsequence_indices_ge_self (x := x) s i
  have hMi : M ≤ s.indices i := le_trans hi hindex
  have h := hM (s.indices i) hMi
  simpa [RealSubsequence.asSequence] using h

/-- Example 2.1.18: A sequence can have convergent subsequences without being
convergent itself. The alternating sequence `0, 1, 0, 1, …` is defined by
`x n = 0` for odd `n` and `x n = 1` for even `n`; its even-indexed subsequence
converges to `1`, its odd-indexed subsequence converges to `0`, but the
full sequence is divergent. Compare Proposition 2.1.15. -/
def alternatingZeroOneSequence : RealSequence :=
  fun n : ℕ => if n % 2 = 0 then (1 : ℝ) else 0

/-- The alternating zero–one sequence diverges, even though its even subsequence
converges to `1` and its odd subsequence converges to `0`. -/
lemma alternatingZeroOne_subsequences_converge :
    ¬ ConvergentSequence alternatingZeroOneSequence ∧
      ConvergesTo (fun i : ℕ => alternatingZeroOneSequence (2 * i)) 1 ∧
      ConvergesTo (fun i : ℕ => alternatingZeroOneSequence (2 * i + 1)) 0 := by
  -- evaluate the even and odd terms explicitly
  have h_even_eval : ∀ i : ℕ, alternatingZeroOneSequence (2 * i) = 1 := by
    intro i
    simp [alternatingZeroOneSequence]
  have h_odd_eval : ∀ i : ℕ, alternatingZeroOneSequence (2 * i + 1) = 0 := by
    intro i
    simp [alternatingZeroOneSequence, Nat.add_mod]
  -- the even subsequence is constantly `1`
  have h_even_const :
      (fun i : ℕ => alternatingZeroOneSequence (2 * i)) =
        fun _ : ℕ => (1 : ℝ) := by
    funext i
    simpa using h_even_eval i
  -- the odd subsequence is constantly `0`
  have h_odd_const :
      (fun i : ℕ => alternatingZeroOneSequence (2 * i + 1)) =
        fun _ : ℕ => (0 : ℝ) := by
    funext i
    simpa using h_odd_eval i
  -- the even subsequence converges to `1`
  have h_even_conv :
      ConvergesTo (fun i : ℕ => alternatingZeroOneSequence (2 * i)) 1 := by
    simpa [h_even_const] using (constant_seq_converges (1 : ℝ))
  -- the odd subsequence converges to `0`
  have h_odd_conv :
      ConvergesTo (fun i : ℕ => alternatingZeroOneSequence (2 * i + 1)) 0 := by
    simpa [h_odd_const] using (constant_seq_converges (0 : ℝ))
  -- the full sequence cannot converge
  have h_not_conv : ¬ ConvergentSequence alternatingZeroOneSequence := by
    intro hconv
    rcases hconv with ⟨l, hl⟩
    rcases hl (1 / 2) (by norm_num) with ⟨M, hM⟩
    have h_even := hM (2 * M) (by nlinarith)
    have h_odd := hM (2 * M + 1) (by nlinarith)
    have h1 : |1 - l| < (1 / 2 : ℝ) := by
      simpa [h_even_eval] using h_even
    have h0 : |l| < (1 / 2 : ℝ) := by
      have h0' : |0 - l| < (1 / 2 : ℝ) := by
        simpa [h_odd_eval] using h_odd
      simpa [sub_eq_add_neg] using h0'
    have htriangle : (1 : ℝ) ≤ |1 - l| + |l| := by
      have h := abs_sub_le (1 : ℝ) l 0
      -- `|1 - 0| ≤ |1 - l| + |l - 0|`
      simpa using h
    have hcontr : False := by linarith
    exact hcontr.elim
  exact ⟨h_not_conv, h_even_conv, h_odd_conv⟩

end Section01
end Chap02
