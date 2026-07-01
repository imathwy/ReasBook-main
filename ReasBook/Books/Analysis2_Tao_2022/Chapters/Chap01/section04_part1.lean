/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
  -/

import Mathlib

section Chap01
section Section04

open Filter

/-- Definition 1.16 (Subsequences): Let `(X,d)` be a metric space, let `(x^(n))_{n=m}^infty` be a
sequence in `X`, and let `(n_j)` be a strictly increasing sequence of integers with `n_j >= m`
(equivalently, `m <= n_1 < n_2 < n_3 < ...`). The sequence `(x^(n_j))_{j=1}^infty` is called a
subsequence of `(x^(n))_{n=m}^infty`. -/
def IsSubsequenceFrom {X : Type*} [MetricSpace X] (x : Nat -> X) (m : Nat) (y : Nat -> X) : Prop :=
  Exists fun n : Nat -> Nat =>
    And (StrictMono n) (And (forall j, m <= n j) (y = fun j => x (n j)))

/-- Lemma 1.2: Let `(X,d)` be a metric space, `(x^{(n)})` a sequence in `X`, and `x0 ∈ X`. If
`x^{(n)} → x0` as `n → ∞`, then for every strictly increasing sequence of indices `(n_j)`, the
subsequence `(x^{(n_j)})` converges to `x0`. -/
/- A strictly increasing subsequence of a convergent sequence has the same limit. -/
lemma tendsto_subseq_of_tendsto {X : Type*} [MetricSpace X] (x : ℕ → X) {x0 : X}
    (hx : Tendsto x atTop (nhds x0)) {n : ℕ → ℕ} (hn : StrictMono n) :
    Tendsto (fun j => x (n j)) atTop (nhds x0) := by
  simpa [Function.comp] using (hx.comp hn.tendsto_atTop)

/-- Definition 1.17 (Limit point of a sequence): Let `(X,d)` be a metric space, let `m` be a
starting index, and let `(x^(n))_{n=m}^infty` be a sequence in `X`. A point `L ∈ X` is called a
limit point of `(x^(n))_{n=m}^infty` if for every `N ≥ m` and every `ε > 0` there exists an integer
`n ≥ N` such that `d(x^(n), L) ≤ ε`. -/
def IsLimitPointSeqFrom {X : Type*} [MetricSpace X] (x : Nat → X) (m : Nat) (L : X) : Prop :=
  ∀ N ≥ m, ∀ ε > 0, ∃ n ≥ N, dist (x n) L ≤ ε

/-- A point is a limit point of a sequence from index `m` if every tail gets within any `ε > 0`. -/
lemma isLimitPointSeqFrom_iff {X : Type*} [MetricSpace X] (x : Nat → X) (m : Nat) (L : X) :
    IsLimitPointSeqFrom x m L ↔ ∀ N ≥ m, ∀ ε > 0, ∃ n ≥ N, dist (x n) L ≤ ε := by
  rfl

/-- Definition 1.18 (Cauchy sequence): Let `(X,d)` be a metric space, let `m ∈ ℕ`, and let
`(x^(n))_{n=m}^∞` be a sequence in `X`. The sequence is called a Cauchy sequence if for every
`ε > 0` there exists an integer `N ≥ m` such that `d(x^(j), x^(k)) < ε` for all `j, k ≥ N`. -/
def IsCauchySeqFrom {X : Type*} [MetricSpace X] (x : Nat → X) (m : Nat) : Prop :=
  ∀ ε > 0, ∃ N ≥ m, ∀ j ≥ N, ∀ k ≥ N, dist (x j) (x k) < ε

/-- A Cauchy sequence from index `m` gives a `CauchySeq` for the shifted tail. -/
lemma isCauchySeqFrom_imp_cauchySeq_tail {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ) :
    IsCauchySeqFrom x m → CauchySeq (fun n => x (n + m)) := by
  intro h
  refine (Metric.cauchySeq_iff).2 ?_
  intro ε hε
  rcases h ε hε with ⟨N, hNm, hN⟩
  refine ⟨N - m, ?_⟩
  intro j hj k hk
  have hj' : N ≤ j + m := (Nat.sub_le_iff_le_add).1 hj
  have hk' : N ≤ k + m := (Nat.sub_le_iff_le_add).1 hk
  exact hN (j + m) hj' (k + m) hk'

/-- A `CauchySeq` of the shifted tail yields a Cauchy sequence from index `m`. -/
lemma cauchySeq_tail_imp_isCauchySeqFrom {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ) :
    CauchySeq (fun n => x (n + m)) → IsCauchySeqFrom x m := by
  intro h
  intro ε hε
  rcases (Metric.cauchySeq_iff).1 h ε hε with ⟨N0, hN0⟩
  refine ⟨N0 + m, ?_, ?_⟩
  · exact Nat.le_add_left m N0
  · intro j hj k hk
    have hj0 : N0 ≤ j - m := Nat.le_sub_of_add_le hj
    have hk0 : N0 ≤ k - m := Nat.le_sub_of_add_le hk
    have hmj : m ≤ j := le_trans (Nat.le_add_left m N0) hj
    have hmk : m ≤ k := le_trans (Nat.le_add_left m N0) hk
    have hdist :
        dist (x ((j - m) + m)) (x ((k - m) + m)) < ε :=
      hN0 (j - m) hj0 (k - m) hk0
    have hjs : j - m + m = j := Nat.sub_add_cancel hmj
    have hks : k - m + m = k := Nat.sub_add_cancel hmk
    simpa [hjs, hks] using hdist

/-- A sequence is Cauchy from index `m` iff its shifted tail is a `CauchySeq`. -/
lemma isCauchySeqFrom_iff_cauchySeq_tail {X : Type*} [MetricSpace X] (x : Nat → X) (m : Nat) :
    IsCauchySeqFrom x m ↔ CauchySeq (fun n => x (n + m)) := by
  constructor
  · intro h
    exact isCauchySeqFrom_imp_cauchySeq_tail x m h
  · intro h
    exact cauchySeq_tail_imp_isCauchySeqFrom x m h

/-- Helper for Proposition 1.19: the bound `1/(k+1)` is always positive. -/
lemma helperForProposition_1_19_one_div_pos (k : ℕ) : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.zero_le k)
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by
    linarith
  exact (one_div_pos).2 hpos

/-- Helper for Proposition 1.19: extend the tail condition to any starting index. -/
lemma helperForProposition_1_19_extend_tail {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ)
    (L : X) (h : ∀ ε > 0, ∀ N ≥ m, ∃ n ≥ N, dist (x n) L < ε) :
    ∀ ε > 0, ∀ N, ∃ n ≥ N, dist (x n) L < ε := by
  intro ε hε N
  have hNm : m ≤ max N m := Nat.le_max_right _ _
  have hNmax : N ≤ max N m := Nat.le_max_left _ _
  rcases h ε hε (max N m) hNm with ⟨n, hn, hdist⟩
  exact ⟨n, le_trans hNmax hn, hdist⟩

/-- Helper for Proposition 1.19: a squeeze argument for the bound `1/(k+1)`. -/
lemma helperForProposition_1_19_tendsto_of_one_div_bound (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ (1 : ℝ) / ((k : ℝ) + 1)) : Tendsto f atTop (nhds 0) := by
  have hlimit :
      Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact squeeze_zero hf0 hf hlimit

/-- Proposition 1.19: Let `(X,d)` be a metric space, let `(x^(n))_{n=m}^infty` be a sequence in
`X`, and let `L ∈ X`. The following statements are equivalent: (i) for every `ε > 0` and every
`N ≥ m`, there exists `n ≥ N` such that `d(x^(n), L) < ε`; (ii) there exists a strictly increasing
sequence of integers `(n_j)_{j=1}^∞` with `n_1 ≥ m` such that `d(x^(n_j), L) → 0` as `j → ∞`. -/
/- A point `L` is a limit point of the tail iff some strictly increasing subsequence has
`dist` to `L` tending to `0`. -/
lemma limitPointSeqFrom_iff_subseq_tendsto {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ)
    (L : X) :
    (∀ ε > 0, ∀ N ≥ m, ∃ n ≥ N, dist (x n) L < ε) ↔
      ∃ n : ℕ → ℕ, StrictMono n ∧ m ≤ n 0 ∧
        Tendsto (fun j => dist (x (n j)) L) atTop (nhds 0) := by
  constructor
  · intro h
    classical
    have h' :
        ∀ ε > 0, ∀ N, ∃ n ≥ N, dist (x n) L < ε :=
      helperForProposition_1_19_extend_tail x m L h
    let chooseIndex : ℕ → ℕ → ℕ := fun k N =>
      Classical.choose
        (h' ((1 : ℝ) / ((k : ℝ) + 1)) (helperForProposition_1_19_one_div_pos k) N)
    have chooseIndex_spec :
        ∀ k N, N ≤ chooseIndex k N ∧
          dist (x (chooseIndex k N)) L < (1 : ℝ) / ((k : ℝ) + 1) := by
      intro k N
      have hspec :=
        Classical.choose_spec
          (h' ((1 : ℝ) / ((k : ℝ) + 1)) (helperForProposition_1_19_one_div_pos k) N)
      simpa [chooseIndex] using hspec
    let n : ℕ → ℕ :=
      Nat.rec (chooseIndex 0 m) (fun k nk => chooseIndex (k + 1) (nk + 1))
    have hn0 : m ≤ n 0 := by
      have hspec := chooseIndex_spec 0 m
      change m ≤ chooseIndex 0 m
      exact hspec.1
    have hn_step : ∀ k, n k + 1 ≤ n (k + 1) := by
      intro k
      have hspec := chooseIndex_spec (k + 1) (n k + 1)
      change n k + 1 ≤ chooseIndex (k + 1) (n k + 1)
      exact hspec.1
    have hlt : ∀ k, n k < n (k + 1) := by
      intro k
      have hstep := hn_step k
      have hlt' : n k < n k + 1 := Nat.lt_succ_self (n k)
      exact lt_of_lt_of_le hlt' hstep
    have hstrict : StrictMono n := strictMono_nat_of_lt_succ hlt
    have hbound : ∀ k, dist (x (n k)) L < (1 : ℝ) / ((k : ℝ) + 1) := by
      intro k
      cases k with
      | zero =>
          have hspec := chooseIndex_spec 0 m
          simpa [n] using hspec.2
      | succ k =>
          have hspec := chooseIndex_spec (k + 1) (n k + 1)
          simpa [n] using hspec.2
    have hle : ∀ k, dist (x (n k)) L ≤ (1 : ℝ) / ((k : ℝ) + 1) := by
      intro k
      exact le_of_lt (hbound k)
    have hnonneg : ∀ k, 0 ≤ dist (x (n k)) L := by
      intro k
      exact dist_nonneg
    have hTendsto :
        Tendsto (fun j => dist (x (n j)) L) atTop (nhds 0) :=
      helperForProposition_1_19_tendsto_of_one_div_bound
        (f := fun j => dist (x (n j)) L) hnonneg hle
    refine ⟨n, hstrict, hn0, hTendsto⟩
  · intro h
    rcases h with ⟨n, hn, hm, hlim⟩
    intro ε hε N hN
    have hεevent :
        ∀ᶠ j in atTop, dist (x (n j)) L < ε :=
      Filter.Tendsto.eventually_lt_const (u := ε) (v := 0) hε hlim
    have hNevent : ∀ᶠ j in atTop, N ≤ n j := by
      have htendsto : Tendsto n atTop atTop := StrictMono.tendsto_atTop hn
      rcases (tendsto_atTop_atTop.1 htendsto N) with ⟨i, hi⟩
      have hi' : ∀ j ≥ i, N ≤ n j := by
        intro j hj
        exact hi j hj
      exact (eventually_atTop.2 ⟨i, hi'⟩)
    have hboth : ∀ᶠ j in atTop, N ≤ n j ∧ dist (x (n j)) L < ε :=
      hNevent.and hεevent
    rcases (eventually_atTop.1 hboth) with ⟨j, hj⟩
    have hj' : N ≤ n j ∧ dist (x (n j)) L < ε := hj j (le_rfl)
    exact ⟨n j, hj'.1, hj'.2⟩

/-- Helper for Lemma 1.3: extend a tail distance bound to any index beyond `N0 + m`. -/
lemma helperForLemma_1_3_dist_lt_of_tail_dist_lt {X : Type*} [MetricSpace X] (x : ℕ → X)
    (m : ℕ) (x0 : X) {N0 j : ℕ} {r : ℝ}
    (h : ∀ n ≥ N0, dist (x (n + m)) x0 < r) (hj : N0 + m ≤ j) :
    dist (x j) x0 < r := by
  have hjN0 : N0 ≤ j - m := Nat.le_sub_of_add_le hj
  have hmj : m ≤ j := le_trans (Nat.le_add_left m N0) hj
  have hjdist' : dist (x ((j - m) + m)) x0 < r := h (j - m) hjN0
  have hjs : j - m + m = j := Nat.sub_add_cancel hmj
  simpa [hjs] using hjdist'

/-- Lemma 1.3 (Convergent sequences are Cauchy): Let `(X,d)` be a metric space and let
`(x^(n))_{n=m}^∞` be a sequence in `X` such that `x^(n) → x0 ∈ X` as `n → ∞`. Then
`(x^(n))_{n=m}^∞` is a Cauchy sequence, i.e., for every `ε > 0` there exists `N ≥ m` such that for
all `n, n' ≥ N` one has `d(x^(n), x^(n')) < ε`.
A convergent tail of a sequence is Cauchy from its starting index. -/
lemma convergentSeqFrom_isCauchy {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ) {x0 : X}
    (hx : Tendsto (fun n => x (n + m)) atTop (nhds x0)) : IsCauchySeqFrom x m := by
  intro ε hε
  have hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x (n + m)) x0 < ε :=
    (Metric.tendsto_atTop.1 hx)
  have hε2 : 0 < ε / 2 := by
    linarith
  rcases hconv (ε / 2) hε2 with ⟨N0, hN0⟩
  refine ⟨N0 + m, ?_, ?_⟩
  · exact Nat.le_add_left m N0
  · intro j hj k hk
    have hjdist : dist (x j) x0 < ε / 2 :=
      helperForLemma_1_3_dist_lt_of_tail_dist_lt x m x0 hN0 hj
    have hkdist : dist (x k) x0 < ε / 2 :=
      helperForLemma_1_3_dist_lt_of_tail_dist_lt x m x0 hN0 hk
    have hkdist' : dist x0 (x k) < ε / 2 := by
      have hkc : dist x0 (x k) = dist (x k) x0 := dist_comm _ _
      simpa [hkc] using hkdist
    have hsum : dist (x j) x0 + dist x0 (x k) < ε := by
      linarith [hjdist, hkdist']
    have htri : dist (x j) (x k) ≤ dist (x j) x0 + dist x0 (x k) :=
      dist_triangle (x j) x0 (x k)
    exact lt_of_le_of_lt htri hsum

/-- Helper for Lemma 1.4: a strictly increasing subsequence is eventually beyond any index. -/
lemma helperForLemma_1_4_eventually_ge_subseqIndex {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    ∃ J, ∀ j ≥ J, N ≤ n j := by
  have htendsto : Tendsto n atTop atTop := StrictMono.tendsto_atTop hn
  rcases (tendsto_atTop_atTop.1 htendsto N) with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro j hj
  exact hJ j hj

/-- Helper for Lemma 1.4: pick a subsequence index beyond `N` that is `ε`-close to `x0`. -/
lemma helperForLemma_1_4_choose_subseqIndex_close {X : Type*} [MetricSpace X] (x : ℕ → X)
    {x0 : X} {n : ℕ → ℕ} (hn : StrictMono n)
    (hsub : Tendsto (fun j => x (n j)) atTop (nhds x0)) {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ j, N ≤ n j ∧ dist (x (n j)) x0 < ε := by
  have hconv : ∀ ε > 0, ∃ J, ∀ j ≥ J, dist (x (n j)) x0 < ε :=
    Metric.tendsto_atTop.1 hsub
  rcases hconv ε hε with ⟨J0, hJ0⟩
  rcases helperForLemma_1_4_eventually_ge_subseqIndex hn N with ⟨J1, hJ1⟩
  let J := max J0 J1
  refine ⟨J, ?_, ?_⟩
  · have hJ1' : J1 ≤ J := Nat.le_max_right _ _
    exact hJ1 J hJ1'
  · have hJ0' : J0 ≤ J := Nat.le_max_left _ _
    exact hJ0 J hJ0'

/-- Lemma 1.4: Let `(X,d)` be a metric space and let `(x^{(n)})_{n=m}^∞` be a Cauchy sequence in
`X`. Suppose there exists a subsequence `(x^{(n_j)})` and a point `x0 ∈ X` such that
`x^{(n_j)} → x0` as `j → ∞`. Then `x^{(n)} → x0` as `n → ∞`. -/
lemma tendsto_of_cauchySeqFrom_of_subseq_tendsto {X : Type*} [MetricSpace X] (x : ℕ → X)
    (m : ℕ) {x0 : X} (hx : IsCauchySeqFrom x m) {n : ℕ → ℕ} (hn : StrictMono n)
    (hnm : ∀ j, m ≤ n j) (hsub : Tendsto (fun j => x (n j)) atTop (nhds x0)) :
    Tendsto (fun k => x (k + m)) atTop (nhds x0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by
    linarith
  rcases hx (ε / 2) hε2 with ⟨N0, hN0m, hN0⟩
  have hsubseq :
      ∃ j, N0 ≤ n j ∧ dist (x (n j)) x0 < ε / 2 :=
    helperForLemma_1_4_choose_subseqIndex_close (x := x) (x0 := x0) hn hsub (N := N0) hε2
  rcases hsubseq with ⟨j0, hj0N0, hj0dist⟩
  refine ⟨N0, ?_⟩
  intro k hk
  have hk' : N0 ≤ k + m := by
    exact le_trans hk (Nat.le_add_right _ _)
  have hdist1 : dist (x (k + m)) (x (n j0)) < ε / 2 :=
    hN0 (k + m) hk' (n j0) hj0N0
  have hsum : dist (x (k + m)) (x (n j0)) + dist (x (n j0)) x0 < ε := by
    linarith [hdist1, hj0dist]
  have htri :
      dist (x (k + m)) x0 ≤
        dist (x (k + m)) (x (n j0)) + dist (x (n j0)) x0 :=
    dist_triangle (x (k + m)) (x (n j0)) x0
  exact lt_of_le_of_lt htri hsum

/-- Helper for Lemma 1.5: a strictly increasing index map dominates any lower bound. -/
lemma helperForLemma_1_5_le_apply_of_le {n : ℕ → ℕ} (hn : StrictMono n) {N j : ℕ}
    (hNj : N ≤ j) : N ≤ n j := by
  have hj : j ≤ n j := hn.id_le j
  exact le_trans hNj hj

/-- Lemma 1.5 (Subsequence of Cauchy sequence is Cauchy): Let `(X,d)` be a metric space and let
`(x^(n))_{n=m}^∞` be a Cauchy sequence in `X`. Then every subsequence `(x^(n_j))_{j=1}^∞` of
`(x^(n))_{n=m}^∞` is also a Cauchy sequence. -/
/- A subsequence of a Cauchy tail is Cauchy (from index `0`). -/
lemma cauchySeqFrom_subseq {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ) (y : ℕ → X)
    (hx : IsCauchySeqFrom x m) (hsub : IsSubsequenceFrom x m y) :
    IsCauchySeqFrom y 0 := by
  rcases hsub with ⟨n, hn, hnm, rfl⟩
  intro ε hε
  rcases hx ε hε with ⟨N, hNm, hN⟩
  refine ⟨N, ?_, ?_⟩
  · exact Nat.zero_le N
  · intro j hj k hk
    have hj' : N ≤ n j := helperForLemma_1_5_le_apply_of_le hn hj
    have hk' : N ≤ n k := helperForLemma_1_5_le_apply_of_le hn hk
    exact hN (n j) hj' (n k) hk'

/-- Definition 1.19 (Complete metric space): A metric space `(X,d)` is complete if every Cauchy
sequence converges to a point of `X`, i.e., for every Cauchy sequence there exists `x ∈ X` such
that `d(x_n, x) → 0` as `n → ∞`. -/
/- A metric space is complete if every Cauchy sequence converges. -/
def IsCompleteMetricSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x : ℕ → X, CauchySeq x → ∃ L : X, Tendsto x atTop (nhds L)

/-- The book's Cauchy-sequence definition of completeness is equivalent to `CompleteSpace`. -/
theorem isCompleteMetricSpace_iff_completeSpace (X : Type*) [MetricSpace X] :
    IsCompleteMetricSpace X ↔ CompleteSpace X := by
  constructor
  · intro hX
    refine Metric.complete_of_cauchySeq_tendsto (α := X) ?_
    intro x hx
    exact hX x hx
  · intro hX
    intro x hx
    haveI : CompleteSpace X := hX
    exact cauchySeq_tendsto_of_complete hx

/-- Proposition 1.20: Let `(X,d)` be a metric space and let `Y ⊆ X` be equipped with the
subspace metric `d|_{Y×Y}`. (a) If `(Y, d|_{Y×Y})` is complete, then `Y` is closed in `X`. (b) If
`(X,d)` is complete and `Y` is closed in `X`, then `(Y, d|_{Y×Y})` is complete. -/
theorem completeSpace_subtype_closed {X : Type*} [MetricSpace X] {Y : Set X} :
    (CompleteSpace Y → IsClosed Y) ∧ (CompleteSpace X → IsClosed Y → CompleteSpace Y) := by
  constructor
  · intro hY
    have hcomp : IsComplete Y := (completeSpace_coe_iff_isComplete (s := Y)).1 hY
    exact IsComplete.isClosed hcomp
  · intro hX hY
    haveI : CompleteSpace X := hX
    have hcomp : IsComplete Y := IsClosed.isComplete hY
    exact (completeSpace_coe_iff_isComplete (s := Y)).2 hcomp

/-- Helper for Proposition 1.21: specialize the limit-point hypothesis at `N = m`. -/
lemma helperForProposition_1_21_exists_index_ge_m {X : Type*} [MetricSpace X] (x : ℕ → X)
    (m : ℕ) (L : X) (hL : ∀ ε > 0, ∀ N ≥ m, ∃ n ≥ N, dist (x n) L < ε) :
    ∀ ε > 0, ∃ n ≥ m, dist (x n) L < ε := by
  intro ε hε
  rcases hL ε hε m (le_rfl) with ⟨n, hn, hdist⟩
  exact ⟨n, hn, hdist⟩

/-- Helper for Proposition 1.21: an index `n ≥ m` gives membership in the tail set. -/
lemma helperForProposition_1_21_mem_tail_set {X : Type*} (x : ℕ → X) (m n : ℕ) (hn : n ≥ m) :
    x n ∈ {a | ∃ n ≥ m, a = x n} := by
  exact ⟨n, hn, rfl⟩

/-- Proposition 1.21: Let `(X,d)` be a metric space, let `m ∈ ℕ`, and let `(x^(n))_{n=m}^∞` be a
sequence in `X`. Let `L ∈ X`. Assume that `L` is a limit point of the sequence, i.e., for every
`ε > 0` and every `N ≥ m` there exists `n ≥ N` such that `d(x^(n), L) < ε`. Then `L` is an
adherent point of the set `A := {x^(n) : n ≥ m}`, i.e., for every `ε > 0` there exists `a ∈ A`
such that `d(a, L) < ε`.
A limit point of a tail of a sequence is an adherent point of the tail set. -/
lemma limitPointSeqFrom_adherent_point {X : Type*} [MetricSpace X] (x : ℕ → X) (m : ℕ) (L : X)
    (hL : ∀ ε > 0, ∀ N ≥ m, ∃ n ≥ N, dist (x n) L < ε) :
    ∀ ε > 0, ∃ a ∈ {a | ∃ n ≥ m, a = x n}, dist a L < ε := by
  intro ε hε
  rcases helperForProposition_1_21_exists_index_ge_m x m L hL ε hε with ⟨n, hn, hdist⟩
  refine ⟨x n, helperForProposition_1_21_mem_tail_set x m n hn, hdist⟩

/-- Proposition 1.22: Let `(X,d)` be a metric space, and let `(x_n)_{n∈ℕ}` be a Cauchy sequence
in `X`. If `x_n → x` and `x_n → y` for some `x,y ∈ X`, then `x = y`. Equivalently, a Cauchy
sequence in a metric space has at most one limit. -/
theorem cauchySeq_limit_unique {X : Type*} [MetricSpace X] (x : ℕ → X) {x0 y0 : X}
    (hx : CauchySeq x) (hx' : Tendsto x atTop (nhds x0))
    (hy' : Tendsto x atTop (nhds y0)) :
    x0 = y0 := by
  exact tendsto_nhds_unique hx' hy'

/-- A Cauchy sequence in a metric space has at most one limit. -/
lemma cauchySeq_limit_unique' {X : Type*} [MetricSpace X] (x : ℕ → X) {x0 y0 : X}
    (hx : CauchySeq x) (hx' : Tendsto x atTop (nhds x0))
    (hy' : Tendsto x atTop (nhds y0)) :
    x0 = y0 := by
  exact cauchySeq_limit_unique x hx hx' hy'

universe u

/-- Definition 1.20 (Completion via formal limits): Let `(X,d)` be a metric space. (1) For every
Cauchy sequence `(x_n)_{n=1}^∞` in `X`, introduce a formal symbol `LIM_{n→∞} x_n`. (2) Define an
equivalence relation `~` on such formal symbols by `LIM x_n ~ LIM y_n` iff
`lim_{n→∞} d(x_n,y_n) = 0`. (3) Define `X̄` to be the set of equivalence classes modulo `~`. (4)
Define `d_{X̄} : X̄ × X̄ → [0,∞)` by `d_{X̄}(LIM x_n, LIM y_n) := lim_{n→∞} d(x_n,y_n)`, where
representatives are chosen from the corresponding equivalence classes. -/
def FormalLimit (X : Type u) [MetricSpace X] : Type u :=
  { x : ℕ → X // CauchySeq x }

/-- The relation identifying two formal limits when their pointwise distance tends to `0`. -/
def FormalLimitRel (X : Type u) [MetricSpace X] (x y : FormalLimit X) : Prop :=
  Tendsto (fun n => dist (x.1 n) (y.1 n)) atTop (nhds 0)

/-- Helper for Proposition 1.23: reflexivity of the formal-limit relation. -/
lemma helperForProposition_1_23_refl (X : Type u) [MetricSpace X] (x : FormalLimit X) :
    FormalLimitRel (X := X) x x := by
  simpa [FormalLimitRel] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Helper for Proposition 1.23: symmetry of the formal-limit relation. -/
lemma helperForProposition_1_23_symm (X : Type u) [MetricSpace X] (x y : FormalLimit X) :
    FormalLimitRel (X := X) x y → FormalLimitRel (X := X) y x := by
  intro hxy
  simpa [FormalLimitRel, dist_comm] using hxy

/-- Helper for Proposition 1.23: transitivity of the formal-limit relation. -/
lemma helperForProposition_1_23_trans (X : Type u) [MetricSpace X]
    (x y z : FormalLimit X) :
    FormalLimitRel (X := X) x y → FormalLimitRel (X := X) y z →
      FormalLimitRel (X := X) x z := by
  intro hxy hyz
  have hnonneg : ∀ n, 0 ≤ dist (x.1 n) (z.1 n) := by
    intro n
    exact dist_nonneg
  have hle :
      ∀ n, dist (x.1 n) (z.1 n) ≤ dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n) := by
    intro n
    exact dist_triangle (x.1 n) (y.1 n) (z.1 n)
  have hsum :
      Tendsto (fun n => dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n)) atTop (nhds 0) := by
    simpa using hxy.add hyz
  exact squeeze_zero hnonneg hle hsum

/-- Proposition 1.23: Let `(X,d)` be a metric space, and let `C` be the set of all Cauchy
sequences in `X`. For Cauchy sequences `(x_n)` and `(y_n)` define a relation `~` on the set of
formal limits `{LIM_{n→∞} x_n : (x_n) ∈ C}` by `LIM x_n ~ LIM y_n` iff
`lim_{n→∞} d(x_n,y_n) = 0`. Then `~` is an equivalence relation. -/
/- The formal-limit relation is an equivalence relation. -/
lemma formalLimitRel_equivalence (X : Type u) [MetricSpace X] :
    Equivalence (FormalLimitRel (X := X)) := by
  constructor
  · intro x
    exact helperForProposition_1_23_refl (X := X) x
  · intro x y hxy
    exact helperForProposition_1_23_symm (X := X) x y hxy
  · intro x y z hxy hyz
    exact helperForProposition_1_23_trans (X := X) x y z hxy hyz

/-- Helper for Proposition 1.24: the setoid induced by the formal-limit relation. -/
def FormalLimitSetoid (X : Type u) [MetricSpace X] : Setoid (FormalLimit X) :=
  { r := FormalLimitRel (X := X), iseqv := formalLimitRel_equivalence (X := X) }

/-- Helper for Proposition 1.24: the completion via formal limits as a quotient of formal symbols. -/
def CompletionViaFormalLimits (X : Type u) [MetricSpace X] : Type u :=
  Quotient (FormalLimitSetoid (X := X))

/-- Helper for Proposition 1.24: the pointwise distance between two Cauchy representatives is
itself a Cauchy sequence. -/
lemma helperForProposition_1_24_distSeq_cauchy (X : Type u) [MetricSpace X] (x y : FormalLimit X) :
    CauchySeq (fun n : ℕ => dist (x.1 n) (y.1 n)) := by
  rcases (Metric.cauchySeq_iff).1 x.2 with hx
  rcases (Metric.cauchySeq_iff).1 y.2 with hy
  refine (Metric.cauchySeq_iff).2 ?_
  intro ε hε
  have hε' : 0 < ε / 2 := by
    linarith
  rcases hx (ε / 2) hε' with ⟨Nx, hNx⟩
  rcases hy (ε / 2) hε' with ⟨Ny, hNy⟩
  refine ⟨max Nx Ny, ?_⟩
  intro m hm n hn
  have hmx : Nx ≤ m := le_trans (le_max_left _ _) hm
  have hmy : Ny ≤ m := le_trans (le_max_right _ _) hm
  have hnx : Nx ≤ n := le_trans (le_max_left _ _) hn
  have hny : Ny ≤ n := le_trans (le_max_right _ _) hn
  have hxmn : dist (x.1 m) (x.1 n) < ε / 2 := hNx m hmx n hnx
  have hymn : dist (y.1 m) (y.1 n) < ε / 2 := hNy m hmy n hny
  have hle :
      dist (dist (x.1 m) (y.1 m)) (dist (x.1 n) (y.1 n)) ≤
        dist (x.1 m) (x.1 n) + dist (y.1 m) (y.1 n) := by
    exact dist_dist_dist_le (x.1 m) (y.1 m) (x.1 n) (y.1 n)
  have hsum : dist (x.1 m) (x.1 n) + dist (y.1 m) (y.1 n) < ε := by
    linarith
  exact lt_of_le_of_lt hle hsum

/-- Helper for Proposition 1.24: define the representative-level distance via `limUnder`. -/
noncomputable def helperForProposition_1_24_formalLimitDist (X : Type u) [MetricSpace X]
    (x y : FormalLimit X) : ℝ :=
  limUnder atTop (fun n : ℕ => dist (x.1 n) (y.1 n))

/-- Helper for Proposition 1.24: the representative-level distance is the limit of pointwise
distances. -/
lemma helperForProposition_1_24_formalLimitDist_tendsto (X : Type u) [MetricSpace X]
    (x y : FormalLimit X) :
    Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n)) atTop
      (nhds (helperForProposition_1_24_formalLimitDist (X := X) x y)) := by
  have hcy : CauchySeq (fun n : ℕ => dist (x.1 n) (y.1 n)) :=
    helperForProposition_1_24_distSeq_cauchy (X := X) x y
  simpa [helperForProposition_1_24_formalLimitDist] using (CauchySeq.tendsto_limUnder hcy)

/-- Helper for Proposition 1.24: the representative-level distance respects the formal-limit
equivalence relation. -/
lemma helperForProposition_1_24_formalLimitDist_congr (X : Type u) [MetricSpace X]
    (x y x' y' : FormalLimit X) :
    FormalLimitRel (X := X) x x' → FormalLimitRel (X := X) y y' →
      helperForProposition_1_24_formalLimitDist (X := X) x y =
        helperForProposition_1_24_formalLimitDist (X := X) x' y' := by
  intro hxx' hyy'
  have hnonneg :
      ∀ n, 0 ≤ dist (dist (x.1 n) (y.1 n)) (dist (x'.1 n) (y'.1 n)) := by
    intro n
    exact dist_nonneg
  have hle :
      ∀ n,
        dist (dist (x.1 n) (y.1 n)) (dist (x'.1 n) (y'.1 n)) ≤
          dist (x.1 n) (x'.1 n) + dist (y.1 n) (y'.1 n) := by
    intro n
    exact dist_dist_dist_le (x.1 n) (y.1 n) (x'.1 n) (y'.1 n)
  have hsum :
      Tendsto (fun n => dist (x.1 n) (x'.1 n) + dist (y.1 n) (y'.1 n)) atTop (nhds 0) := by
    simpa using hxx'.add hyy'
  have hdist :
      Tendsto
        (fun n =>
          dist (dist (x.1 n) (y.1 n)) (dist (x'.1 n) (y'.1 n))) atTop (nhds 0) := by
    exact squeeze_zero hnonneg hle hsum
  have hxy :
      Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x y)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x y
  have hx'y' :
      Tendsto (fun n : ℕ => dist (x'.1 n) (y'.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x' y')) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x' y'
  have hdist' :
      Tendsto
        (fun n =>
          dist (dist (x'.1 n) (y'.1 n)) (dist (x.1 n) (y.1 n))) atTop (nhds 0) := by
    simpa [dist_comm] using hdist
  have hxy_to :
      Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x' y')) := by
    exact tendsto_of_tendsto_of_dist hx'y' hdist'
  exact tendsto_nhds_unique hxy hxy_to

/-- Helper for Proposition 1.24: the distance on the formal completion, defined by limits of distances. -/
noncomputable def completionViaFormalLimitsDist (X : Type u) [MetricSpace X] :
    CompletionViaFormalLimits X → CompletionViaFormalLimits X → ℝ :=
  fun qx qy =>
    Quotient.liftOn₂ qx qy
      (fun x y => helperForProposition_1_24_formalLimitDist (X := X) x y)
      (helperForProposition_1_24_formalLimitDist_congr (X := X))

/-- Helper for Proposition 1.24: the coerced sequence of a formal limit is Cauchy in the completion. -/
lemma helperForProposition_1_24_formalLimit_coe_cauchy (X : Type u) [MetricSpace X]
    (x : FormalLimit X) :
    CauchySeq (fun n => (x.1 n : UniformSpace.Completion X)) := by
  simpa [Function.comp] using
    (UniformContinuous.comp_cauchySeq
      (UniformSpace.Completion.uniformContinuous_coe (α := X)) x.2)

/-- Helper for Proposition 1.24: send a formal limit to the limit of its coerced sequence. -/
noncomputable def helperForProposition_1_24_formalLimit_to_uniformCompletion (X : Type u)
    [MetricSpace X] (x : FormalLimit X) : UniformSpace.Completion X :=
  let hCauchy :
      CauchySeq (fun n => (x.1 n : UniformSpace.Completion X)) :=
    helperForProposition_1_24_formalLimit_coe_cauchy (X := X) x
  let _ : Nonempty (UniformSpace.Completion X) := hCauchy.1.nonempty
  limUnder atTop (fun n => (x.1 n : UniformSpace.Completion X))

/-- Helper for Proposition 1.24: the coerced sequence converges to its chosen completion point. -/
lemma helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X : Type u)
    [MetricSpace X] (x : FormalLimit X) :
    Tendsto (fun n => (x.1 n : UniformSpace.Completion X)) atTop
      (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) := by
  let hCauchy :
      CauchySeq (fun n => (x.1 n : UniformSpace.Completion X)) :=
    helperForProposition_1_24_formalLimit_coe_cauchy (X := X) x
  let _ : Nonempty (UniformSpace.Completion X) := hCauchy.1.nonempty
  have hlim :
      Tendsto (fun n => (x.1 n : UniformSpace.Completion X)) atTop
        (nhds (limUnder atTop (fun n => (x.1 n : UniformSpace.Completion X)))) :=
    CauchySeq.tendsto_limUnder hCauchy
  simpa [helperForProposition_1_24_formalLimit_to_uniformCompletion] using hlim

/-- Helper for Proposition 1.24: equivalent formal limits map to the same completion point. -/
lemma helperForProposition_1_24_formalLimit_to_uniformCompletion_congr (X : Type u)
    [MetricSpace X] (x y : FormalLimit X) :
    FormalLimitRel (X := X) x y →
      helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x =
        helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) y := by
  intro hxy
  have hx :
      Tendsto (fun n => (x.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) :=
    helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X := X) x
  have hy :
      Tendsto (fun n => (y.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) y)) :=
    helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X := X) y
  have hdist :
      Tendsto
        (fun n => dist ((x.1 n : UniformSpace.Completion X)) (y.1 n)) atTop (nhds 0) := by
    simpa [FormalLimitRel, UniformSpace.Completion.dist_eq] using hxy
  have hy_to :
      Tendsto (fun n => (y.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) :=
    tendsto_of_tendsto_of_dist hx hdist
  exact tendsto_nhds_unique hy_to hy

/-- Helper for Proposition 1.24: the map from the formal completion to the uniform completion. -/
noncomputable def helperForProposition_1_24_completion_to_uniformCompletion (X : Type u)
    [MetricSpace X] :
    CompletionViaFormalLimits X → UniformSpace.Completion X :=
  Quotient.lift (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X))
    (helperForProposition_1_24_formalLimit_to_uniformCompletion_congr (X := X))

/-- Helper for Proposition 1.24: powers of `1/2` tend to `0`. -/
lemma helperForProposition_1_24_tendsto_pow_one_half :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

/-- Helper for Proposition 1.24: powers of `1/2` are eventually below any positive threshold. -/
lemma helperForProposition_1_24_pow_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, (1 / 2 : ℝ) ^ n < ε := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) :=
    helperForProposition_1_24_tendsto_pow_one_half
  rcases (Metric.tendsto_atTop.1 hpow) ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : dist ((1 / 2 : ℝ) ^ n) 0 < ε := hN n hn
  have hdist' : |(1 / 2 : ℝ) ^ n - 0| < ε := by
    simpa [Real.dist_eq] using hdist
  have habs : |(1 / 2 : ℝ) ^ n| < ε := by
    simpa using hdist'
  exact (abs_lt.1 habs).2

/-- Helper for Proposition 1.24: the map to the uniform completion is surjective. -/
lemma helperForProposition_1_24_completion_to_uniformCompletion_surjective (X : Type u)
    [MetricSpace X] :
    Function.Surjective (helperForProposition_1_24_completion_to_uniformCompletion (X := X)) := by
  classical
  intro z
  have hDense : DenseRange ((↑) : X → UniformSpace.Completion X) :=
    UniformSpace.Completion.denseRange_coe
  have hDense' :
      ∀ z : UniformSpace.Completion X, ∀ r > 0, ∃ y : X,
        dist z (y : UniformSpace.Completion X) < r :=
    (Metric.denseRange_iff).1 hDense
  let a : ℕ → X := fun n =>
    Classical.choose
      (hDense' z ((1 / 2 : ℝ) ^ n) (pow_pos one_half_pos n))
  have ha : ∀ n, dist z (a n : UniformSpace.Completion X) < (1 / 2 : ℝ) ^ n := by
    intro n
    exact Classical.choose_spec
      (hDense' z ((1 / 2 : ℝ) ^ n) (pow_pos one_half_pos n))
  have ha_cauchy : CauchySeq a := by
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by
      linarith
    rcases helperForProposition_1_24_pow_eventually_lt (ε / 2) hε2 with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm' : dist z (a m : UniformSpace.Completion X) < ε / 2 := by
      exact lt_trans (ha m) (hN m hm)
    have hn' : dist z (a n : UniformSpace.Completion X) < ε / 2 := by
      exact lt_trans (ha n) (hN n hn)
    have hle :
        dist (a m : UniformSpace.Completion X) (a n : UniformSpace.Completion X) ≤
          dist (a m : UniformSpace.Completion X) z + dist z (a n : UniformSpace.Completion X) := by
      exact dist_triangle (a m : UniformSpace.Completion X) z (a n : UniformSpace.Completion X)
    have hm'' : dist (a m : UniformSpace.Completion X) z < ε / 2 := by
      simpa [dist_comm] using hm'
    have hsum' :
        dist (a m : UniformSpace.Completion X) z + dist z (a n : UniformSpace.Completion X) <
          ε / 2 + ε / 2 := add_lt_add hm'' hn'
    have hsum :
        dist (a m : UniformSpace.Completion X) z + dist z (a n : UniformSpace.Completion X) < ε := by
      simpa [add_halves] using hsum'
    have hlt :
        dist (a m : UniformSpace.Completion X) (a n : UniformSpace.Completion X) < ε :=
      lt_of_le_of_lt hle hsum
    simpa [UniformSpace.Completion.dist_eq] using hlt
  let x : FormalLimit X := ⟨a, ha_cauchy⟩
  refine ⟨Quotient.mk (FormalLimitSetoid (X := X)) x, ?_⟩
  have hdist :
      Tendsto (fun n => dist (a n : UniformSpace.Completion X) z) atTop (nhds 0) := by
    have hnonneg : ∀ n, 0 ≤ dist (a n : UniformSpace.Completion X) z := by
      intro n
      exact dist_nonneg
    have hle : ∀ n, dist (a n : UniformSpace.Completion X) z ≤ (1 / 2 : ℝ) ^ n := by
      intro n
      exact le_of_lt (by simpa [dist_comm] using ha n)
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) :=
      helperForProposition_1_24_tendsto_pow_one_half
    exact squeeze_zero hnonneg hle hpow
  have hlimz :
      Tendsto (fun n => (a n : UniformSpace.Completion X)) atTop (nhds z) :=
    (tendsto_iff_dist_tendsto_zero).2 hdist
  have hlimUnder :
      Tendsto (fun n => (a n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) :=
    helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X := X) x
  have hEq :
      helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x = z :=
    tendsto_nhds_unique hlimUnder hlimz
  simpa [helperForProposition_1_24_completion_to_uniformCompletion, hEq]

/-- Helper for Proposition 1.24: the map to the uniform completion is injective. -/
lemma helperForProposition_1_24_completion_to_uniformCompletion_injective (X : Type u)
    [MetricSpace X] :
    Function.Injective (helperForProposition_1_24_completion_to_uniformCompletion (X := X)) := by
  intro qx qy hxy
  refine Quotient.inductionOn₂ qx qy ?_ hxy
  intro x y hxy
  have hxy' :
      helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x =
        helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) y := by
    simpa [helperForProposition_1_24_completion_to_uniformCompletion] using hxy
  have hx :
      Tendsto (fun n => (x.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) :=
    helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X := X) x
  have hy0 :
      Tendsto (fun n => (y.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) y)) :=
    helperForProposition_1_24_formalLimit_to_uniformCompletion_tendsto (X := X) y
  have hy :
      Tendsto (fun n => (y.1 n : UniformSpace.Completion X)) atTop
        (nhds (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)) := by
    simpa [hxy'.symm] using hy0
  have hx0 :
      Tendsto
        (fun n =>
          dist ((x.1 n : UniformSpace.Completion X))
            (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x))
        atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hx
  have hy0' :
      Tendsto
        (fun n =>
          dist ((y.1 n : UniformSpace.Completion X))
            (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x))
        atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hy
  have hsum :
      Tendsto
        (fun n =>
          dist ((x.1 n : UniformSpace.Completion X))
              (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x) +
            dist ((y.1 n : UniformSpace.Completion X))
              (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x))
        atTop (nhds 0) := by
    simpa using hx0.add hy0'
  have hnonneg :
      ∀ n, 0 ≤ dist ((x.1 n : UniformSpace.Completion X)) (y.1 n) := by
    intro n
    exact dist_nonneg
  have hle :
      ∀ n,
        dist ((x.1 n : UniformSpace.Completion X)) (y.1 n) ≤
          dist ((x.1 n : UniformSpace.Completion X))
              (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x) +
            dist ((y.1 n : UniformSpace.Completion X))
              (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x) := by
    intro n
    have hle' :
        dist ((x.1 n : UniformSpace.Completion X)) (y.1 n) ≤
          dist ((x.1 n : UniformSpace.Completion X))
              (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x) +
            dist (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)
              (y.1 n : UniformSpace.Completion X) := by
      exact dist_triangle (x.1 n : UniformSpace.Completion X)
        (helperForProposition_1_24_formalLimit_to_uniformCompletion (X := X) x)
        (y.1 n : UniformSpace.Completion X)
    simpa [dist_comm] using hle'
  have hdist :
      Tendsto
        (fun n => dist ((x.1 n : UniformSpace.Completion X)) (y.1 n)) atTop (nhds 0) :=
    squeeze_zero hnonneg hle hsum
  have hdist' :
      Tendsto (fun n => dist (x.1 n) (y.1 n)) atTop (nhds 0) := by
    simpa [UniformSpace.Completion.dist_eq] using hdist
  have hrel : FormalLimitRel (X := X) x y := hdist'
  exact Quotient.sound hrel

/-- Helper for Proposition 1.24: the formal-limit completion is (noncanonically) equivalent to the
uniform completion. -/
theorem completionViaFormalLimits_equiv_uniformCompletion (X : Type u) [MetricSpace X] :
    Nonempty (CompletionViaFormalLimits X ≃ UniformSpace.Completion X) := by
  refine ⟨Equiv.ofBijective (helperForProposition_1_24_completion_to_uniformCompletion (X := X))
    ⟨helperForProposition_1_24_completion_to_uniformCompletion_injective (X := X),
      helperForProposition_1_24_completion_to_uniformCompletion_surjective (X := X)⟩⟩

/-- Helper for Proposition 1.24: `dist` vanishes on identical classes. -/
lemma helperForProposition_1_24_completionDist_self (X : Type u) [MetricSpace X] :
    ∀ q : CompletionViaFormalLimits X, completionViaFormalLimitsDist X q q = 0 := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  have hlim :
      helperForProposition_1_24_formalLimitDist (X := X) x x = (0 : ℝ) := by
    have h1 :
        Tendsto (fun n : ℕ => dist (x.1 n) (x.1 n)) atTop
          (nhds (helperForProposition_1_24_formalLimitDist (X := X) x x)) := by
      exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x x
    have h0 :
        Tendsto (fun n : ℕ => dist (x.1 n) (x.1 n)) atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    exact tendsto_nhds_unique h1 h0
  simpa [completionViaFormalLimitsDist, hlim]

/-- Helper for Proposition 1.24: the formal-limit distance is symmetric. -/
lemma helperForProposition_1_24_completionDist_comm (X : Type u) [MetricSpace X] :
    ∀ qx qy : CompletionViaFormalLimits X,
      completionViaFormalLimitsDist X qx qy = completionViaFormalLimitsDist X qy qx := by
  intro qx qy
  refine Quotient.inductionOn₂ qx qy ?_
  intro x y
  have h1 :
      Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x y)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x y
  have h2 :
      Tendsto (fun n : ℕ => dist (y.1 n) (x.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) y x)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) y x
  have hcomm :
      helperForProposition_1_24_formalLimitDist (X := X) x y =
        helperForProposition_1_24_formalLimitDist (X := X) y x := by
    apply tendsto_nhds_unique h1
    simpa [dist_comm] using h2
  simpa [completionViaFormalLimitsDist, hcomm]

/-- Helper for Proposition 1.24: the formal-limit distance satisfies the triangle inequality. -/
lemma helperForProposition_1_24_completionDist_triangle (X : Type u) [MetricSpace X] :
    ∀ qx qy qz : CompletionViaFormalLimits X,
      completionViaFormalLimitsDist X qx qz ≤
        completionViaFormalLimitsDist X qx qy + completionViaFormalLimitsDist X qy qz := by
  intro qx qy qz
  refine Quotient.inductionOn₃ qx qy qz ?_
  intro x y z
  have hleft :
      Tendsto (fun n : ℕ => dist (x.1 n) (z.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x z)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x z
  have hright :
      Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n)) atTop
        (nhds
          (helperForProposition_1_24_formalLimitDist (X := X) x y +
            helperForProposition_1_24_formalLimitDist (X := X) y z)) := by
    exact (helperForProposition_1_24_formalLimitDist_tendsto (X := X) x y).add
      (helperForProposition_1_24_formalLimitDist_tendsto (X := X) y z)
  have hle :
      Filter.Eventually
        (fun n =>
          dist (x.1 n) (z.1 n) ≤ dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n))
        atTop := by
    exact Filter.Eventually.of_forall (fun n =>
      dist_triangle (x.1 n) (y.1 n) (z.1 n))
  have hlim :
      helperForProposition_1_24_formalLimitDist (X := X) x z ≤
        helperForProposition_1_24_formalLimitDist (X := X) x y +
          helperForProposition_1_24_formalLimitDist (X := X) y z :=
    tendsto_le_of_eventuallyLE hleft hright hle
  simpa [completionViaFormalLimitsDist] using hlim

/-- Helper for Proposition 1.24: distance zero gives equality in the quotient. -/
lemma helperForProposition_1_24_completionDist_eq_zero (X : Type u) [MetricSpace X] :
    ∀ {qx qy : CompletionViaFormalLimits X},
      completionViaFormalLimitsDist X qx qy = 0 → qx = qy := by
  intro qx qy
  refine Quotient.inductionOn₂ qx qy ?_
  intro x y hxy
  have hxy' :
      helperForProposition_1_24_formalLimitDist (X := X) x y = (0 : ℝ) := by
    simpa [completionViaFormalLimitsDist] using hxy
  have hrel : FormalLimitRel (X := X) x y := by
    have hlim :
        Tendsto (fun n : ℕ => dist (x.1 n) (y.1 n)) atTop
          (nhds (helperForProposition_1_24_formalLimitDist (X := X) x y)) := by
      exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x y
    simpa [FormalLimitRel, hxy'] using hlim
  exact Quotient.sound hrel

/-- Helper for Proposition 1.24: the `edist` field is `ENNReal.ofReal` of the distance. -/
lemma helperForProposition_1_24_completion_edist_dist (X : Type u) [MetricSpace X] :
    ∀ x y : CompletionViaFormalLimits X,
      (fun a b => ENNReal.ofReal (completionViaFormalLimitsDist X a b)) x y =
        ENNReal.ofReal (completionViaFormalLimitsDist X x y) := by
  intro x y
  rfl

/-- Helper for Proposition 1.24: the pseudo-metric structure on the formal completion. -/
noncomputable def helperForProposition_1_24_completionPseudoMetricSpace (X : Type u)
    [MetricSpace X] : PseudoMetricSpace (CompletionViaFormalLimits X) :=
  { dist := completionViaFormalLimitsDist X
    dist_self := helperForProposition_1_24_completionDist_self (X := X)
    dist_comm := helperForProposition_1_24_completionDist_comm (X := X)
    dist_triangle := helperForProposition_1_24_completionDist_triangle (X := X)
    edist := fun x y => ENNReal.ofReal (completionViaFormalLimitsDist X x y)
    edist_dist := helperForProposition_1_24_completion_edist_dist (X := X)
    toUniformSpace :=
      UniformSpace.ofDist (completionViaFormalLimitsDist X)
        (helperForProposition_1_24_completionDist_self (X := X))
        (helperForProposition_1_24_completionDist_comm (X := X))
        (helperForProposition_1_24_completionDist_triangle (X := X))
    toBornology :=
      Bornology.ofDist (completionViaFormalLimitsDist X)
        (helperForProposition_1_24_completionDist_comm (X := X))
        (helperForProposition_1_24_completionDist_triangle (X := X)) }

/-- Helper for Proposition 1.24: the formal-limit completion carries a metric-space structure. -/
noncomputable def helperForProposition_1_24_completionMetricSpace (X : Type u) [MetricSpace X] :
    MetricSpace (CompletionViaFormalLimits X) :=
  MetricSpace.mk
    (toPseudoMetricSpace := helperForProposition_1_24_completionPseudoMetricSpace (X := X))
    (helperForProposition_1_24_completionDist_eq_zero (X := X))

/-- Proposition 1.24: Let `(X,d)` be a metric space. Define `X̄` as the set of equivalence classes
of Cauchy sequences in `X`, where two Cauchy sequences `(x_n)` and `(y_n)` are equivalent if
`d(x_n,y_n) → 0` as `n → ∞`. For classes `[(x_n)], [(y_n)] ∈ X̄`, define
`d_{X̄}([(x_n)],[(y_n)]) := lim_{n→∞} d(x_n,y_n)`. Then `d_{X̄}` is well-defined and
`(X̄, d_{X̄})` is a metric space. -/
theorem completionViaFormalLimitsDist_wellDefined_and_metricSpace (X : Type u) [MetricSpace X] :
    (∀ x y x' y' : FormalLimit X,
      FormalLimitRel (X := X) x x' → FormalLimitRel (X := X) y y' →
        completionViaFormalLimitsDist X
            (Quotient.mk (FormalLimitSetoid (X := X)) x)
            (Quotient.mk (FormalLimitSetoid (X := X)) y) =
          completionViaFormalLimitsDist X
            (Quotient.mk (FormalLimitSetoid (X := X)) x')
            (Quotient.mk (FormalLimitSetoid (X := X)) y')) ∧
    Nonempty (MetricSpace (CompletionViaFormalLimits X)) := by
  refine And.intro ?_ ?_
  · intro x y x' y' hxx' hyy'
    simpa [completionViaFormalLimitsDist] using
      (helperForProposition_1_24_formalLimitDist_congr (X := X) x y x' y' hxx' hyy')
  · exact ⟨helperForProposition_1_24_completionMetricSpace (X := X)⟩

/-- Helper for Proposition 1.24: the formal-limit distance does not depend on the chosen Cauchy
representatives. -/
lemma completionViaFormalLimitsDist_wellDefined (X : Type u) [MetricSpace X] :
    ∀ x y x' y' : FormalLimit X,
      FormalLimitRel (X := X) x x' → FormalLimitRel (X := X) y y' →
        completionViaFormalLimitsDist X
            (Quotient.mk (FormalLimitSetoid (X := X)) x)
            (Quotient.mk (FormalLimitSetoid (X := X)) y) =
          completionViaFormalLimitsDist X
            (Quotient.mk (FormalLimitSetoid (X := X)) x')
            (Quotient.mk (FormalLimitSetoid (X := X)) y') := by
  intro x y x' y' hxx' hyy'
  simpa [completionViaFormalLimitsDist] using
    (helperForProposition_1_24_formalLimitDist_congr (X := X) x y x' y' hxx' hyy')

/-- Helper for Proposition 1.24: the formal-limit completion carries a metric-space structure via
the formal-limit distance. -/
noncomputable instance completionViaFormalLimitsMetricSpace (X : Type u) [MetricSpace X] :
    MetricSpace (CompletionViaFormalLimits X) :=
  helperForProposition_1_24_completionMetricSpace (X := X)

/-- Helper for Theorem 1.4: choose representatives for a sequence in the quotient. -/
lemma helperForTheorem_1_4_chooseRepresentatives (X : Type u) [MetricSpace X]
    (u : ℕ → CompletionViaFormalLimits X) :
    ∃ x : ℕ → FormalLimit X,
      ∀ n, u n = Quotient.mk (FormalLimitSetoid (X := X)) (x n) := by
  classical
  refine ⟨fun n => Quotient.out (u n), ?_⟩
  intro n
  simpa using (Quotient.out_eq (u n)).symm

/-- Helper for Theorem 1.4: reindexing a Cauchy representative stays Cauchy. -/
lemma helperForTheorem_1_4_reindex_cauchy (X : Type u) [MetricSpace X]
    (z : FormalLimit X) {m : ℕ → ℕ} (hm : StrictMono m) :
    CauchySeq (fun n => z.1 (m n)) := by
  exact z.2.comp_tendsto hm.tendsto_atTop

/-- Helper for Theorem 1.4: a formal limit is equivalent to any strictly monotone reindexing. -/
lemma helperForTheorem_1_4_equiv_reindex (X : Type u) [MetricSpace X]
    (z : FormalLimit X) {m : ℕ → ℕ} (hm : StrictMono m) :
    FormalLimitRel (X := X) z
      ⟨fun n => z.1 (m n), helperForTheorem_1_4_reindex_cauchy (X := X) z hm⟩ := by
  have hz : CauchySeq z.1 := z.2
  have hz' := Metric.cauchySeq_iff.1 hz
  refine (Metric.tendsto_atTop.2 ?_)
  intro ε hε
  rcases hz' ε hε with ⟨N, hN⟩
  have htendsto : Tendsto m atTop atTop := hm.tendsto_atTop
  rcases (tendsto_atTop_atTop.1 htendsto N) with ⟨K, hK⟩
  refine ⟨max N K, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnK : K ≤ n := le_trans (le_max_right _ _) hn
  have hmN : N ≤ m n := hK n hnK
  have hdist : dist (z.1 n) (z.1 (m n)) < ε := hN n hnN (m n) hmN
  simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hdist

/-- Helper for Theorem 1.4: if the formal-limit distance is below `r`, then pointwise distances are eventually below `r`. -/
lemma helperForTheorem_1_4_eventually_dist_lt (X : Type u) [MetricSpace X]
    {x y : FormalLimit X} {r : ℝ}
    (h : helperForProposition_1_24_formalLimitDist (X := X) x y < r) :
    ∃ N, ∀ n ≥ N, dist (x.1 n) (y.1 n) < r := by
  have hlim :
      Tendsto (fun n => dist (x.1 n) (y.1 n)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) x y)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x y
  have hε :
      0 < r - helperForProposition_1_24_formalLimitDist (X := X) x y := by
    exact sub_pos.mpr h
  rcases (Metric.tendsto_atTop.1 hlim)
      (r - helperForProposition_1_24_formalLimitDist (X := X) x y) hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdist :
      dist (dist (x.1 n) (y.1 n))
          (helperForProposition_1_24_formalLimitDist (X := X) x y) <
        r - helperForProposition_1_24_formalLimitDist (X := X) x y := hN n hn
  have hdist' :
      |dist (x.1 n) (y.1 n) -
          helperForProposition_1_24_formalLimitDist (X := X) x y| <
        r - helperForProposition_1_24_formalLimitDist (X := X) x y := by
    simpa [Real.dist_eq] using hdist
  have hupper :
      dist (x.1 n) (y.1 n) -
          helperForProposition_1_24_formalLimitDist (X := X) x y <
        r - helperForProposition_1_24_formalLimitDist (X := X) x y := (abs_lt.1 hdist').2
  linarith

/-- Helper for Theorem 1.4: powers of `1/2` are eventually below any positive threshold. -/
lemma helperForTheorem_1_4_pow_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, (1 / 2 : ℝ) ^ (n + 2) < ε := by
  have hpow' : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) := by
    exact
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) atTop (nhds (0 : ℝ)) := by
    exact hpow'.comp (tendsto_add_atTop_nat 2)
  rcases (Metric.tendsto_atTop.1 hpow) ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : dist ((1 / 2 : ℝ) ^ (n + 2)) 0 < ε := hN n hn
  have hdist' : |(1 / 2 : ℝ) ^ (n + 2) - 0| < ε := by
    simpa [Real.dist_eq] using hdist
  have habs : |(1 / 2 : ℝ) ^ (n + 2)| < ε := by
    simpa using hdist'
  exact (abs_lt.1 habs).2

/-- Helper for Theorem 1.4: extract a geometric subsequence of a Cauchy sequence in the completion. -/
lemma helperForTheorem_1_4_cauchySeq_subseq_geometric (X : Type u) [MetricSpace X]
    (u : ℕ → CompletionViaFormalLimits X) (hu : CauchySeq u) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      ∀ n, dist (u (m n)) (u (m (n + 1))) < (1 / 2 : ℝ) ^ (n + 2) := by
  classical
  have hCauchy := (Metric.cauchySeq_iff).1 hu
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2)
  have hrpos : ∀ n, 0 < r n := by
    intro n
    have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by
      norm_num
    exact pow_pos hhalf (n + 2)
  let N : ℕ → ℕ := fun n => Classical.choose (hCauchy (r n) (hrpos n))
  have hN :
      ∀ n, ∀ j ≥ N n, ∀ k ≥ N n, dist (u j) (u k) < r n := by
    intro n
    exact Classical.choose_spec (hCauchy (r n) (hrpos n))
  let m : ℕ → ℕ :=
    Nat.rec (N 0) (fun n mn => max (mn + 1) (N (n + 1)))
  have hm_step : ∀ n, m n + 1 ≤ m (n + 1) := by
    intro n
    have hle : m n + 1 ≤ max (m n + 1) (N (n + 1)) := le_max_left _ _
    simpa [m] using hle
  have hm_lt : ∀ n, m n < m (n + 1) := by
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (m n)) (hm_step n)
  have hm_strict : StrictMono m := strictMono_nat_of_lt_succ hm_lt
  have hm_ge : ∀ n, N n ≤ m n := by
    intro n
    cases n with
    | zero =>
        simp [m]
    | succ n =>
        have hle : N (n + 1) ≤ max (m n + 1) (N (n + 1)) := le_max_right _ _
        simpa [m] using hle
  refine ⟨m, hm_strict, ?_⟩
  intro n
  have hmN : N n ≤ m n := hm_ge n
  have hmN' : N n ≤ m (n + 1) := by
    have hle : m n + 1 ≤ m (n + 1) := hm_step n
    have hle' : N n ≤ m n + 1 := Nat.le_succ_of_le hmN
    exact le_trans hle' hle
  exact hN n (m n) hmN (m (n + 1)) hmN'

/-- Helper for Theorem 1.4: build a monotone diagonal index with pointwise control. -/
lemma helperForTheorem_1_4_diagonal_index (X : Type u) [MetricSpace X]
    {u : ℕ → CompletionViaFormalLimits X} {m : ℕ → ℕ}
    {x : ℕ → FormalLimit X}
    (hx : ∀ n, u (m n) = Quotient.mk (FormalLimitSetoid (X := X)) (x n))
    (hsmall : ∀ n, dist (u (m n)) (u (m (n + 1))) < (1 / 2 : ℝ) ^ (n + 2)) :
    ∃ k : ℕ → ℕ, Monotone k ∧
      (∀ n, ∀ j ≥ k n, dist ((x n).1 j) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2)) ∧
      (∀ n, ∀ j ≥ k n,
        dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2)) := by
  classical
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2)
  have hdist_rep :
      ∀ n, helperForProposition_1_24_formalLimitDist (X := X) (x n) (x (n + 1)) < r n := by
    intro n
    have hsmall' :
        completionViaFormalLimitsDist X (u (m n)) (u (m (n + 1))) < r n := by
      simpa [r] using hsmall n
    simpa [completionViaFormalLimitsDist, hx n, hx (n + 1)] using hsmall'
  let N1 : ℕ → ℕ := fun n =>
    Classical.choose
      (helperForTheorem_1_4_eventually_dist_lt (X := X)
        (x := x n) (y := x (n + 1)) (r := r n) (hdist_rep n))
  have hN1 :
      ∀ n, ∀ j ≥ N1 n, dist ((x n).1 j) ((x (n + 1)).1 j) < r n := by
    intro n
    exact Classical.choose_spec
      (helperForTheorem_1_4_eventually_dist_lt (X := X)
        (x := x n) (y := x (n + 1)) (r := r n) (hdist_rep n))
  have hrpos : ∀ n, 0 < r n := by
    intro n
    have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by
      norm_num
    exact pow_pos hhalf (n + 2)
  have hCauchy : ∀ n, CauchySeq (x (n + 1)).1 := by
    intro n
    exact (x (n + 1)).2
  have hCauchy' :
      ∀ n, ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N,
        dist ((x (n + 1)).1 j) ((x (n + 1)).1 k) < ε := by
    intro n
    exact (Metric.cauchySeq_iff).1 (hCauchy n)
  let N2 : ℕ → ℕ := fun n => Classical.choose (hCauchy' n (r n) (hrpos n))
  have hN2 :
      ∀ n, ∀ j ≥ N2 n, ∀ k ≥ N2 n,
        dist ((x (n + 1)).1 j) ((x (n + 1)).1 k) < r n := by
    intro n
    exact Classical.choose_spec (hCauchy' n (r n) (hrpos n))
  let k : ℕ → ℕ :=
    Nat.rec (max (N1 0) (N2 0))
      (fun n kn => max kn (max (N1 (n + 1)) (N2 (n + 1))))
  have hk_step : ∀ n, k n ≤ k (n + 1) := by
    intro n
    have hle : k n ≤ max (k n) (max (N1 (n + 1)) (N2 (n + 1))) := le_max_left _ _
    simpa [k] using hle
  have hkmono : Monotone k := monotone_nat_of_le_succ hk_step
  have hk_ge_N1 : ∀ n, N1 n ≤ k n := by
    intro n
    cases n with
    | zero =>
        simp [k]
    | succ n =>
        have hle : N1 (n + 1) ≤ max (k n) (max (N1 (n + 1)) (N2 (n + 1))) := by
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        simpa [k] using hle
  have hk_ge_N2 : ∀ n, N2 n ≤ k n := by
    intro n
    cases n with
    | zero =>
        simp [k]
    | succ n =>
        have hle : N2 (n + 1) ≤ max (k n) (max (N1 (n + 1)) (N2 (n + 1))) := by
          exact le_trans (le_max_right _ _) (le_max_right _ _)
        simpa [k] using hle
  refine ⟨k, hkmono, ?_, ?_⟩
  · intro n j hj
    have hN1' : N1 n ≤ j := le_trans (hk_ge_N1 n) hj
    exact hN1 n j hN1'
  · intro n j hj
    have hN2' : N2 n ≤ k n := hk_ge_N2 n
    have hN2j : N2 n ≤ j := le_trans hN2' hj
    exact hN2 n (k n) hN2' j hN2j

/-- Helper for Theorem 1.4: the diagonal sequence is Cauchy. -/
lemma helperForTheorem_1_4_diagonal_cauchy (X : Type u) [MetricSpace X]
    {x : ℕ → FormalLimit X} {k : ℕ → ℕ} (hkmono : Monotone k)
    (hA : ∀ n, ∀ j ≥ k n,
      dist ((x n).1 j) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2))
    (hB : ∀ n, ∀ j ≥ k n,
      dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2)) :
    CauchySeq (fun n => (x n).1 (k n)) := by
  have hhalf : (1 / 2 : ℝ) < 1 := by
    norm_num
  have hdist_le :
      ∀ n, dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    have hkn : k n ≤ k (n + 1) := hkmono (Nat.le_succ n)
    have hA' : dist ((x n).1 (k n)) ((x (n + 1)).1 (k n)) < (1 / 2 : ℝ) ^ (n + 2) :=
      hA n (k n) (le_rfl)
    have hB' :
        dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 (k (n + 1))) <
          (1 / 2 : ℝ) ^ (n + 2) := by
      simpa using hB n (k (n + 1)) hkn
    have htri :
        dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) ≤
          dist ((x n).1 (k n)) ((x (n + 1)).1 (k n)) +
            dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 (k (n + 1))) :=
      dist_triangle _ _ _
    have hsum :
        dist ((x n).1 (k n)) ((x (n + 1)).1 (k n)) +
          dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 (k (n + 1))) <
            2 * (1 / 2 : ℝ) ^ (n + 2) := by
      linarith [hA', hB']
    have hlt :
        dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) <
          2 * (1 / 2 : ℝ) ^ (n + 2) := lt_of_le_of_lt htri hsum
    have hpow :
        2 * (1 / 2 : ℝ) ^ (n + 2) = (1 / 2 : ℝ) ^ (n + 1) := by
      calc
        2 * (1 / 2 : ℝ) ^ (n + 2) =
            2 * ((1 / 2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ)) := by
          simp [pow_succ]
        _ = (1 / 2 : ℝ) ^ (n + 1) * ((1 / 2 : ℝ) * 2) := by
          ring
        _ = (1 / 2 : ℝ) ^ (n + 1) := by
          have htwo : (1 / 2 : ℝ) * 2 = 1 := by
            norm_num
          simp [htwo, mul_assoc, mul_left_comm, mul_comm]
    have hlt' :
        dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) < (1 / 2 : ℝ) ^ (n + 1) := by
      calc
        dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) <
            2 * (1 / 2 : ℝ) ^ (n + 2) := hlt
        _ = (1 / 2 : ℝ) ^ (n + 1) := hpow
    exact le_of_lt hlt'
  refine cauchySeq_of_le_geometric (r := (1 / 2 : ℝ)) (C := (1 / 2 : ℝ)) hhalf ?_
  intro n
  have hdist : dist ((x n).1 (k n)) ((x (n + 1)).1 (k (n + 1))) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    hdist_le n
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hdist

/-- Helper for Theorem 1.4: a Cauchy sequence with a convergent subsequence converges. -/
lemma helperForTheorem_1_4_tendsto_of_cauchy_of_subseq {X : Type u} [MetricSpace X]
    {u : ℕ → X} (hu : CauchySeq u) {m : ℕ → ℕ} (hm : StrictMono m) {a : X}
    (hsub : Tendsto (fun n => u (m n)) atTop (nhds a)) :
    Tendsto u atTop (nhds a) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by
    linarith
  have hCauchy := (Metric.cauchySeq_iff).1 hu
  rcases hCauchy (ε / 2) hε2 with ⟨N0, hN0⟩
  have hsub' : ∀ ε > 0, ∃ J, ∀ j ≥ J, dist (u (m j)) a < ε :=
    (Metric.tendsto_atTop.1 hsub)
  rcases hsub' (ε / 2) hε2 with ⟨J0, hJ0⟩
  rcases helperForLemma_1_4_eventually_ge_subseqIndex hm N0 with ⟨J1, hJ1⟩
  let J := max J0 J1
  have hJ0' : J0 ≤ J := Nat.le_max_left _ _
  have hJ1' : J1 ≤ J := Nat.le_max_right _ _
  have hJN0 : N0 ≤ m J := hJ1 J hJ1'
  refine ⟨m J, ?_⟩
  intro n hn
  have hnN0 : N0 ≤ n := le_trans hJN0 hn
  have hdist1 : dist (u n) (u (m J)) < ε / 2 := hN0 n hnN0 (m J) hJN0
  have hdist2 : dist (u (m J)) a < ε / 2 := hJ0 J hJ0'
  have hsum : dist (u n) (u (m J)) + dist (u (m J)) a < ε := by
    linarith [hdist1, hdist2]
  have htri : dist (u n) a ≤ dist (u n) (u (m J)) + dist (u (m J)) a :=
    dist_triangle _ _ _
  exact lt_of_le_of_lt htri hsum


end Section04
end Chap01
