/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib

open scoped Topology
open Filter

section Chap03
section Section03

/-- Theorem 3.3.1: [Uniform limits preserve continuity I] Suppose `(X, d_X)` and `(Y, d_Y)` are
metric spaces, `f^{(n)} : X → Y` converges uniformly to `f : X → Y`, and `x0 ∈ X`. If each
`f^{(n)}` is continuous at `x0`, then `f` is continuous at `x0`. -/
theorem uniformLimit_continuousAt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop)
    (x0 : X) (hcont : ∀ n, ContinuousAt (fseq n) x0) :
    ContinuousAt f x0 := by
  refine (Metric.continuousAt_iff (f := f) (a := x0)).2 ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by
    linarith
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : X, dist (f x) (fseq n x) < ε :=
    (Metric.tendstoUniformly_iff (F := fseq) (f := f) (p := atTop)).1 h_unif
  have h_eventually := h_unif' (ε / 3) hε3
  rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
  have hN' : ∀ x : X, dist (f x) (fseq N x) < ε / 3 := by
    intro x
    exact hN N (le_rfl) x
  have hcontN : ContinuousAt (fseq N) x0 := hcont N
  have hεδ :
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : X⦄, dist x x0 < δ →
        dist (fseq N x) (fseq N x0) < ε :=
    (Metric.continuousAt_iff (f := fseq N) (a := x0)).1 hcontN
  rcases hεδ (ε / 3) hε3 with ⟨δ, δ_pos, hδ⟩
  refine ⟨δ, δ_pos, ?_⟩
  intro x hx
  have h1 : dist (f x) (fseq N x) < ε / 3 := hN' x
  have h2 : dist (fseq N x) (fseq N x0) < ε / 3 := hδ (x := x) hx
  have h3 : dist (fseq N x0) (f x0) < ε / 3 := by
    have h3' : dist (f x0) (fseq N x0) < ε / 3 := hN' x0
    simpa [dist_comm] using h3'
  have htriangle :
      dist (f x) (f x0) ≤
        dist (f x) (fseq N x) + dist (fseq N x) (fseq N x0) +
          dist (fseq N x0) (f x0) := by
    have h1' := dist_triangle (f x) (fseq N x) (f x0)
    have h2' := dist_triangle (fseq N x) (fseq N x0) (f x0)
    linarith
  have hsum :
      dist (f x) (fseq N x) + dist (fseq N x) (fseq N x0) +
        dist (fseq N x0) (f x0) < ε := by
    linarith
  exact lt_of_le_of_lt htriangle hsum

/-- Theorem 3.3.2: [Uniform limits preserve continuity] Suppose `(X, d_X)` and `(Y, d_Y)` are
metric spaces and `f^{(n)} : X → Y` converges uniformly to `f : X → Y`. If each `f^{(n)}` is
continuous at every point of `X`, then `f` is continuous at every point of `X`. -/
theorem uniformLimit_continuous
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop)
    (hcont : ∀ n, Continuous (fseq n)) :
    Continuous f := by
  refine (continuous_iff_continuousAt).2 ?_
  intro x0
  have hcontAt : ∀ n, ContinuousAt (fseq n) x0 := by
    intro n
    exact (hcont n).continuousAt
  exact uniformLimit_continuousAt (h_unif := h_unif) x0 hcontAt

/-- Helper for Proposition 3.3.3: the comap filter at an adherent point is nontrivial. -/
lemma helperForProp_3_3_3_comap_neBot
    {X : Type*} [TopologicalSpace X] {E : Set X} {x0 : X}
    (hx0 : x0 ∈ closure E) :
    (Filter.comap (fun x : E => (x : X)) (𝓝 x0)).NeBot := by
  simpa using (mem_closure_iff_comap_neBot (s := E) (x := x0)).1 hx0

/-- Helper for Proposition 3.3.3: convert a limit into an eventual distance bound. -/
lemma helperForProp_3_3_3_eventually_dist_lt_of_hlim
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {F : Filter X} {g : X → Y} {l : Y} (hlim : Tendsto g F (𝓝 l)) :
    ∀ ε > 0, {x : X | dist (g x) l < ε} ∈ F := by
  intro ε hε
  have hball : Metric.ball l ε ∈ 𝓝 l := Metric.ball_mem_nhds _ hε
  have hmem : ∀ᶠ x in F, g x ∈ Metric.ball l ε := hlim.eventually_mem hball
  have hmem' : {x : X | g x ∈ Metric.ball l ε} ∈ F := hmem
  simpa [Metric.mem_ball] using hmem'

/-- Helper for Proposition 3.3.3: the sequence of limits `ℓ` is Cauchy. -/
lemma helperForProp_3_3_3_cauchySeq_ell
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {E : Set X} {fseq : ℕ → E → Y} {f : E → Y} (h_unif : TendstoUniformly fseq f atTop)
    (x0 : X) (hx0 : x0 ∈ closure E) (ℓ : ℕ → Y)
    (hlim :
      ∀ n, Tendsto (fseq n)
        (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 (ℓ n))) :
    CauchySeq ℓ := by
  classical
  let F : Filter E := Filter.comap (fun x : E => (x : X)) (𝓝 x0)
  have hF : Filter.NeBot F :=
    helperForProp_3_3_3_comap_neBot (X := X) (E := E) (x0 := x0) hx0
  haveI : Filter.NeBot F := hF
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : E, dist (f x) (fseq n x) < ε :=
    (Metric.tendstoUniformly_iff (F := fseq) (f := f) (p := atTop)).1 h_unif
  refine (Metric.cauchySeq_iff (u := ℓ)).2 ?_
  intro ε hε
  have hε4 : 0 < ε / 4 := by
    linarith
  have h_eventually := h_unif' (ε / 4) hε4
  rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hlimm :
      {x : E | dist (fseq m x) (ℓ m) < ε / 4} ∈ F := by
    have hlimm' : Tendsto (fseq m) F (𝓝 (ℓ m)) := by
      simpa [F] using hlim m
    exact
      helperForProp_3_3_3_eventually_dist_lt_of_hlim (F := F) (g := fseq m) (l := ℓ m)
        hlimm' (ε / 4) hε4
  have hlimn :
      {x : E | dist (fseq n x) (ℓ n) < ε / 4} ∈ F := by
    have hlimn' : Tendsto (fseq n) F (𝓝 (ℓ n)) := by
      simpa [F] using hlim n
    exact
      helperForProp_3_3_3_eventually_dist_lt_of_hlim (F := F) (g := fseq n) (l := ℓ n)
        hlimn' (ε / 4) hε4
  have hS :
      {x : E | dist (fseq m x) (ℓ m) < ε / 4} ∩
        {x : E | dist (fseq n x) (ℓ n) < ε / 4} ∈ F :=
    Filter.inter_mem hlimm hlimn
  rcases Filter.nonempty_of_mem hS with ⟨x, hx⟩
  have hxm : dist (fseq m x) (ℓ m) < ε / 4 := hx.1
  have hxn : dist (fseq n x) (ℓ n) < ε / 4 := hx.2
  have hxm' : dist (ℓ m) (fseq m x) < ε / 4 := by
    simpa [dist_comm] using hxm
  have hfm : dist (f x) (fseq m x) < ε / 4 := hN m hm x
  have hfn : dist (f x) (fseq n x) < ε / 4 := hN n hn x
  have hfm' : dist (fseq m x) (f x) < ε / 4 := by
    simpa [dist_comm] using hfm
  have htriangle1 :
      dist (ℓ m) (ℓ n) ≤ dist (ℓ m) (fseq m x) + dist (fseq m x) (ℓ n) :=
    dist_triangle (ℓ m) (fseq m x) (ℓ n)
  have htriangle2 :
      dist (fseq m x) (ℓ n) ≤ dist (fseq m x) (f x) + dist (f x) (ℓ n) :=
    dist_triangle (fseq m x) (f x) (ℓ n)
  have htriangle3 :
      dist (f x) (ℓ n) ≤ dist (f x) (fseq n x) + dist (fseq n x) (ℓ n) :=
    dist_triangle (f x) (fseq n x) (ℓ n)
  have htotal :
      dist (ℓ m) (ℓ n) ≤ dist (ℓ m) (fseq m x) + dist (fseq m x) (f x) +
          dist (f x) (fseq n x) + dist (fseq n x) (ℓ n) := by
    linarith [htriangle1, htriangle2, htriangle3]
  have hsum :
      dist (ℓ m) (fseq m x) + dist (fseq m x) (f x) +
          dist (f x) (fseq n x) + dist (fseq n x) (ℓ n) < ε := by
    linarith [hxm', hfm', hfn, hxn]
  exact lt_of_le_of_lt htotal hsum

/-- Helper for Proposition 3.3.3: the uniform limit has the expected limit at `x0`. -/
lemma helperForProp_3_3_3_tendsto_f_limit
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {E : Set X} {fseq : ℕ → E → Y} {f : E → Y} (h_unif : TendstoUniformly fseq f atTop)
    (x0 : X) (ℓ : ℕ → Y)
    (hlim :
      ∀ n, Tendsto (fseq n)
        (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 (ℓ n)))
    {l : Y} (hl : Tendsto ℓ atTop (𝓝 l)) :
    Tendsto f (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 l) := by
  classical
  let F : Filter E := Filter.comap (fun x : E => (x : X)) (𝓝 x0)
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : E, dist (f x) (fseq n x) < ε :=
    (Metric.tendstoUniformly_iff (F := fseq) (f := f) (p := atTop)).1 h_unif
  refine (tendsto_iff_forall_eventually_mem.2 ?_)
  intro s hs
  rcases (Metric.mem_nhds_iff.1 hs) with ⟨ε, hε, hball⟩
  have hε3 : 0 < ε / 3 := by
    linarith
  have h_eventually := h_unif' (ε / 3) hε3
  rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N1, hN1⟩
  have hball_l : Metric.ball l (ε / 3) ∈ 𝓝 l := Metric.ball_mem_nhds _ hε3
  have hℓ_eventually : ∀ᶠ n in atTop, ℓ n ∈ Metric.ball l (ε / 3) :=
    hl.eventually_mem hball_l
  rcases (Filter.eventually_atTop.1 hℓ_eventually) with ⟨N2, hN2⟩
  let N : ℕ := max N1 N2
  have hN1' : ∀ x : E, dist (f x) (fseq N x) < ε / 3 := by
    intro x
    exact hN1 N (le_max_left _ _) x
  have hN2' : dist (ℓ N) l < ε / 3 := by
    have hmem : ℓ N ∈ Metric.ball l (ε / 3) := hN2 N (le_max_right _ _)
    simpa [Metric.mem_ball] using hmem
  have hlimN :
      {x : E | dist (fseq N x) (ℓ N) < ε / 3} ∈ F := by
    have hlimN' : Tendsto (fseq N) F (𝓝 (ℓ N)) := by
      simpa [F] using hlim N
    exact
      helperForProp_3_3_3_eventually_dist_lt_of_hlim (F := F) (g := fseq N) (l := ℓ N)
        hlimN' (ε / 3) hε3
  have hsubset :
      {x : E | dist (fseq N x) (ℓ N) < ε / 3} ⊆ {x : E | dist (f x) l < ε} := by
    intro x hx
    have h1 : dist (f x) (fseq N x) < ε / 3 := hN1' x
    have h2 : dist (fseq N x) (ℓ N) < ε / 3 := hx
    have h3 : dist (ℓ N) l < ε / 3 := hN2'
    have htriangle :
        dist (f x) l ≤ dist (f x) (fseq N x) + dist (fseq N x) (ℓ N) + dist (ℓ N) l := by
      have h1' := dist_triangle (f x) (fseq N x) l
      have h2' := dist_triangle (fseq N x) (ℓ N) l
      linarith
    have hsum :
        dist (f x) (fseq N x) + dist (fseq N x) (ℓ N) + dist (ℓ N) l < ε := by
      linarith [h1, h2, h3]
    exact lt_of_le_of_lt htriangle hsum
  have hball_event : {x : E | dist (f x) l < ε} ∈ F :=
    Filter.mem_of_superset hlimN hsubset
  have hball_event' : {x : E | f x ∈ Metric.ball l ε} ∈ F := by
    simpa [Metric.mem_ball] using hball_event
  have hsubset_ball : {x : E | f x ∈ Metric.ball l ε} ⊆ {x : E | f x ∈ s} := by
    intro x hx
    exact hball hx
  exact Filter.mem_of_superset hball_event' hsubset_ball

/-- Proposition 3.3.3: [Interchange of limits and uniform limits] Let `(X, d_X)` and `(Y, d_Y)`
be metric spaces with `Y` complete, let `E ⊆ X`, and let `f^{(n)} : E → Y` converge uniformly on
`E` to `f : E → Y`. If `x0` is an adherent point of `E` and each `f^{(n)}` has a limit at `x0`
along `E` equal to `ℓ n`, then `ℓ n` converges and `f` has a limit at `x0` along `E`, with the two
iterated limits equal. -/
theorem uniformLimit_interchange_limits
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {E : Set X} {fseq : ℕ → E → Y} {f : E → Y} (h_unif : TendstoUniformly fseq f atTop)
    (x0 : X) (hx0 : x0 ∈ closure E) (ℓ : ℕ → Y)
    (hlim :
      ∀ n, Tendsto (fseq n)
        (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 (ℓ n))) :
    ∃ l : Y, Tendsto ℓ atTop (𝓝 l) ∧
      Tendsto f (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 l) := by
  have hCauchy :
      CauchySeq ℓ :=
    helperForProp_3_3_3_cauchySeq_ell (h_unif := h_unif) (x0 := x0) (hx0 := hx0)
      (ℓ := ℓ) hlim
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨l, hl⟩
  have hT :
      Tendsto f (Filter.comap (fun x : E => (x : X)) (𝓝 x0)) (𝓝 l) :=
    helperForProp_3_3_3_tendsto_f_limit (h_unif := h_unif) (x0 := x0) (ℓ := ℓ)
      (hlim := hlim) hl
  exact ⟨l, hl, hT⟩

/-- Helper for Proposition 3.3.4: uniform convergence with the distance order reversed. -/
lemma helperForProp_3_3_4_unif_dist_lt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : X, dist (fseq n x) (f x) < ε := by
  intro ε hε
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : X, dist (f x) (fseq n x) < ε :=
    (Metric.tendstoUniformly_iff (F := fseq) (f := f) (p := atTop)).1 h_unif
  have h_eventually := h_unif' ε hε
  refine h_eventually.mono ?_
  intro n hn x
  simpa [dist_comm] using hn x

/-- Helper for Proposition 3.3.4: a 5-point triangle inequality chain. -/
lemma helperForProp_3_3_4_dist_triangle5
    {Y : Type*} [MetricSpace Y] (a b c d e : Y) :
    dist a e ≤ dist a b + dist b c + dist c d + dist d e := by
  have h1 : dist a e ≤ dist a b + dist b c + dist c e := dist_triangle4 a b c e
  have h2 : dist c e ≤ dist c d + dist d e := dist_triangle c d e
  have h3 :
      dist a b + dist b c + dist c e ≤ dist a b + dist b c + dist c d + dist d e := by
    linarith
  exact le_trans h1 h3

/-- Proposition 3.3.4: Let `(X, d_X)` and `(Y, d_Y)` be metric spaces. Let `f^{(n)} : X → Y` be
continuous for each `n`, and suppose `f^{(n)} → f : X → Y` uniformly on `X`. If `(x^{(n)})` is a
sequence in `X` with `x^{(n)} → x`, then `f^{(n)}(x^{(n)}) → f(x)` in `Y`. -/
theorem uniformLimit_eval_tendsto
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop)
    (hcont : ∀ n, Continuous (fseq n))
    {xseq : ℕ → X} {x : X} (hx : Tendsto xseq atTop (𝓝 x)) :
    Tendsto (fun n => fseq n (xseq n)) atTop (𝓝 (f x)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε4 : 0 < ε / 4 := by
    linarith
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : X, dist (fseq n x) (f x) < ε :=
    helperForProp_3_3_4_unif_dist_lt (X := X) (Y := Y) (fseq := fseq) (f := f) h_unif
  have h_eventually := h_unif' (ε / 4) hε4
  rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N0, hN0⟩
  have hcontN0 : Tendsto (fun n => fseq N0 (xseq n)) atTop (𝓝 (fseq N0 x)) := by
    have hcontN0' : Tendsto (fseq N0) (𝓝 x) (𝓝 (fseq N0 x)) :=
      (hcont N0).tendsto x
    exact hcontN0'.comp hx
  have hcontN0' := Metric.tendsto_atTop.1 hcontN0 (ε / 4) hε4
  rcases hcontN0' with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hdist_n_xseq : dist (fseq n (xseq n)) (f (xseq n)) < ε / 4 := hN0 n hn0 (xseq n)
  have hdist_N0_xseq : dist (fseq N0 (xseq n)) (f (xseq n)) < ε / 4 := hN0 N0 le_rfl (xseq n)
  have hdist_N0_x : dist (fseq N0 x) (f x) < ε / 4 := hN0 N0 le_rfl x
  have hdist_cont : dist (fseq N0 (xseq n)) (fseq N0 x) < ε / 4 := hN1 n hn1
  have hdist_mid :
      dist (f (xseq n)) (fseq N0 (xseq n)) < ε / 4 := by
    simpa [dist_comm] using hdist_N0_xseq
  have htriangle :
      dist (fseq n (xseq n)) (f x) ≤
        dist (fseq n (xseq n)) (f (xseq n)) +
        dist (f (xseq n)) (fseq N0 (xseq n)) +
        dist (fseq N0 (xseq n)) (fseq N0 x) +
        dist (fseq N0 x) (f x) :=
    helperForProp_3_3_4_dist_triangle5
      (fseq n (xseq n)) (f (xseq n)) (fseq N0 (xseq n)) (fseq N0 x) (f x)
  have hsum :
      dist (fseq n (xseq n)) (f (xseq n)) +
        dist (f (xseq n)) (fseq N0 (xseq n)) +
        dist (fseq N0 (xseq n)) (fseq N0 x) +
        dist (fseq N0 x) (f x) < ε := by
    linarith [hdist_n_xseq, hdist_mid, hdist_cont, hdist_N0_x]
  exact lt_of_le_of_lt htriangle hsum

/-- Definition 3.4: A function `f : X → Y` between metric spaces is bounded if its image lies in
some ball, i.e., there exist `y0 ∈ Y` and `R > 0` such that `dist (f x) y0 < R` for all `x ∈ X`. -/
def IsBoundedFunction
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∃ y0 : Y, ∃ R : ℝ, 0 < R ∧ ∀ x : X, dist (f x) y0 < R

/-- Helper for Proposition 3.3.5: boundedness is stable under a uniform perturbation. -/
lemma helperForProp_3_3_5_isBounded_of_uniform_dist_lt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f g : X → Y} {ε : ℝ} (hε : 0 < ε)
    (hbounded : IsBoundedFunction g) (hfg : ∀ x, dist (f x) (g x) < ε) :
    IsBoundedFunction f := by
  rcases hbounded with ⟨y0, R, hRpos, hR⟩
  refine ⟨y0, R + ε, ?_, ?_⟩
  · linarith
  · intro x
    have htriangle : dist (f x) y0 ≤ dist (f x) (g x) + dist (g x) y0 :=
      dist_triangle (f x) (g x) y0
    have hsum' : dist (f x) (g x) + dist (g x) y0 < ε + R :=
      add_lt_add (hfg x) (hR x)
    have hsum : dist (f x) (g x) + dist (g x) y0 < R + ε := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum'
    exact lt_of_le_of_lt htriangle hsum

/-- Proposition 3.3.5: [Uniform limits preserve boundedness] Let `(X, d_X)` and `(Y, d_Y)` be
metric spaces. Let `f^{(n)} : X → Y` converge uniformly to `f : X → Y`. If each `f^{(n)}` is
bounded on `X`, then `f` is bounded on `X`. -/
theorem uniformLimit_bounded
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop)
    (hbounded : ∀ n, IsBoundedFunction (fseq n)) :
    IsBoundedFunction f := by
  have h_unif' :
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : X, dist (f x) (fseq n x) < ε :=
    (Metric.tendstoUniformly_iff (F := fseq) (f := f) (p := atTop)).1 h_unif
  have hε : 0 < (1 : ℝ) := by
    norm_num
  have h_eventually := h_unif' 1 hε
  rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
  have hN' : ∀ x : X, dist (f x) (fseq N x) < (1 : ℝ) := by
    intro x
    exact hN N (le_rfl) x
  have hboundedN : IsBoundedFunction (fseq N) := hbounded N
  exact
    helperForProp_3_3_5_isBounded_of_uniform_dist_lt
      (f := f) (g := fseq N) (ε := 1) hε hboundedN hN'

/-- Proposition 3.3.6: [Uniform limits preserve boundedness] Let `(X, d_X)` and `(Y, d_Y)` be
metric spaces. Let `f^{(n)} : X → Y` converge uniformly to `f : X → Y`. If each `f^{(n)}` is
bounded on `X`, then `f` is bounded on `X`. -/
theorem uniformLimit_boundedness
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {fseq : ℕ → X → Y} {f : X → Y} (h_unif : TendstoUniformly fseq f atTop)
    (hbounded : ∀ n, IsBoundedFunction (fseq n)) :
    IsBoundedFunction f :=
  uniformLimit_bounded (h_unif := h_unif) hbounded

end Section03
end Chap03
