/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open Filter Topology

section Chap03
section Section01

/-- Definition 3.1.1: For a set `S ⊆ ℝ`, a real number `x` is a cluster point of
`S` if for every `ε > 0` the punctured neighborhood `(x - ε, x + ε) ∩ S \ {x}`
is nonempty. -/
def IsClusterPoint (S : Set ℝ) (x : ℝ) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε →
    ((Set.Ioo (x - ε) (x + ε) ∩ S) \ {x}).Nonempty

/-- Mathlib expresses cluster points via closure of punctured sets. -/
lemma isClusterPoint_iff_mem_closure_diff (S : Set ℝ) (x : ℝ) :
    IsClusterPoint S x ↔ x ∈ closure (S \ {x}) := by
  classical
  constructor
  · intro hx
    refine (Metric.mem_closure_iff : x ∈ closure (S \ {x}) ↔ _).2 ?_
    intro ε hε
    obtain ⟨y, hy⟩ := hx hε
    rcases hy with ⟨⟨hyIoo, hyS⟩, hyx⟩
    rcases Set.mem_Ioo.1 hyIoo with ⟨hleft, hright⟩
    have hleft' : -ε < y - x := by
      have := sub_lt_sub_right hleft x
      simpa [sub_eq_add_neg] using this
    have hright' : y - x < ε := by
      have := sub_lt_sub_right hright x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hy_ball : dist y x < ε := by
      simpa [Real.dist_eq] using (abs_lt.2 ⟨hleft', hright'⟩ : |y - x| < ε)
    have hy_ball' : dist x y < ε := by simpa [dist_comm] using hy_ball
    exact ⟨y, ⟨⟨hyS, hyx⟩, hy_ball'⟩⟩
  · intro hx
    refine fun ε hε => ?_
    obtain ⟨y, hySdiff, hy_ball⟩ :=
      (Metric.mem_closure_iff : x ∈ closure (S \ {x}) ↔ _).1 hx ε hε
    have hy_ball' : dist y x < ε := by simpa [dist_comm] using hy_ball
    have hy_abs : |y - x| < ε := by
      simpa [Real.dist_eq] using hy_ball'
    rcases hySdiff with ⟨hyS, hyx⟩
    rcases abs_lt.1 hy_abs with ⟨hleft, hright⟩
    have hleft' : x - ε < y := by
      have := add_lt_add_right hleft x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hright' : y < x + ε := by
      have := add_lt_add_right hright x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hyIoo : y ∈ Set.Ioo (x - ε) (x + ε) := ⟨hleft', hright'⟩
    exact ⟨y, ⟨⟨hyIoo, hyS⟩, hyx⟩⟩

/-- Proposition 3.1.2: A real number `x` is a cluster point of `S ⊆ ℝ` iff
there exists a sequence `(xₙ)` with each `xₙ ∈ S`, `xₙ ≠ x`, and
`xₙ → x`. -/
lemma isClusterPoint_iff_exists_seq_tendsto (S : Set ℝ) (x : ℝ) :
    IsClusterPoint S x ↔
      ∃ u : ℕ → ℝ,
        (∀ n, u n ∈ S ∧ u n ≠ x) ∧ Tendsto u atTop (𝓝 x) := by
  classical
  constructor
  · intro hx
    let ε : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
    have hε_pos : ∀ n, 0 < ε n := fun n =>
      one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
    have hnonempty :
        ∀ n : ℕ,
          ((Set.Ioo (x - ε n) (x + ε n) ∩ S) \ {x}).Nonempty := fun n => by
      simpa [ε] using hx (hε_pos n)
    choose u hu using hnonempty
    have hu_mem : ∀ n, u n ∈ S := fun n => (hu n).1.2
    have hu_ne : ∀ n, u n ≠ x := fun n => by
      have hxmem : u n ∉ ({x} : Set ℝ) := (hu n).2
      simpa [Set.mem_singleton_iff] using hxmem
    have hu_dist :
        ∀ n, dist (u n) x < ε n := fun n => by
      have huIoo := (hu n).1.1
      rcases Set.mem_Ioo.1 huIoo with ⟨hleft, hright⟩
      have hleft' : -(ε n) < u n - x := by
        have := sub_lt_sub_right hleft x
        simpa [ε, sub_eq_add_neg] using this
      have hright' : u n - x < ε n := by
        have := sub_lt_sub_right hright x
        simpa [ε, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      simpa [Real.dist_eq] using (abs_lt.2 ⟨hleft', hright'⟩ : |u n - x| < ε n)
    refine ⟨u, ?_, ?_⟩
    · intro n
      exact ⟨hu_mem n, hu_ne n⟩
    · have hnonneg :
        ∀ n, 0 ≤ dist (u n) x := fun _ => dist_nonneg
      have hbound :
          ∀ n, dist (u n) x ≤ ε n := fun n => le_of_lt (hu_dist n)
      have hlim_dist :
          Tendsto (fun n => dist (u n) x) atTop (𝓝 (0 : ℝ)) :=
        Filter.Tendsto.squeeze tendsto_const_nhds
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          hnonneg hbound
      simpa [ε, tendsto_iff_dist_tendsto_zero] using hlim_dist
  · rintro ⟨u, hu_mem, hlim⟩
    refine fun ε hε => ?_
    have hx_ball : x ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball, dist_self] using hε
    have h_event :
        (fun n => u n) ⁻¹' Metric.ball x ε ∈ atTop :=
      (_root_.tendsto_nhds.1 hlim) _ Metric.isOpen_ball hx_ball
    rcases eventually_atTop.1 h_event with ⟨N, hN⟩
    refine ⟨u N, ?_⟩
    have hball_mem : u N ∈ Metric.ball x ε := hN N (le_rfl)
    have hdist : dist (u N) x < ε := by
      simpa [Metric.mem_ball] using hball_mem
    have hy_abs : |u N - x| < ε := by
      simpa [Real.dist_eq] using hdist
    rcases abs_lt.1 hy_abs with ⟨hleft, hright⟩
    have hleft' : x - ε < u N := by
      have := add_lt_add_right hleft x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hright' : u N < x + ε := by
      have := add_lt_add_right hright x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hyIoo : u N ∈ Set.Ioo (x - ε) (x + ε) := ⟨hleft', hright'⟩
    have hy_mem : u N ∈ S := (hu_mem N).1
    have hy_ne : u N ≠ x := (hu_mem N).2
    have hy_ne_set : u N ∉ ({x} : Set ℝ) := by
      simpa [Set.mem_singleton_iff] using hy_ne
    exact ⟨⟨hyIoo, hy_mem⟩, hy_ne_set⟩

/-- Definition 3.1.3: A function `f : ℝ → ℝ` converges to `L` as `x` approaches
`c` within a set `S` if `c` is a cluster point of `S` and for every `ε > 0`
there is `δ > 0` such that for all `x ∈ S` with `x ≠ c` and `|x - c| < δ` we
have `|f x - L| < ε`. -/
def LimitWithin (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) : Prop :=
  IsClusterPoint S c ∧
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ δ > 0, ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε

/-- Given a cluster point and a radius, we can find a point of the set that
lies within that radius yet differs from the center. -/
lemma exists_mem_near_cluster {S : Set ℝ} {c δ : ℝ}
    (hc : IsClusterPoint S c) (hδ : 0 < δ) :
    ∃ x ∈ S, x ≠ c ∧ |x - c| < δ := by
  obtain ⟨x, hx⟩ := hc hδ
  rcases hx with ⟨⟨hxIoo, hxS⟩, hx_ne⟩
  refine ⟨x, hxS, ?_, ?_⟩
  · simpa [Set.mem_singleton_iff] using hx_ne
  · rcases Set.mem_Ioo.1 hxIoo with ⟨hleft, hright⟩
    have hleft' : -δ < x - c := by
      have := sub_lt_sub_right hleft c
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hright' : x - c < δ := by
      have := sub_lt_sub_right hright c
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    simpa [sub_eq_add_neg] using (abs_lt.2 ⟨hleft', hright'⟩ :
      |x - c| < δ)

/-- A quantitative triangle inequality specialized to halving an epsilon. -/
lemma abs_sub_lt_of_add {a b c ε : ℝ} (h₁ : |a - b| < ε / 2)
    (h₂ : |b - c| < ε / 2) : |a - c| < ε := by
  have htriangle : |a - c| ≤ |a - b| + |b - c| := by
    have := abs_add_le (a - b) (b - c)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hsum : |a - b| + |b - c| < ε := by
    have := add_lt_add h₁ h₂
    have hhalf : ε / 2 + ε / 2 = ε := by ring
    simpa [hhalf] using this
  exact lt_of_le_of_lt htriangle hsum

/-- Membership in `S \ {c}` means membership in `S` and inequality to `c`. -/
lemma mem_diff_singleton_iff {S : Set ℝ} {x c : ℝ} :
    x ∈ S \ {c} ↔ x ∈ S ∧ x ≠ c := by
  simp [Set.mem_diff, Set.mem_singleton_iff]

/-- Convert `LimitWithin` to a `Tendsto` statement on `S \ {c}`. -/
lemma limitWithin_to_tendsto {S : Set ℝ} {f : ℝ → ℝ} {c L : ℝ} :
    LimitWithin S f c L → Tendsto f (𝓝[S \ {c}] c) (𝓝 L) := by
  intro h
  refine (Metric.tendsto_nhdsWithin_nhds.2 ?_)
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := h.2 hε
  refine ⟨δ, hδpos, ?_⟩
  intro x hxSdiff hx_dist
  rcases (mem_diff_singleton_iff).1 hxSdiff with ⟨hxS, hxne⟩
  have hxabs : |x - c| < δ := by
    simpa [Real.dist_eq] using hx_dist
  have hfxabs : |f x - L| < ε := hδ hxS hxne hxabs
  simpa [Real.dist_eq] using hfxabs

/-- Repackage a `Tendsto` statement on `S \ {c}` into eps-delta form. -/
lemma tendsto_to_limitWithin_epsdelta {S : Set ℝ} {f : ℝ → ℝ} {c L : ℝ} :
    Tendsto f (𝓝[S \ {c}] c) (𝓝 L) →
      ∀ ⦃ε : ℝ⦄, 0 < ε →
        ∃ δ > 0, ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε := by
  intro h ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.1 h) ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro x hxS hxne hxabs
  have hxSdiff : x ∈ S \ {c} := (mem_diff_singleton_iff).2 ⟨hxS, hxne⟩
  have hx_dist : dist x c < δ := by
    simpa [Real.dist_eq] using hxabs
  have hfx_dist : dist (f x) L < ε := hδ hxSdiff hx_dist
  simpa [Real.dist_eq] using hfx_dist

/-- Mathlib expresses this limit as a `Tendsto` statement toward the `nhdsWithin`
filter that omits the point `c`. -/
lemma limitWithin_iff_tendsto (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) :
    LimitWithin S f c L ↔ IsClusterPoint S c ∧ Tendsto f (𝓝[S \ {c}] c) (𝓝 L) := by
  constructor
  · intro h
    exact ⟨h.1, limitWithin_to_tendsto h⟩
  · rintro ⟨hc, hT⟩
    exact ⟨hc, tendsto_to_limitWithin_epsdelta hT⟩

/-- Proposition 3.1.4: If `c` is a cluster point of `S ⊆ ℝ` and a function
`f : ℝ → ℝ` converges to some real number as `x` approaches `c` within `S`,
then that limit value is unique. -/
lemma limitWithin_unique (S : Set ℝ) (f : ℝ → ℝ) (c L₁ L₂ : ℝ)
    (h₁ : LimitWithin S f c L₁) (h₂ : LimitWithin S f c L₂) : L₁ = L₂ := by
  classical
  have hc : IsClusterPoint S c := h₁.1
  have h_abs :
      ∀ ⦃ε : ℝ⦄, 0 < ε → |L₁ - L₂| < ε := by
    intro ε hε
    have hε_half : 0 < ε / 2 := half_pos hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h₁.2 hε_half
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := h₂.2 hε_half
    let δ := min δ₁ δ₂
    have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
    obtain ⟨x, hxS, hx_ne, hx_lt⟩ := exists_mem_near_cluster hc hδ_pos
    have hx_lt₁ : |x - c| < δ₁ := lt_of_lt_of_le hx_lt (min_le_left _ _)
    have hx_lt₂ : |x - c| < δ₂ := lt_of_lt_of_le hx_lt (min_le_right _ _)
    have h₁bound : |f x - L₁| < ε / 2 := hδ₁ hxS hx_ne hx_lt₁
    have h₂bound : |f x - L₂| < ε / 2 := hδ₂ hxS hx_ne hx_lt₂
    have h₁bound' : |L₁ - f x| < ε / 2 := by simpa [abs_sub_comm] using h₁bound
    exact abs_sub_lt_of_add h₁bound' h₂bound
  have hzero : |L₁ - L₂| = 0 := by
    by_contra hpos
    have hpos' : 0 < |L₁ - L₂| :=
      lt_of_le_of_ne (abs_nonneg _) (by simpa [eq_comm] using hpos)
    exact lt_irrefl _ (h_abs hpos')
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Bounding `|x|` when `x` lies within `1` of `c`. -/
lemma abs_le_of_abs_sub_lt_one {x c : ℝ} (h : |x - c| < 1) : |x| ≤ |c| + 1 := by
  have htriangle : |x| ≤ |x - c| + |c| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_add_le (x - c) c)
  have hle : |x - c| ≤ 1 := le_of_lt h
  have hsum : |x - c| + |c| ≤ 1 + |c| := by
    simpa [add_comm] using add_le_add_right hle |c|
  have hsum' : |x - c| + |c| ≤ |c| + 1 := by simpa [add_comm] using hsum
  exact htriangle.trans hsum'

/-- Bounding `|x^2 - c^2|` by `|x - c|` when `x` is within `1` of `c`. -/
lemma abs_sq_sub_bound {x c : ℝ} (h : |x - c| < 1) :
    |x ^ 2 - c ^ 2| ≤ (2 * |c| + 1) * |x - c| := by
  have habsx : |x| ≤ |c| + 1 := abs_le_of_abs_sub_lt_one h
  have hx_add : |x + c| ≤ |x| + |c| := by
    simpa using abs_add_le x c
  have hx_sum : |x| + |c| ≤ (|c| + 1) + |c| := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right habsx |c|
  have hx_sum' : (|c| + 1) + |c| = 2 * |c| + 1 := by ring
  have hx_bound : |x + c| ≤ 2 * |c| + 1 := by
    have := le_trans hx_add hx_sum
    simpa [hx_sum', add_comm, add_left_comm, add_assoc] using this
  have hnonneg : 0 ≤ |x - c| := abs_nonneg _
  have hmul : |x - c| * |x + c| ≤ |x - c| * (2 * |c| + 1) :=
    mul_le_mul_of_nonneg_left hx_bound hnonneg
  have hfactor : x ^ 2 - c ^ 2 = (x - c) * (x + c) := by
    simpa [mul_comm] using (sq_sub_sq x c)
  calc
    |x ^ 2 - c ^ 2|
        = |(x - c) * (x + c)| := by
            simp [hfactor]
    _ = |x - c| * |x + c| := by
            simp [abs_mul]
    _ ≤ |x - c| * (2 * |c| + 1) := hmul
    _ = (2 * |c| + 1) * |x - c| := by
            simp [mul_comm]

/-- Example 3.1.5: For the function `f x = x^2` and any real `c`, the limit
as `x → c` is `c^2`. -/
lemma tendsto_sq (c : ℝ) : Tendsto (fun x : ℝ => x ^ 2) (𝓝 c) (𝓝 (c ^ 2)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hpos : 0 < 2 * |c| + 1 := by
    have hnonneg : 0 ≤ 2 * |c| := by
      have hc : 0 ≤ |c| := abs_nonneg _
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg htwo hc
    exact add_pos_of_nonneg_of_pos hnonneg zero_lt_one
  have hδ :
      0 < min 1 (ε / (2 * |c| + 1)) := lt_min zero_lt_one (div_pos hε hpos)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ hδ) ?_
  intro x hx
  have hx_abs : |x - c| < min 1 (ε / (2 * |c| + 1)) := by
    simpa [Real.dist_eq] using hx
  have hx_lt_one : |x - c| < 1 :=
    lt_of_lt_of_le hx_abs (min_le_left _ _)
  have hx_lt_eps : |x - c| < ε / (2 * |c| + 1) :=
    lt_of_lt_of_le hx_abs (min_le_right _ _)
  have hbound := abs_sq_sub_bound hx_lt_one
  have hmul : (2 * |c| + 1) * |x - c| < ε := by
    have hmul' := mul_lt_mul_of_pos_right hx_lt_eps hpos
    have hne : (2 * |c| + 1) ≠ 0 := ne_of_gt hpos
    have hcancel :
        (ε / (2 * |c| + 1)) * (2 * |c| + 1) = ε := by
      have hne' : 2 * |c| + 1 ≠ 0 := hne
      calc
        (ε / (2 * |c| + 1)) * (2 * |c| + 1)
            = ε * ((2 * |c| + 1)⁻¹ * (2 * |c| + 1)) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm]
        _ = ε * 1 := by
              simpa [mul_comm] using
                congrArg (fun t => ε * t) (inv_mul_cancel₀ hne')
        _ = ε := by simp
    have hmul'' : |x - c| * (2 * |c| + 1) < ε := by
      simpa [hcancel] using hmul'
    simpa [mul_comm] using hmul''
  have hlt : |x ^ 2 - c ^ 2| < ε := lt_of_le_of_lt hbound hmul
  simpa [Real.dist_eq] using hlt

/-- Example 3.1.6: The piecewise function on `[0, 1)` given by `f x = x` for
`x > 0` and `f 0 = 1` satisfies `f ⟶ 0` as `x → 0` within `[0, 1)`, even though
`f 0 = 1`. -/
noncomputable def limitValueDiff (x : ℝ) : ℝ :=
  if x = 0 then 1 else x

lemma limitValueDiff_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    limitValueDiff x = x := by
  classical
  simp [limitValueDiff, hx]

lemma limitValueDiff_eq_self_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : limitValueDiff x = x := by
  have hx₀ : x ≠ 0 := ne_of_gt hx.1
  exact limitValueDiff_of_ne_zero hx₀

lemma abs_limitValueDiff_eq_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : |limitValueDiff x| = x := by
  classical
  have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx.1
  simp [limitValueDiff_eq_self_of_mem_Ioo hx, abs_of_nonneg hx_nonneg]

/-- The limit of `limitValueDiff` at `0` within `(0, 1)` (the punctured part of `[0, 1)`)
is `0`. -/
lemma tendsto_limitValueDiff :
    Tendsto limitValueDiff (𝓝[Set.Ioo 0 1] 0) (𝓝 (0 : ℝ)) := by
  refine (Metric.tendsto_nhdsWithin_nhds : _).2 ?_
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x hx_mem hx_dist
  have hx_abs :
      |x| < min ε 1 := by
        simpa [Real.dist_eq, sub_eq_add_neg] using hx_dist
  have hx_lt_eps : x < ε := by
    have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx_mem.1
    have hx_abs_eq : |x| = x := abs_of_nonneg hx_nonneg
    have hx_abs_lt : |x| < ε :=
      lt_of_lt_of_le hx_abs (min_le_left _ _)
    simpa [hx_abs_eq] using hx_abs_lt
  have habs : |limitValueDiff x| < ε := by
    simpa [abs_limitValueDiff_eq_of_mem_Ioo hx_mem] using hx_lt_eps
  simpa [Real.dist_eq, sub_eq_add_neg] using habs

/-- The value of `limitValueDiff` at `0` is `1`, differing from the limit. -/
lemma limitValueDiff_zero : limitValueDiff 0 = (1 : ℝ) := by
  classical
  simp [limitValueDiff]

/-- Lemma 3.1.7: For `S ⊆ ℝ`, a cluster point `c` of `S`, a function `f : S → ℝ`,
and `L : ℝ`, we have `f(x) → L` as `x → c` iff for every sequence `(xₙ)` with
`xₙ ∈ S \ {c}` and `xₙ → c`, the sequence `(f xₙ)` converges to `L`. -/
lemma limitWithin_iff_seq_tendsto (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) :
    LimitWithin S f c L ↔
      IsClusterPoint S c ∧
        ∀ u : ℕ → ℝ,
          (∀ n, u n ∈ S \ {c}) →
          Tendsto u atTop (𝓝 c) →
          Tendsto (fun n => f (u n)) atTop (𝓝 L) := by
  classical
  constructor
  · intro hlimit
    refine ⟨hlimit.1, ?_⟩
    intro u hu_mem hu_tendsto
    refine (tendsto_nhds.2 ?_)
    intro s hs_open hL
    have hs : s ∈ 𝓝 L := hs_open.mem_nhds hL
    rcases Metric.mem_nhds_iff.1 hs with ⟨ε, hε_pos, hball_subset⟩
    obtain ⟨δ, hδ_pos, hδ⟩ := hlimit.2 hε_pos
    have h_ball_u : (fun n => u n) ⁻¹' Metric.ball c δ ∈ atTop := by
      refine (tendsto_nhds.1 hu_tendsto) _ Metric.isOpen_ball ?_
      simpa [Metric.mem_ball, dist_self] using hδ_pos
    refine Filter.mem_of_superset h_ball_u ?_
    intro n hn
    have huS : u n ∈ S := (hu_mem n).1
    have hu_ne_set : u n ∉ ({c} : Set ℝ) := (hu_mem n).2
    have hu_ne : u n ≠ c := by
      simpa [Set.mem_singleton_iff] using hu_ne_set
    have hdist : dist (u n) c < δ := by
      simpa [Metric.mem_ball] using hn
    have habs : |u n - c| < δ := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hdist
    have hf_bound : |f (u n) - L| < ε := hδ huS hu_ne habs
    have hf_ball : f (u n) ∈ Metric.ball L ε := by
      simpa [Metric.mem_ball, Real.dist_eq] using hf_bound
    exact hball_subset hf_ball
  · rintro ⟨hc, hseq⟩
    refine ⟨hc, ?_⟩
    intro ε hε
    classical
    by_contra hfail
    have hcounter :
        ∀ δ > 0,
          ∃ x, x ∈ S ∧ x ≠ c ∧ |x - c| < δ ∧ ε ≤ |f x - L| := by
      intro δ hδ
      have hneg :
          ¬ ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε := by
        intro hgood
        exact hfail ⟨δ, hδ, hgood⟩
      rcases not_forall.1 hneg with ⟨x, hx⟩
      have hxS : x ∈ S := by
        classical
        by_contra hxS
        have hx_imp : x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε := by
          intro hx_mem
          exact (hxS hx_mem).elim
        exact hx hx_imp
      have hnot₁ :
          ¬ (x ≠ c → |x - c| < δ → |f x - L| < ε) := by
        simpa [hxS] using hx
      have hx_ne : x ≠ c := by
        classical
        by_contra hx_ne
        have hx_imp : x ≠ c → |x - c| < δ → |f x - L| < ε := by
          intro hx_ne'
          exact (hx_ne' hx_ne).elim
        exact hnot₁ hx_imp
      have hnot₂ : ¬ (|x - c| < δ → |f x - L| < ε) := by
        simpa [hx_ne] using hnot₁
      have hx_lt : |x - c| < δ := by
        classical
        by_contra hx_lt
        have hx_imp : |x - c| < δ → |f x - L| < ε := by
          intro hx_lt'
          exact (hx_lt hx_lt').elim
        exact hnot₂ hx_imp
      have hnot₃ : ¬ (|f x - L| < ε) := by
        simpa [hx_lt] using hnot₂
      have hx_ge : ε ≤ |f x - L| := not_lt.1 hnot₃
      exact ⟨x, hxS, hx_ne, hx_lt, hx_ge⟩
    let δ : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
    have hδ_pos : ∀ n, 0 < δ n := fun n =>
      one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
    have hx_exists :
        ∀ n,
          ∃ x, x ∈ S ∧ x ≠ c ∧ |x - c| < δ n ∧ ε ≤ |f x - L| :=
      fun n => hcounter (δ n) (hδ_pos n)
    choose u hu using hx_exists
    have hu_mem : ∀ n, u n ∈ S := fun n => (hu n).1
    have hu_ne : ∀ n, u n ≠ c := fun n => (hu n).2.1
    have hu_dist : ∀ n, |u n - c| < δ n := fun n => (hu n).2.2.1
    have hu_far : ∀ n, ε ≤ |f (u n) - L| := fun n => (hu n).2.2.2
    have hu_diff : ∀ n, u n ∈ S \ {c} := fun n =>
      ⟨hu_mem n, by simpa [Set.mem_singleton_iff] using hu_ne n⟩
    have hdist_lt : ∀ n, dist (u n) c < δ n := fun n =>
      by simpa [Real.dist_eq, sub_eq_add_neg] using hu_dist n
    have hdist_nonneg : ∀ n, 0 ≤ dist (u n) c := fun _ => dist_nonneg
    have hdist_le : ∀ n, dist (u n) c ≤ δ n := fun n => le_of_lt (hdist_lt n)
    have hδ_lim :
        Tendsto (fun n : ℕ => δ n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hlim_dist :
        Tendsto (fun n : ℕ => dist (u n) c) atTop (𝓝 (0 : ℝ)) :=
      Filter.Tendsto.squeeze tendsto_const_nhds hδ_lim hdist_nonneg hdist_le
    have hu_tendsto : Tendsto u atTop (𝓝 c) := by
      simpa [tendsto_iff_dist_tendsto_zero] using hlim_dist
    have hlim_f := hseq u hu_diff hu_tendsto
    have hball_mem : L ∈ Metric.ball L ε := by
      simpa [Metric.mem_ball, dist_self] using hε
    have hf_event :
        (fun n => f (u n)) ⁻¹' Metric.ball L ε ∈ atTop :=
      (tendsto_nhds.1 hlim_f) _ Metric.isOpen_ball hball_mem
    rcases eventually_atTop.1 hf_event with ⟨N, hN⟩
    have hf_lt : |f (u N) - L| < ε := by
      have : f (u N) ∈ Metric.ball L ε := hN N le_rfl
      simpa [Metric.mem_ball, Real.dist_eq] using this
    have hf_ge : ε ≤ |f (u N) - L| := hu_far N
    exact (not_lt_of_ge hf_ge) hf_lt

/-- The sequence `uₙ = 1 / (π n + π / 2)` used in Example 3.1.8. -/
noncomputable def sinInvSeq (n : ℕ) : ℝ :=
  1 / (Real.pi * (n : ℝ) + Real.pi / 2)

lemma sinInvSeq_den_pos (n : ℕ) :
    0 < Real.pi * (n : ℝ) + Real.pi / 2 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi2_pos : 0 < Real.pi / 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact div_pos hpi_pos this
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hmul_nonneg : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg hpi_pos.le hn_nonneg
  exact add_pos_of_nonneg_of_pos hmul_nonneg hpi2_pos

lemma sinInvSeq_pos (n : ℕ) : 0 < sinInvSeq n :=
  one_div_pos.mpr (sinInvSeq_den_pos n)

lemma sinInvSeq_ne_zero (n : ℕ) : sinInvSeq n ≠ 0 :=
  (ne_of_gt (sinInvSeq_pos n))

lemma sinInvSeq_eq (n : ℕ) :
    sinInvSeq n = (1 / Real.pi) * (1 / ((n : ℝ) + (1 / 2 : ℝ))) := by
  let s := (n : ℝ) + (1 / 2 : ℝ)
  have hden :
      Real.pi * (n : ℝ) + Real.pi / 2 =
        Real.pi * s := by
    ring
  have hrewrite :
      sinInvSeq n = 1 / (Real.pi * s) := by
    simp [sinInvSeq, hden, s]
  calc
    sinInvSeq n = 1 / (Real.pi * s) := hrewrite
    _ = 1 / (s * Real.pi) := by simp [s, mul_comm]
    _ = (1 / Real.pi) * (1 / s) :=
        (one_div_mul_one_div_rev Real.pi s).symm
    _ = (1 / Real.pi) * (1 / ((n : ℝ) + (1 / 2 : ℝ))) := by
        simp [s]

lemma sin_inv_seq_tendsto :
    Tendsto sinInvSeq atTop (𝓝 (0 : ℝ)) := by
  have h_nat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h_shift :
      Tendsto (fun n : ℕ => (n : ℝ) + (1 / 2 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ h_nat
  have h_inv :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + (1 / 2 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp h_shift)
  have h_mul :
      Tendsto (fun n : ℕ =>
          ((1 : ℝ) / Real.pi) * (1 / ((n : ℝ) + (1 / 2 : ℝ))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.mul h_inv :
        Tendsto
          (fun n : ℕ =>
            ((1 : ℝ) / Real.pi) * (1 / ((n : ℝ) + (1 / 2 : ℝ))))
          atTop (𝓝 (((1 : ℝ) / Real.pi) * 0)))
  have hfun :
      sinInvSeq =
        fun n : ℕ => (1 / Real.pi) * (1 / ((n : ℝ) + (1 / 2 : ℝ))) := by
    funext n; exact sinInvSeq_eq n
  simpa [hfun] using h_mul

lemma sin_inv_seq_values (n : ℕ) :
    Real.sin (1 / sinInvSeq n) = (-1 : ℝ) ^ n := by
  have hsin :
      Real.sin (Real.pi * (n : ℝ) + Real.pi / 2)
          = Real.cos (Real.pi * (n : ℝ)) := by
    have := Real.sin_add (Real.pi * (n : ℝ)) (Real.pi / 2)
    simpa [Real.sin_pi_div_two, Real.cos_pi_div_two, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using this
  have hcos :
      Real.cos (Real.pi * (n : ℝ)) = (-1 : ℝ) ^ n := by
    simpa [mul_comm] using Real.cos_nat_mul_pi n
  simp [sinInvSeq, hsin, hcos]

lemma sin_inv_seq_values' (n : ℕ) :
    Real.sin ((sinInvSeq n)⁻¹) = (-1 : ℝ) ^ n := by
  simpa [one_div] using sin_inv_seq_values n

lemma pow_neg_one_not_convergent :
    ¬ ∃ L : ℝ,
        Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (𝓝 L) := by
  classical
  intro h
  rcases h with ⟨L, hL⟩
  have hhalf :=
    (Metric.tendsto_nhds.1 hL) ((1 : ℝ) / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hhalf
  have hN_le_even : N ≤ 2 * N := by
    have : (1 : ℕ) ≤ 2 := by decide
    simpa [one_mul] using (Nat.mul_le_mul_right N this)
  have hN_le_odd : N ≤ 2 * N + 1 := by
    exact Nat.le_trans hN_le_even (Nat.le_succ _)
  have h_even :
      |(-1 : ℝ) ^ (2 * N) - L| < (1 : ℝ) / 2 :=
    hN (2 * N) hN_le_even
  have h_odd :
      |(-1 : ℝ) ^ (2 * N + 1) - L| < (1 : ℝ) / 2 :=
    hN (2 * N + 1) hN_le_odd
  have h_even_val : (-1 : ℝ) ^ (2 * N) = 1 := by
    have htwo : (-1 : ℝ) ^ 2 = 1 := by norm_num
    calc
      (-1 : ℝ) ^ (2 * N)
          = ((-1 : ℝ) ^ 2) ^ N := (pow_mul (-1 : ℝ) 2 N)
      _ = (1 : ℝ) ^ N := by simp [htwo]
      _ = 1 := by simp
  have h_odd_val : (-1 : ℝ) ^ (2 * N + 1) = -1 := by
    have hpow := pow_add (-1 : ℝ) (2 * N) 1
    simp [pow_one, h_even_val] at hpow
    exact hpow
  have hsum_lt :
      |1 - L| + |-1 - L| < 1 := by
    have h1 := h_even
    have h2 := h_odd
    simp [h_even_val] at h1
    simp [h_odd_val] at h2
    have hsum' := add_lt_add h1 h2
    have hden : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
    exact lt_of_lt_of_eq hsum' hden
  have htriangle' :
      |(1 : ℝ) - (-1 : ℝ)| ≤ |1 - L| + |-1 - L| := by
    have haux := abs_sub_le (1 : ℝ) L (-1)
    simpa [abs_sub_comm] using haux
  have htriangle : (2 : ℝ) ≤ |1 - L| + |-1 - L| := by
    have htwo : |(1 : ℝ) - (-1 : ℝ)| = (2 : ℝ) := by norm_num
    exact htwo ▸ htriangle'
  have hcontr : (2 : ℝ) < 1 :=
    lt_of_le_of_lt htriangle hsum_lt
  exact not_lt_of_ge (by norm_num : (2 : ℝ) ≥ 1) hcontr

lemma seq_mul_sin_inv_tendsto_zero {v : ℕ → ℝ}
    (hv_zero : Tendsto v atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => v n * Real.sin (1 / v n)) atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hball :=
    (Metric.tendsto_nhds.1 hv_zero) ε hε
  refine hball.mono ?_
  intro n hn
  have hbound :
      |v n * Real.sin (1 / v n)| ≤ |v n| := by
    have hsin_le : |Real.sin (1 / v n)| ≤ 1 :=
      Real.abs_sin_le_one (1 / v n)
    have hnonneg : 0 ≤ |v n| := abs_nonneg _
    calc
      |v n * Real.sin (1 / v n)| = |v n| * |Real.sin (1 / v n)| := by
        simp [abs_mul]
      _ ≤ |v n| * 1 :=
        mul_le_mul_of_nonneg_left hsin_le hnonneg
      _ = |v n| := by simp
  have hn_abs : |v n| < ε := by
    simpa [Real.dist_eq, sub_eq_add_neg] using hn
  have hlt : |v n * Real.sin (1 / v n)| < ε :=
    lt_of_le_of_lt hbound hn_abs
  simpa [Real.dist_eq, sub_eq_add_neg] using hlt

/-- Example 3.1.8: The limit of `sin (1 / x)` as `x → 0` does not exist, but the
limit of `x * sin (1 / x)` as `x → 0` equals `0`. -/
lemma sin_inv_no_limit :
    ¬ ∃ L : ℝ, LimitWithin Set.univ (fun x : ℝ => Real.sin (1 / x)) 0 L := by
  intro h
  rcases h with ⟨L, hL⟩
  have hmem : ∀ n : ℕ, sinInvSeq n ∈ Set.univ \ {0} := fun n =>
    ⟨trivial, by simpa [Set.mem_singleton_iff] using sinInvSeq_ne_zero n⟩
  have hseq :=
    ((limitWithin_iff_seq_tendsto (S := Set.univ)
        (f := fun x : ℝ => Real.sin (1 / x)) 0 L).mp hL).2
      sinInvSeq hmem sin_inv_seq_tendsto
  have hpow : Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (𝓝 L) := by
    simpa [sin_inv_seq_values'] using hseq
  exact pow_neg_one_not_convergent ⟨L, hpow⟩

/-- The product `x * sin (1 / x)` converges to `0` as `x → 0`. -/
lemma limit_mul_sin_inv :
    LimitWithin Set.univ (fun x : ℝ => x * Real.sin (1 / x)) 0 0 := by
  have hcluster : IsClusterPoint Set.univ 0 := by
    intro ε hε
    have hx_pos : 0 < ε / 2 := half_pos hε
    have hx_left : -ε < ε / 2 := by
      have := hε
      linarith
    have hx_right : ε / 2 < ε := by
      simpa using half_lt_self hε
    refine ⟨ε / 2, ?_⟩
    have hxIoo :
        ε / 2 ∈ Set.Ioo (0 - ε) (0 + ε) := ⟨by simpa [sub_eq_add_neg] using hx_left,
      by simpa using hx_right⟩
    have hx_ne : ε / 2 ≠ 0 := ne_of_gt hx_pos
    exact ⟨⟨hxIoo, trivial⟩, by simpa [Set.mem_singleton_iff] using hx_ne⟩
  refine
    ((limitWithin_iff_seq_tendsto (S := Set.univ)
        (f := fun x : ℝ => x * Real.sin (1 / x)) 0 0).2 ?_)
  refine ⟨hcluster, ?_⟩
  intro u hu_mem hu_tendsto
  have hlimit := seq_mul_sin_inv_tendsto_zero hu_tendsto
  simpa using hlimit

/-- If two real sequences converge and one bounds the other termwise,
then their limits respect the same inequality. -/
lemma seq_limit_le {a b : ℕ → ℝ} {L₁ L₂ : ℝ}
    (ha : Tendsto a atTop (𝓝 L₁)) (hb : Tendsto b atTop (𝓝 L₂))
    (hmono : ∀ n, a n ≤ b n) :
    L₁ ≤ L₂ := by
  classical
  by_contra h
  have hlt : L₂ < L₁ := lt_of_not_ge h
  set δ := (L₁ - L₂) / 2 with hδ
  have hδ_def : δ = (L₁ - L₂) / 2 := hδ
  have hδ_pos : 0 < δ := by
    have : 0 < (L₁ - L₂) / 2 := div_pos (sub_pos.mpr hlt) (by norm_num)
    simpa [hδ_def] using this
  have hsub_eq : L₁ - (L₂ + δ) = δ := by
    calc
      L₁ - (L₂ + δ) = L₁ - L₂ - δ := by ring
      _ = L₁ - L₂ - (L₁ - L₂) / 2 := by
        simp [hδ_def]
      _ = (L₁ - L₂) / 2 := by ring
      _ = δ := by
        simp [hδ_def]
  have hLf_mem : L₁ ∈ Set.Ioi (L₂ + δ) := by
    have hdiff_pos : 0 < L₁ - (L₂ + δ) := by
      simpa [hsub_eq] using hδ_pos
    have : L₂ + δ < L₁ := sub_pos.1 hdiff_pos
    exact (Set.mem_Ioi).2 this
  have hLg_mem : L₂ ∈ Set.Iio (L₂ + δ) := by
    refine Set.mem_Iio.2 ?_
    have hlt' : L₂ < L₂ + δ := by
      simpa using add_lt_add_left hδ_pos L₂
    exact hlt'
  have ha_event :
      (fun n => a n) ⁻¹' Set.Ioi (L₂ + δ) ∈ atTop :=
    (tendsto_nhds.1 ha) _ isOpen_Ioi hLf_mem
  have hb_event :
      (fun n => b n) ⁻¹' Set.Iio (L₂ + δ) ∈ atTop :=
    (tendsto_nhds.1 hb) _ isOpen_Iio hLg_mem
  obtain ⟨Na, hNa⟩ := eventually_atTop.1 ha_event
  obtain ⟨Nb, hNb⟩ := eventually_atTop.1 hb_event
  let N := max Na Nb
  have hNa' : Na ≤ N := le_max_left _ _
  have hNb' : Nb ≤ N := le_max_right _ _
  have hgt : L₂ + δ < a N :=
    Set.mem_Ioi.1 (hNa N hNa')
  have hlt' : b N < L₂ + δ :=
    Set.mem_Iio.1 (hNb N hNb')
  have hcontr : ¬ a N ≤ b N :=
    not_le_of_gt ((lt_trans hlt' hgt))
  exact hcontr (hmono N)

/-- Corollary 3.1.9: If `c` is a cluster point of `S ⊆ ℝ`, `f, g : ℝ → ℝ`
have limits `L_f, L_g` as `x → c` within `S`, and `f x ≤ g x` for all
`x ∈ S \ {c}`, then `L_f ≤ L_g`. -/
lemma limitWithin_le_of_le {S : Set ℝ} {c Lf Lg : ℝ} {f g : ℝ → ℝ}
    (hf : LimitWithin S f c Lf) (hg : LimitWithin S g c Lg)
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → f x ≤ g x) :
    Lf ≤ Lg := by
  classical
  have hc : IsClusterPoint S c := hf.1
  obtain ⟨x, hxS, hx_lim⟩ :=
    (isClusterPoint_iff_exists_seq_tendsto S c).mp hc
  have hx_mem : ∀ n, x n ∈ S \ {c} := fun n =>
    ⟨(hxS n).1, by simpa [Set.mem_singleton_iff] using (hxS n).2⟩
  have hf_seq :=
    ((limitWithin_iff_seq_tendsto S f c Lf).mp hf).2 x hx_mem hx_lim
  have hg_seq :=
    ((limitWithin_iff_seq_tendsto S g c Lg).mp hg).2 x hx_mem hx_lim
  have hpointwise : ∀ n, f (x n) ≤ g (x n) := fun n =>
    hfg (hxS n).1 (hxS n).2
  exact seq_limit_le hf_seq hg_seq hpointwise

/-- Corollary 3.1.10: If `c` is a cluster point of `S ⊆ ℝ`, `f : ℝ → ℝ` has a
limit `L` as `x → c` within `S`, and `a ≤ f x ≤ b` for all `x ∈ S \ {c}`, then
`a ≤ L ≤ b`. -/
lemma limitWithin_mem_interval {S : Set ℝ} {c L a b : ℝ} {f : ℝ → ℝ}
    (hlim : LimitWithin S f c L)
    (hbounds : ∀ ⦃x : ℝ⦄, x ∈ S \ {c} → a ≤ f x ∧ f x ≤ b) :
    a ≤ L ∧ L ≤ b := by
  have hcluster : IsClusterPoint S c := hlim.1
  have hconst_a : LimitWithin S (fun _ => a) c a := by
    refine (limitWithin_iff_tendsto S (fun _ => a) c a).2 ?_
    refine ⟨hcluster, ?_⟩
    simpa using (tendsto_const_nhds : Tendsto (fun _ => a) (𝓝[S \ {c}] c) (𝓝 a))
  have hconst_b : LimitWithin S (fun _ => b) c b := by
    refine (limitWithin_iff_tendsto S (fun _ => b) c b).2 ?_
    refine ⟨hcluster, ?_⟩
    simpa using (tendsto_const_nhds : Tendsto (fun _ => b) (𝓝[S \ {c}] c) (𝓝 b))
  have hle : a ≤ L := by
    refine limitWithin_le_of_le (f := fun _ => a) (g := f) hconst_a hlim ?_
    intro x hxS hxne
    have hx : x ∈ S \ {c} := (mem_diff_singleton_iff).2 ⟨hxS, hxne⟩
    exact (hbounds hx).1
  have hge : L ≤ b := by
    refine limitWithin_le_of_le (f := f) (g := fun _ => b) hlim hconst_b ?_
    intro x hxS hxne
    have hx : x ∈ S \ {c} := (mem_diff_singleton_iff).2 ⟨hxS, hxne⟩
    exact (hbounds hx).2
  exact ⟨hle, hge⟩

/-- Corollary 3.1.11 (squeeze theorem): Let `S ⊆ ℝ` and `c` be a cluster point
of `S`. If `f, g, h : ℝ → ℝ` satisfy `f x ≤ g x ≤ h x` for all `x ∈ S \ {c}`
and `f` and `h` both have limit `L` as `x → c` within `S`, then `g` also has
limit `L` as `x → c` within `S`. -/
lemma limitWithin_squeeze {S : Set ℝ} {c L : ℝ} {f g h : ℝ → ℝ}
    (hf : LimitWithin S f c L) (hh : LimitWithin S h c L)
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → f x ≤ g x)
    (hgh : ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → g x ≤ h x) :
    LimitWithin S g c L := by
  classical
  refine (limitWithin_iff_seq_tendsto S g c L).2 ?_
  refine ⟨hf.1, ?_⟩
  intro u hu_mem hu_tendsto
  have hf_seq :=
    ((limitWithin_iff_seq_tendsto S f c L).1 hf).2 u hu_mem hu_tendsto
  have hh_seq :=
    ((limitWithin_iff_seq_tendsto S h c L).1 hh).2 u hu_mem hu_tendsto
  have hfg_seq : ∀ n, f (u n) ≤ g (u n) := by
    intro n
    have hxS : u n ∈ S := (hu_mem n).1
    have hxne : u n ≠ c := by
      have hxne' : u n ∉ ({c} : Set ℝ) := (hu_mem n).2
      simpa [Set.mem_singleton_iff] using hxne'
    exact hfg hxS hxne
  have hgh_seq : ∀ n, g (u n) ≤ h (u n) := by
    intro n
    have hxS : u n ∈ S := (hu_mem n).1
    have hxne : u n ≠ c := by
      have hxne' : u n ∉ ({c} : Set ℝ) := (hu_mem n).2
      simpa [Set.mem_singleton_iff] using hxne'
    exact hgh hxS hxne
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hf_seq hh_seq hfg_seq hgh_seq

/-- Corollary 3.1.12: Let `S ⊆ ℝ` and `c` be a cluster point of `S`. If
`f, g : ℝ → ℝ` have limits as `x → c` within `S`, then (i) the limit of
`f + g` equals the sum of the limits, (ii) the limit of `f - g` equals the
difference of the limits, (iii) the limit of `f * g` equals the product of the
limits, and (iv) if the limit of `g` is nonzero and `g x ≠ 0` for all
`x ∈ S \ {c}`, then the limit of `f / g` equals the quotient of the limits. -/
lemma limitWithin_add {S : Set ℝ} {c Lf Lg : ℝ} {f g : ℝ → ℝ}
    (hf : LimitWithin S f c Lf) (hg : LimitWithin S g c Lg) :
    LimitWithin S (fun x => f x + g x) c (Lf + Lg) := by
  have hfT : Tendsto f (𝓝[S \ {c}] c) (𝓝 Lf) :=
    (limitWithin_iff_tendsto S f c Lf).1 hf |>.2
  have hgT : Tendsto g (𝓝[S \ {c}] c) (𝓝 Lg) :=
    (limitWithin_iff_tendsto S g c Lg).1 hg |>.2
  refine (limitWithin_iff_tendsto S (fun x => f x + g x) c (Lf + Lg)).2 ?_
  refine ⟨hf.1, ?_⟩
  simpa using (Filter.Tendsto.add hfT hgT)

lemma limitWithin_sub {S : Set ℝ} {c Lf Lg : ℝ} {f g : ℝ → ℝ}
    (hf : LimitWithin S f c Lf) (hg : LimitWithin S g c Lg) :
    LimitWithin S (fun x => f x - g x) c (Lf - Lg) := by
  have hfT : Tendsto f (𝓝[S \ {c}] c) (𝓝 Lf) :=
    (limitWithin_iff_tendsto S f c Lf).1 hf |>.2
  have hgT : Tendsto g (𝓝[S \ {c}] c) (𝓝 Lg) :=
    (limitWithin_iff_tendsto S g c Lg).1 hg |>.2
  have hneg : Tendsto (fun x => -g x) (𝓝[S \ {c}] c) (𝓝 (-Lg)) :=
    Filter.Tendsto.neg hgT
  refine (limitWithin_iff_tendsto S (fun x => f x - g x) c (Lf - Lg)).2 ?_
  refine ⟨hf.1, ?_⟩
  have hsum : Tendsto (fun x => f x + -g x) (𝓝[S \ {c}] c) (𝓝 (Lf + -Lg)) :=
    Filter.Tendsto.add hfT hneg
  simpa [sub_eq_add_neg] using hsum

lemma limitWithin_mul {S : Set ℝ} {c Lf Lg : ℝ} {f g : ℝ → ℝ}
    (hf : LimitWithin S f c Lf) (hg : LimitWithin S g c Lg) :
    LimitWithin S (fun x => f x * g x) c (Lf * Lg) := by
  have hfT : Tendsto f (𝓝[S \ {c}] c) (𝓝 Lf) :=
    (limitWithin_iff_tendsto S f c Lf).1 hf |>.2
  have hgT : Tendsto g (𝓝[S \ {c}] c) (𝓝 Lg) :=
    (limitWithin_iff_tendsto S g c Lg).1 hg |>.2
  refine (limitWithin_iff_tendsto S (fun x => f x * g x) c (Lf * Lg)).2 ?_
  refine ⟨hf.1, ?_⟩
  simpa using (Filter.Tendsto.mul hfT hgT)

lemma limitWithin_div {S : Set ℝ} {c Lf Lg : ℝ} {f g : ℝ → ℝ}
    (hf : LimitWithin S f c Lf) (hg : LimitWithin S g c Lg)
    (hg0 : ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → g x ≠ 0) (hL0 : Lg ≠ 0) :
    LimitWithin S (fun x => f x / g x) c (Lf / Lg) := by
  have hg0' := hg0
  have hfT : Tendsto f (𝓝[S \ {c}] c) (𝓝 Lf) :=
    (limitWithin_iff_tendsto S f c Lf).1 hf |>.2
  have hgT : Tendsto g (𝓝[S \ {c}] c) (𝓝 Lg) :=
    (limitWithin_iff_tendsto S g c Lg).1 hg |>.2
  refine (limitWithin_iff_tendsto S (fun x => f x / g x) c (Lf / Lg)).2 ?_
  refine ⟨hf.1, ?_⟩
  simpa using (Filter.Tendsto.div hfT hgT hL0)

/-- Corollary 3.1.13: If `S ⊆ ℝ`, `c` is a cluster point of `S`, and the limit
`lim_{x → c, x ∈ S} f x` exists for a function `f : ℝ → ℝ`, then the limit of
`|f x|` as `x → c` within `S` equals the absolute value of the limit of `f`. -/
lemma limitWithin_abs {S : Set ℝ} {c L : ℝ} {f : ℝ → ℝ}
    (hlim : LimitWithin S f c L) :
    LimitWithin S (fun x => |f x|) c |L| := by
  have hfT : Tendsto f (𝓝[S \ {c}] c) (𝓝 L) :=
    (limitWithin_iff_tendsto S f c L).1 hlim |>.2
  refine (limitWithin_iff_tendsto S (fun x => |f x|) c |L|).2 ?_
  refine ⟨hlim.1, ?_⟩
  have hcont : Tendsto (fun x : ℝ => |x|) (𝓝 L) (𝓝 |L|) := by
    simpa using
      (continuous_abs.continuousAt : ContinuousAt (fun x : ℝ => |x|) L).tendsto
  exact hcont.comp hfT

/-- Definition 3.1.14: For a function `f : S → ℝ` and a subset `A ⊆ S`, the
restriction `f|_A : A → ℝ` is given by `f|_A x = f x` for `x ∈ A`. -/
def restrictToSubset {S A : Set ℝ} (f : S → ℝ) (hAS : A ⊆ S) : A → ℝ :=
  fun x => f ⟨x, hAS x.property⟩

/-- Proposition 3.1.15(i): If `A ⊆ S ⊆ ℝ` agree with `S` on a punctured
neighborhood of `c` (i.e., there exists `α > 0` with `(A \ {c}) ∩ (c-α, c+α) =
(S \ {c}) ∩ (c-α, c+α)`), then `c` is a cluster point of `A` iff it is a cluster
point of `S`. -/
lemma clusterPoint_iff_of_local_agree
    {S A : Set ℝ} {c α : ℝ}
    (hα : 0 < α)
    (hA : (A \ {c}) ∩ Set.Ioo (c - α) (c + α) =
          (S \ {c}) ∩ Set.Ioo (c - α) (c + α)) :
    IsClusterPoint A c ↔ IsClusterPoint S c := by
  constructor
  · intro hA_cluster ε hε
    let δ := min ε α
    have hδ_pos : 0 < δ := lt_min hε hα
    have hδ_le : δ ≤ α := min_le_right ε α
    have ⟨x, hx⟩ := hA_cluster hδ_pos
    rcases hx with ⟨hxIooA, hx_ne⟩
    rcases hxIooA with ⟨hx_small, hxA⟩
    have hx_big : x ∈ Set.Ioo (c - α) (c + α) := by
      have hleft : c - α < x := lt_of_le_of_lt (sub_le_sub_left hδ_le c) hx_small.1
      have hright : x < c + α :=
        lt_of_lt_of_le hx_small.2 (by simpa [add_comm] using add_le_add_left hδ_le c)
      exact Set.mem_Ioo.2 ⟨hleft, hright⟩
    have hxA_big : x ∈ (A \ {c}) ∩ Set.Ioo (c - α) (c + α) := by
      exact ⟨⟨hxA, hx_ne⟩, hx_big⟩
    have hxS_big : x ∈ (S \ {c}) ∩ Set.Ioo (c - α) (c + α) := by
      rwa [hA] at hxA_big
    have hδ_le' : δ ≤ ε := min_le_left ε α
    have hIoo_small : x ∈ Set.Ioo (c - δ) (c + δ) := hx_small
    have ⟨hxS_diff, _⟩ := hxS_big
    have ⟨hS_mem, _⟩ := hxS_diff
    have hIoo_big : x ∈ Set.Ioo (c - ε) (c + ε) := by
      have hleft_big : c - ε < x := by
        have hneg : -ε ≤ -δ := neg_le_neg hδ_le'
        have hleft_le := add_le_add_left hneg c
        have hleft_le' : c - ε ≤ c - δ := by
          simpa [sub_eq_add_neg, add_comm] using hleft_le
        exact lt_of_le_of_lt hleft_le' hx_small.1
      have hright_big : x < c + ε :=
        lt_of_lt_of_le hx_small.2 (by simpa [add_comm] using add_le_add_left hδ_le' c)
      exact Set.mem_Ioo.2 ⟨hleft_big, hright_big⟩
    have hset : x ∈ (Set.Ioo (c - ε) (c + ε) ∩ S) \ {c} := by
      constructor
      · constructor
        · exact hIoo_big
        · exact hS_mem
      · exact hx_ne
    exact ⟨x, hset⟩
  · intro hS_cluster ε hε
    let δ := min ε α
    have hδ_pos : 0 < δ := lt_min hε hα
    have hδ_le : δ ≤ α := min_le_right ε α
    have ⟨x, hx⟩ := hS_cluster hδ_pos
    rcases hx with ⟨hxIooS, hx_ne⟩
    rcases hxIooS with ⟨hx_small, hxS⟩
    have hx_big : x ∈ Set.Ioo (c - α) (c + α) := by
      have hleft : c - α < x := lt_of_le_of_lt (sub_le_sub_left hδ_le c) hx_small.1
      have hright : x < c + α :=
        lt_of_lt_of_le hx_small.2 (by simpa [add_comm] using add_le_add_left hδ_le c)
      exact Set.mem_Ioo.2 ⟨hleft, hright⟩
    have hxS_big : x ∈ (S \ {c}) ∩ Set.Ioo (c - α) (c + α) := by
      exact ⟨⟨hxS, hx_ne⟩, hx_big⟩
    have hxA_big : x ∈ (A \ {c}) ∩ Set.Ioo (c - α) (c + α) := by
      rwa [Eq.symm hA] at hxS_big
    have hδ_le' : δ ≤ ε := min_le_left ε α
    have hIoo_small : x ∈ Set.Ioo (c - δ) (c + δ) := hx_small
    have ⟨hxA_diff, _⟩ := hxA_big
    have ⟨hA_mem, _⟩ := hxA_diff
    have hIoo_big : x ∈ Set.Ioo (c - ε) (c + ε) := by
      have hleft_big : c - ε < x := by
        have hneg : -ε ≤ -δ := neg_le_neg hδ_le'
        have hleft_le := add_le_add_left hneg c
        have hleft_le' : c - ε ≤ c - δ := by
          simpa [sub_eq_add_neg, add_comm] using hleft_le
        exact lt_of_le_of_lt hleft_le' hx_small.1
      have hright_big : x < c + ε :=
        lt_of_lt_of_le hx_small.2 (by simpa [add_comm] using add_le_add_left hδ_le' c)
      exact Set.mem_Ioo.2 ⟨hleft_big, hright_big⟩
    have hset : x ∈ (Set.Ioo (c - ε) (c + ε) ∩ A) \ {c} := by
      constructor
      · constructor
        · exact hIoo_big
        · exact hA_mem
      · exact hx_ne
    exact ⟨x, hset⟩

/-- The ε–δ condition for the limit within `S` implies the corresponding
condition within `A` provided the sets coincide on a punctured neighborhood of
`c`. -/
lemma limitWithin_imp_of_local_agree
    {S A : Set ℝ} {c α L : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α)
    (hA : (A \ {c}) ∩ Set.Ioo (c - α) (c + α) =
          (S \ {c}) ∩ Set.Ioo (c - α) (c + α))
    (hlim : ∀ ⦃ε : ℝ⦄, 0 < ε →
        ∃ δ > 0,
          ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε) :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ δ > 0,
        ∀ ⦃x : ℝ⦄, x ∈ A → x ≠ c → |x - c| < δ → |f x - L| < ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_cond⟩ := hlim hε
  let δ' := min δ α
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hα
  have hδ'_α : δ' ≤ α := min_le_right _ _
  have hδ'_δ : δ' ≤ δ := min_le_left _ _
  refine ⟨δ', hδ'_pos, ?_⟩
  intro x hxA hx_ne hx_lt
  have hx_small : x ∈ Set.Ioo (c - δ') (c + δ') := by
    have habs := abs_lt.1 hx_lt
    have hleft_small : c - δ' < x := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using add_lt_add_right habs.1 c
    have hright_small : x < c + δ' := by
      simpa [add_comm, add_left_comm, add_assoc]
        using add_lt_add_right habs.2 c
    exact Set.mem_Ioo.2 ⟨hleft_small, hright_small⟩
  have hx_big : x ∈ Set.Ioo (c - α) (c + α) := by
    have ⟨hleft_small, hright_small⟩ := Set.mem_Ioo.1 hx_small
    have hleft : c - α < x :=
      lt_of_le_of_lt (sub_le_sub_left hδ'_α c) hleft_small
    have hright : x < c + α :=
      lt_of_lt_of_le hright_small
        (by simpa [add_comm, add_left_comm, add_assoc]
            using add_le_add_left hδ'_α c)
    exact Set.mem_Ioo.2 ⟨hleft, hright⟩
  have hxA_big : x ∈ (A \ {c}) ∩ Set.Ioo (c - α) (c + α) :=
    ⟨⟨hxA, hx_ne⟩, hx_big⟩
  have hxS_big : x ∈ (S \ {c}) ∩ Set.Ioo (c - α) (c + α) := by
    rwa [hA] at hxA_big
  have hxS_diff : x ∈ S \ {c} := hxS_big.1
  have hS_mem : x ∈ S := hxS_diff.1
  have hδ_lt : |x - c| < δ := lt_of_lt_of_le hx_lt hδ'_δ
  exact hδ_cond hS_mem hx_ne hδ_lt

/-- Proposition 3.1.15(ii): Under the same local agreement near `c` and assuming
`c` is a cluster point of `S`, the limit of `f` along `S` at `c` equals that of
its restriction to `A`. -/
lemma limitWithin_iff_of_local_agree
    {S A : Set ℝ} {c α L : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α)
    (hA : (A \ {c}) ∩ Set.Ioo (c - α) (c + α) =
          (S \ {c}) ∩ Set.Ioo (c - α) (c + α))
    (_ : IsClusterPoint S c) :
    LimitWithin S f c L ↔ LimitWithin A f c L := by
  have h_cluster :
      IsClusterPoint S c ↔ IsClusterPoint A c :=
    (clusterPoint_iff_of_local_agree hα hA).symm
  have h_tendsto :
      (∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0,
          ∀ ⦃x : ℝ⦄, x ∈ S → x ≠ c → |x - c| < δ → |f x - L| < ε) ↔
        (∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0,
          ∀ ⦃x : ℝ⦄, x ∈ A → x ≠ c → |x - c| < δ → |f x - L| < ε) := by
    constructor
    · exact limitWithin_imp_of_local_agree hα hA
    · exact limitWithin_imp_of_local_agree hα hA.symm
  exact and_congr h_cluster h_tendsto

/-- Definition 3.1.16: For a function `f : ℝ → ℝ`, the right-hand limit of `f`
at `c` along a set `S` is the limit of the restriction of `f` to `S ∩ (c, ∞)`
as `x → c`. The left-hand limit is defined analogously using `S ∩ (-∞, c)`. -/
def RightLimitWithin (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) : Prop :=
  LimitWithin (S ∩ Set.Ioi c) f c L

/-- The left-hand limit of `f` at `c` along `S`, given by restricting to
`S ∩ (-∞, c)` and taking the limit as `x → c`. -/
def LeftLimitWithin (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) : Prop :=
  LimitWithin (S ∩ Set.Iio c) f c L

/-- Right-hand limits coincide with mathlib's `Tendsto` along the `𝓝` within
the right half-neighborhood. -/
lemma rightLimitWithin_iff_tendsto (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) :
    RightLimitWithin S f c L ↔
      IsClusterPoint (S ∩ Set.Ioi c) c ∧
        Tendsto f (𝓝[S ∩ Set.Ioi c] c) (𝓝 L) := by
  simpa [RightLimitWithin] using
    (limitWithin_iff_tendsto (S := S ∩ Set.Ioi c) (f := f) c L)

/-- Left-hand limits coincide with mathlib's `Tendsto` along the `𝓝` within
the left half-neighborhood. -/
lemma leftLimitWithin_iff_tendsto (S : Set ℝ) (f : ℝ → ℝ) (c L : ℝ) :
    LeftLimitWithin S f c L ↔
      IsClusterPoint (S ∩ Set.Iio c) c ∧
        Tendsto f (𝓝[S ∩ Set.Iio c] c) (𝓝 L) := by
  simpa [LeftLimitWithin] using
    (limitWithin_iff_tendsto (S := S ∩ Set.Iio c) (f := f) c L)

/-- Proposition 3.1.17: If `c` is a cluster point of both `S ∩ (-∞, c)` and
`S ∩ (c, ∞)`, then `c` is a cluster point of `S`, and `f(x) → L` as `x → c`
within `S` iff both the left-hand and right-hand limits along `S` equal `L`. -/
lemma limitWithin_iff_left_right {S : Set ℝ} {c L : ℝ} {f : ℝ → ℝ}
    (hleft : IsClusterPoint (S ∩ Set.Iio c) c)
    (hright : IsClusterPoint (S ∩ Set.Ioi c) c) :
    IsClusterPoint S c ∧
      (LimitWithin S f c L ↔
        LeftLimitWithin S f c L ∧ RightLimitWithin S f c L) := by
  have hSc : IsClusterPoint S c := by
    intro ε hε
    rcases hright hε with ⟨x, hx⟩
    rcases hx with ⟨hx_inner, hx_ne⟩
    rcases hx_inner with ⟨hx_Ioo, hx_SIoi⟩
    have hset : x ∈ (Set.Ioo (c - ε) (c + ε) ∩ S) \ {c} := by
      constructor
      · constructor
        · exact hx_Ioo
        · exact hx_SIoi.1
      · exact hx_ne
    exact ⟨x, hset⟩
  have limit_iff :
      LimitWithin S f c L ↔
        LimitWithin (S ∩ Set.Iio c) f c L ∧ LimitWithin (S ∩ Set.Ioi c) f c L := by
    refine
      ⟨fun hf =>
        ⟨⟨hleft, fun ε hε => by
            rcases hf.2 hε with ⟨δ, hδpos, hδ⟩
            use δ, hδpos
            intro x hxs hxc hlt
            exact hδ (hxs.1) hxc hlt⟩,
        ⟨hright, fun ε hε => by
            rcases hf.2 hε with ⟨δ, hδpos, hδ⟩
            use δ, hδpos
            intro x hxs hxc hlt
            exact hδ (hxs.1) hxc hlt⟩⟩,
       fun ⟨hl, hr⟩ =>
        ⟨hSc, fun ε hε => by
            rcases hl.2 hε with ⟨δl, hδl_pos, hδl⟩
            rcases hr.2 hε with ⟨δr, hδr_pos, hδr⟩
            let δ := min δl δr
            have hδ_pos : 0 < δ := lt_min hδl_pos hδr_pos
            use δ, hδ_pos
            intro x hxs hxc hdist
            have hcases := lt_or_gt_of_ne hxc
            rcases hcases with hlt | hgt
            · have hxs_left : x ∈ S ∩ Set.Iio c := ⟨hxs, hlt⟩
              have hdist' : |x - c| < δl := lt_of_lt_of_le hdist (min_le_left _ _)
              exact hδl hxs_left hxc hdist'
            · have hxs_right : x ∈ S ∩ Set.Ioi c := ⟨hxs, hgt⟩
              have hdist' : |x - c| < δr := lt_of_lt_of_le hdist (min_le_right _ _)
              exact hδr hxs_right hxc hdist'⟩⟩
  exact ⟨hSc, by simpa [LeftLimitWithin, RightLimitWithin] using limit_iff⟩

end Section01
end Chap03
