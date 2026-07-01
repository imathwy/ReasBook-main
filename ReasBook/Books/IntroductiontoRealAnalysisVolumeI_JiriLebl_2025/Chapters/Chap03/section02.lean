/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open Filter
open Metric
open scoped Topology Rat

section Chap03
section Section02

/-- Definition 3.2.1. A function `f : S → ℝ` is continuous at a point `c ∈ S`
if for every `ε > 0` there exists `δ > 0` such that whenever `x ∈ S` satisfies
`|x - c| < δ`, then `|f x - f c| < ε`. A function is continuous on `S` if it is
continuous at every point of `S`. -/
def continuousAtInSet (S : Set ℝ) (f : S → ℝ) (c : S) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : S, |(x : ℝ) - (c : ℝ)| < δ → |f x - f c| < ε

/-- A function `f : S → ℝ` is continuous on `S` when it is continuous at every
point of `S`. -/
def continuousOnSet (S : Set ℝ) (f : S → ℝ) : Prop :=
  ∀ c : S, continuousAtInSet S f c

/-- The epsilon-delta continuity at a point agrees with mathlib's notion of
continuity for subtype domains. -/
theorem continuousAtInSet_iff (S : Set ℝ) (f : S → ℝ) (c : S) :
    continuousAtInSet S f c ↔ ContinuousAt f c := by
  constructor
  · intro h
    refine (continuousAt_iff).2 ?_
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have hx' : |(x : ℝ) - (c : ℝ)| < δ := by
      simpa [Real.dist_eq] using hx
    have hfx : |f x - f c| < ε := hδprop x hx'
    simpa [Real.dist_eq] using hfx
  · intro h
    have h' := (continuousAt_iff).1 h
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := h' ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have hx' : dist x c < δ := by
      simpa [Real.dist_eq] using hx
    have hfx : dist (f x) (f c) < ε := hδprop (x := x) hx'
    simpa [Real.dist_eq] using hfx

/-- Continuity on a set agrees with mathlib's `Continuous` for functions defined
on a subtype of `ℝ`. -/
theorem continuousOnSet_iff (S : Set ℝ) (f : S → ℝ) :
    continuousOnSet S f ↔ Continuous f := by
  constructor
  · intro h
    refine (continuous_iff_continuousAt).2 ?_
    intro c
    exact (continuousAtInSet_iff S f c).1 (h c)
  · intro h c
    have hc : ContinuousAt f c := (continuous_iff_continuousAt).1 h c
    exact (continuousAtInSet_iff S f c).2 hc

/-- Proposition 3.2.2. For a function `f : S → ℝ` on a set `S ⊆ ℝ` and a
point `c ∈ S`:
(i) if `c` is not a cluster point of `S`, then `f` is continuous at `c`;
(ii) if `c` is a cluster point of `S`, then `f` is continuous at `c` if and
only if `\lim_{x \to c} f x = f c`;
(iii) `f` is continuous at `c` if and only if for every sequence
`(x_n) ⊆ S` with `x_n → c`, one has `f (x_n) → f c`. -/
lemma proposition_3_2_2 (S : Set ℝ) (f : S → ℝ) (c : S) :
    (¬ (c : ℝ) ∈ closure (S \ ({(c : ℝ)} : Set ℝ)) →
      ContinuousAt f c) ∧
    ((c : ℝ) ∈ closure (S \ ({(c : ℝ)} : Set ℝ)) →
      (ContinuousAt f c ↔ Filter.Tendsto f (𝓝 c) (𝓝 (f c)))) ∧
    (ContinuousAt f c ↔
      ∀ u : ℕ → S,
        Filter.Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (c : ℝ)) →
          Filter.Tendsto (fun n => f (u n)) atTop (𝓝 (f c))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hnot
    set U := (closure (S \ ({(c : ℝ)} : Set ℝ)))ᶜ
    have hUopen : IsOpen U := (isClosed_closure).isOpen_compl
    have hUc : (c : ℝ) ∈ U := by simpa [U] using hnot
    have hpre :
        {x : S | (x : ℝ) ∈ U} = ({c} : Set S) := by
      ext x
      constructor
      · intro hx
        have hxnot :
            (x : ℝ) ∉ closure (S \ ({(c : ℝ)} : Set ℝ)) := by
          simpa [U] using hx
        by_contra hx_ne
        have hx_ne' : (x : ℝ) ≠ (c : ℝ) := by
          intro h
          apply hx_ne
          ext
          simp [h]
        have hx_mem :
            (x : ℝ) ∈ S \ ({(c : ℝ)} : Set ℝ) := by
          refine ⟨x.property, ?_⟩
          simpa [Set.mem_singleton_iff] using hx_ne'
        have hx_closure :
            (x : ℝ) ∈ closure (S \ ({(c : ℝ)} : Set ℝ)) :=
          subset_closure hx_mem
        exact hxnot hx_closure
      · intro hx
        have hx' : x = c := by
          simpa [Set.mem_singleton_iff] using hx
        change (x : ℝ) ∈ U
        simpa [hx', U] using hUc
    have hx_mem :
        {x : S | (x : ℝ) ∈ U} ∈ 𝓝 c := by
      have hopen :
          IsOpen {x : S | (x : ℝ) ∈ U} :=
        hUopen.preimage continuous_subtype_val
      have hcin : c ∈ {x : S | (x : ℝ) ∈ U} := by
        change (c : ℝ) ∈ U
        simpa [U] using hUc
      exact hopen.mem_nhds hcin
    have hsingleton :
        ({c} : Set S) ∈ 𝓝 c := by
      simpa [hpre] using hx_mem
    refine (_root_.tendsto_nhds.2 ?_)
    intro s hs_open hfc
    have hsubset :
        ({c} : Set S) ⊆ f ⁻¹' s := by
      intro x hx
      have hx' : x = c := by
        simpa [Set.mem_singleton_iff] using hx
      simp [hx', hfc]
    exact Filter.mem_of_superset hsingleton hsubset
  · intro _; rfl
  · constructor
    · intro hf u hu
      have hdist_real :
          Tendsto (fun n => dist ((u n : ℝ)) (c : ℝ)) atTop (𝓝 (0 : ℝ)) := by
        simpa [tendsto_iff_dist_tendsto_zero] using hu
      have hdist_sub :
          Tendsto (fun n => dist (u n) c) atTop (𝓝 (0 : ℝ)) := by
        simpa using hdist_real
      have hu_sub :
          Tendsto u atTop (𝓝 c) := by
        simpa [tendsto_iff_dist_tendsto_zero] using hdist_sub
      have hf_tend : Tendsto f (𝓝 c) (𝓝 (f c)) := hf
      exact hf_tend.comp hu_sub
    · intro hseq
      classical
      by_contra hcont
      have hnot :
          ¬ ∀ ε > 0,
              {x : S | dist (f x) (f c) < ε} ∈ 𝓝 c := by
        intro hprop
        exact hcont (Metric.tendsto_nhds.2 hprop)
      obtain ⟨ε, hε⟩ := not_forall.1 hnot
      have hε_pos_and :
          0 < ε ∧
            ({x : S | dist (f x) (f c) < ε} ∉ 𝓝 c) :=
        (_root_.not_imp.1 hε)
      rcases hε_pos_and with ⟨hε_pos, hε_fail⟩
      have hx_exists :
          ∀ δ > 0,
            ∃ x : S,
              dist (x : ℝ) (c : ℝ) < δ ∧
                ε ≤ dist (f x) (f c) := by
        intro δ hδ
        have hsubset :
            ¬ Metric.ball c δ ⊆ {x : S | dist (f x) (f c) < ε} := by
          intro hsub
          have hball : Metric.ball c δ ∈ 𝓝 c :=
            Metric.ball_mem_nhds c hδ
          have : {x : S | dist (f x) (f c) < ε} ∈ 𝓝 c :=
            Filter.mem_of_superset hball hsub
          exact hε_fail this
        obtain ⟨x, hx_ball, hx_not⟩ := Set.not_subset.1 hsubset
        have hx_dist :
            dist (x : ℝ) (c : ℝ) < δ := by
          simpa [Metric.mem_ball] using hx_ball
        have hx_ge :
            ε ≤ dist (f x) (f c) := by
          have hnot_lt :
              ¬ dist (f x) (f c) < ε := by
            simpa using hx_not
          exact le_of_not_gt hnot_lt
        exact ⟨x, hx_dist, hx_ge⟩
      have hδ_pos :
          ∀ n : ℕ, 0 < (1 : ℝ) / (n.succ : ℝ) := fun n =>
        one_div_pos.2 (by
          simpa using (Nat.cast_pos.2 (Nat.succ_pos n)))
      choose u hu using fun n : ℕ =>
        hx_exists ((1 : ℝ) / (n.succ : ℝ)) (hδ_pos n)
      have hu_dist :
          ∀ n : ℕ, dist ((u n : ℝ)) (c : ℝ) <
              (1 : ℝ) / (n.succ : ℝ) := fun n =>
        (hu n).1
      have hu_lower :
          ∀ n : ℕ, ε ≤ dist (f (u n)) (f c) := fun n =>
        (hu n).2
      have hu_tendsto_real :
          Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (c : ℝ)) := by
        have hnonneg :
            ∀ n, 0 ≤ dist ((u n : ℝ)) (c : ℝ) :=
          fun _ => dist_nonneg
        have hbound :
            ∀ n,
              dist ((u n : ℝ)) (c : ℝ) ≤
                (1 : ℝ) / (n.succ : ℝ) := fun n =>
          le_of_lt (hu_dist n)
        have hlim :
            Tendsto (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ))
              atTop (𝓝 (0 : ℝ)) := by
          simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have hdist_lim :
            Tendsto (fun n => dist ((u n : ℝ)) (c : ℝ))
              atTop (𝓝 (0 : ℝ)) :=
          Filter.Tendsto.squeeze tendsto_const_nhds hlim hnonneg hbound
        simpa [tendsto_iff_dist_tendsto_zero] using hdist_lim
      have hnot_tend :
          ¬ Tendsto (fun n => f (u n)) atTop (𝓝 (f c)) := by
        intro hlim
        have h_event :=
          (Metric.tendsto_nhds.1 hlim) ε hε_pos
        rcases eventually_atTop.1 h_event with ⟨N, hN⟩
        have hless : dist (f (u N)) (f c) < ε := hN N le_rfl
        have hge : ε ≤ dist (f (u N)) (f c) := hu_lower N
        exact (not_lt_of_ge hge) hless
      have hlim := hseq u hu_tendsto_real
      exact hnot_tend hlim

/-- Elements of the positive real subtype are nonzero. -/
lemma subtype_pos_ne_zero (x : {x : ℝ // 0 < x}) : (x : ℝ) ≠ 0 :=
  ne_of_gt x.property

/-- The reciprocal map is continuous at every point of `(0, ∞)`. -/
lemma continuousAt_inv_subtype (c : {x : ℝ // 0 < x}) :
    ContinuousAt (fun x : {x : ℝ // 0 < x} => (x : ℝ)⁻¹) c := by
  have h := (continuous_subtype_val :
      Continuous fun x : {x : ℝ // 0 < x} => (x : ℝ))
  have h₀ :
      ((fun x : {x : ℝ // 0 < x} => (x : ℝ)) c) ≠ 0 := by
    simpa using subtype_pos_ne_zero c
  simpa using h.continuousAt.inv₀ h₀

/-- Example 3.2.3. The reciprocal function `f : (0, ∞) → ℝ` given by
`f x = 1 / x` is continuous on its domain. -/
lemma example_3_2_3 : Continuous fun x : {x : ℝ // 0 < x} => (x : ℝ)⁻¹ := by
  refine (continuous_iff_continuousAt).2 ?_
  intro c
  simpa using continuousAt_inv_subtype c

/-- Proposition 3.2.4. A real polynomial `f(x) = a_d x^d + a_{d-1} x^{d-1} +
⋯ + a_1 x + a_0` defines a continuous function `ℝ → ℝ`. -/
lemma polynomial_continuous (p : Polynomial ℝ) :
    Continuous fun x : ℝ => p.eval x := by
  simpa using p.continuous

/-- Proposition 3.2.5. If `f, g : S → ℝ` are continuous at `c ∈ S`, then:
(i) the sum `x ↦ f x + g x` is continuous at `c`;
(ii) the difference `x ↦ f x - g x` is continuous at `c`;
(iii) the product `x ↦ f x * g x` is continuous at `c`;
(iv) if additionally `g x ≠ 0` for all `x ∈ S`, the quotient
`x ↦ f x / g x` is continuous at `c`. -/
lemma proposition_3_2_5 {S : Set ℝ} {f g : S → ℝ} {c : S}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c)
    (h0 : ∀ x : S, g x ≠ 0) :
    ContinuousAt (fun x : S => f x + g x) c ∧
      ContinuousAt (fun x : S => f x - g x) c ∧
      ContinuousAt (fun x : S => f x * g x) c ∧
      ContinuousAt (fun x : S => f x / g x) c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hf.add hg
  · simpa [sub_eq_add_neg] using hf.add hg.neg
  · simpa using hf.mul hg
  · simpa using hf.div hg (h0 c)

/-- Example 3.2.6. The sine and cosine functions on `ℝ` are continuous. The
book justifies this using trigonometric identities and the estimates
`|sin x| ≤ |x|`, `|cos x| ≤ 1`, and `|sin x| ≤ 1`. -/
lemma sin_is_continuous : Continuous fun x : ℝ => Real.sin x := by
  simpa using Real.continuous_sin

lemma cos_is_continuous : Continuous fun x : ℝ => Real.cos x := by
  simpa using Real.continuous_cos

lemma example_3_2_6 :
    Continuous (fun x : ℝ => Real.sin x) ∧
      Continuous (fun x : ℝ => Real.cos x) := by
  exact ⟨sin_is_continuous, cos_is_continuous⟩

/-- Helper lemma for Proposition 3.2.7: composing `hf` and `hg` gives the desired
continuity conclusion. -/
lemma comp_continuousAt_helper {A B : Set ℝ} {f : B → ℝ} {g : A → B} {c : A}
    (hf : ContinuousAt f (g c)) (hg : ContinuousAt g c) :
    ContinuousAt (fun x : A => f (g x)) c := by
  simpa [Function.comp] using hf.comp hg

/-- Proposition 3.2.7. If `g : A → B` is continuous at `c ∈ A` and
`f : B → ℝ` is continuous at `g c`, then the composition `f ∘ g : A → ℝ` is
continuous at `c`. -/
lemma composition_continuousAt {A B : Set ℝ} {f : B → ℝ} {g : A → B} {c : A}
    (hg : ContinuousAt g c) (hf : ContinuousAt f (g c)) :
    ContinuousAt (fun x : A => f (g x)) c := by
  simpa using comp_continuousAt_helper hf hg

/-- The reciprocal map is continuous on `(0, ∞)` when regarded as a function
`ℝ → ℝ`. -/
lemma continuousOn_inv_Ioi :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / x) (Set.Ioi 0) := by
  have hcont :
      ContinuousOn (fun x : ℝ => x) (Set.Ioi 0) :=
    (continuousOn_id : ContinuousOn (fun x : ℝ => x) (Set.Ioi 0))
  have hne :
      ∀ x ∈ Set.Ioi (0 : ℝ), x ≠ 0 := fun x hx => ne_of_gt hx
  simpa [one_div] using hcont.inv₀ hne

/-- Composing the reciprocal with the sine function yields a continuous
function on `(0, ∞)`. -/
lemma continuousOn_sin_inv :
    ContinuousOn (fun x : ℝ => Real.sin (1 / x)) (Set.Ioi 0) := by
  have hsin :
      ContinuousOn (fun y : ℝ => Real.sin y) (Set.univ : Set ℝ) :=
    Real.continuous_sin.continuousOn
  have hmaps :
      Set.MapsTo (fun x : ℝ => (1 : ℝ) / x) (Set.Ioi 0)
        (Set.univ : Set ℝ) := fun x _ => trivial
  have hcomp :=
      ContinuousOn.comp hsin continuousOn_inv_Ioi hmaps
  simpa [Function.comp, one_div] using hcomp

/-- Example 3.2.8. The function `x ↦ (sin (1 / x))^2` is continuous on the
open interval `(0, ∞)`. -/
lemma example_3_2_8 :
    ContinuousOn (fun x : ℝ => (Real.sin (1 / x)) ^ 2) (Set.Ioi 0) := by
  have hsin :
      ContinuousOn (fun x : ℝ => Real.sin (1 / x)) (Set.Ioi 0) :=
    continuousOn_sin_inv
  simpa [pow_two] using hsin.mul hsin

/-- Proposition 3.2.9. If there exists a sequence `(x_n)` in `S` converging to
`c` such that `(f (x_n))` does not converge to `f c`, then `f` is
discontinuous at `c`. -/
lemma proposition_3_2_9 {S : Set ℝ} {f : S → ℝ} {c : S}
    (h : ∃ u : ℕ → S,
      Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop (𝓝 (c : ℝ)) ∧
        ¬ Filter.Tendsto (fun n => f (u n)) Filter.atTop (𝓝 (f c))) :
    ¬ ContinuousAt f c := by
  intro hcont
  rcases h with ⟨u, hu, hnot⟩
  have hseq :=
    ((proposition_3_2_2 S f c).2.2).1 hcont
  exact hnot (hseq u hu)

/-- Explicit values of even powers of `-1` in `ℝ`. -/
lemma neg_one_pow_even_real (m : ℕ) :
    (-1 : ℝ) ^ (2 * m) = 1 := by
  have hsq : (-1 : ℝ) ^ 2 = (1 : ℝ) := by norm_num
  simp [pow_mul, hsq]

/-- Explicit values of odd powers of `-1` in `ℝ`. -/
lemma neg_one_pow_odd_real (m : ℕ) :
    (-1 : ℝ) ^ (2 * m + 1) = -1 := by
  have h_even := neg_one_pow_even_real m
  simp [pow_succ, h_even]

/-- Example 3.2.10. The function `f : ℝ → ℝ` given by
`f x = -1` for `x < 0` and `f x = 1` for `x ≥ 0` has a jump discontinuity at
`0`. The left-limit along `x_n = -1 / n` is `-1`, the right-limit along
`x_n = 1 / n` is `1`, and along the alternating sequence
`x_n = (-1)^n / n` the values oscillate and diverge. -/
noncomputable def jumpDiscontinuity (x : ℝ) : ℝ :=
  if x < 0 then -1 else 1

lemma jumpDiscontinuity_of_neg {x : ℝ} (hx : x < 0) :
    jumpDiscontinuity x = -1 := by
  unfold jumpDiscontinuity
  simp [hx]

lemma jumpDiscontinuity_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    jumpDiscontinuity x = 1 := by
  unfold jumpDiscontinuity
  have hx' : ¬ x < 0 := not_lt_of_ge hx
  simp [hx']

lemma jumpDiscontinuity_left_sequence :
    Tendsto (fun n : ℕ => jumpDiscontinuity (-((n.succ : ℝ)⁻¹)))
      atTop (𝓝 (-1 : ℝ)) := by
  classical
  have hconst :
      (fun n : ℕ => jumpDiscontinuity (-((n.succ : ℝ)⁻¹))) =
        fun _ : ℕ => (-1 : ℝ) := by
    funext n
    have hxpos :
        0 < (n.succ : ℝ)⁻¹ :=
      inv_pos.2 (by exact_mod_cast Nat.succ_pos n)
    have hxneg :
        -((n.succ : ℝ)⁻¹) < 0 := by
      simpa using mul_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hxpos
    exact jumpDiscontinuity_of_neg hxneg
  have hlimit :
      Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1 : ℝ)) :=
    tendsto_const_nhds
  exact hconst ▸ hlimit

lemma jumpDiscontinuity_right_sequence :
    Tendsto (fun n : ℕ => jumpDiscontinuity ((n.succ : ℝ)⁻¹))
      atTop (𝓝 (1 : ℝ)) := by
  classical
  have hconst :
      (fun n : ℕ => jumpDiscontinuity ((n.succ : ℝ)⁻¹)) =
        fun _ : ℕ => (1 : ℝ) := by
    funext n
    have hxpos :
        0 < (n.succ : ℝ)⁻¹ :=
      inv_pos.2 (by exact_mod_cast Nat.succ_pos n)
    exact jumpDiscontinuity_of_nonneg hxpos.le
  have hlimit :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  exact hconst ▸ hlimit

lemma jumpDiscontinuity_alternating_sequence_diverges :
    ¬ ∃ l : ℝ,
      Tendsto (fun n : ℕ =>
        jumpDiscontinuity (((-1 : ℝ) ^ n) / (n.succ : ℝ))) atTop (𝓝 l) := by
  classical
  intro h
  rcases h with ⟨l, hlim⟩
  have h_even_index :
      Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro N
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N, ?_⟩
    intro n hn
    have hle : n ≤ 2 * n := by
      convert (Nat.le_add_right n n) using 1
      simp [two_mul]
    exact le_trans hn hle
  have h_odd_index :
      Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro N
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N, ?_⟩
    intro n hn
    have hle : n ≤ 2 * n := by
      convert (Nat.le_add_right n n) using 1
      simp [two_mul]
    have hsucc : 2 * n ≤ 2 * n + 1 := Nat.le_succ _
    exact le_trans hn (le_trans hle hsucc)
  have h_even_values :
      ∀ n : ℕ,
        jumpDiscontinuity (((-1 : ℝ) ^ (2 * n)) / ((2 * n).succ : ℝ)) = 1 := by
    intro n
    have h_even := neg_one_pow_even_real n
    have hden_pos :
        0 < ((2 * n).succ : ℝ) := by
      exact_mod_cast Nat.succ_pos (2 * n)
    have hxpos :
        0 < ((-1 : ℝ) ^ (2 * n)) / ((2 * n).succ : ℝ) := by
      have : 0 < ((2 * n).succ : ℝ)⁻¹ := inv_pos.mpr hden_pos
      simpa [h_even, div_eq_mul_inv] using this
    exact jumpDiscontinuity_of_nonneg hxpos.le
  have h_odd_values :
      ∀ n : ℕ,
        jumpDiscontinuity (((-1 : ℝ) ^ (2 * n + 1)) /
            ((2 * n + 1).succ : ℝ)) = -1 := by
    intro n
    have h_odd := neg_one_pow_odd_real n
    have hden_pos :
        0 < ((2 * n + 1).succ : ℝ) := by
      exact_mod_cast Nat.succ_pos (2 * n + 1)
    have hxneg :
        ((-1 : ℝ) ^ (2 * n + 1)) / ((2 * n + 1).succ : ℝ) < 0 := by
      have hden_inv :
          0 < ((2 * n + 1).succ : ℝ)⁻¹ :=
        inv_pos.mpr hden_pos
      have hnum_neg :
          (-1 : ℝ) ^ (2 * n + 1) < 0 := by
        simp [h_odd]
      have hxneg' :
          ((-1 : ℝ) ^ (2 * n + 1)) * ((2 * n + 1).succ : ℝ)⁻¹ < 0 :=
        mul_neg_of_neg_of_pos hnum_neg hden_inv
      simpa [div_eq_mul_inv] using hxneg'
    exact jumpDiscontinuity_of_neg hxneg
  have h_even_const :
      (fun n : ℕ =>
          jumpDiscontinuity (((-1 : ℝ) ^ (2 * n)) / ((2 * n).succ : ℝ))) =
        fun _ : ℕ => (1 : ℝ) := by
    funext n
    exact h_even_values n
  have h_even_lim :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 l) :=
    h_even_const ▸ (hlim.comp h_even_index)
  have h_odd_const :
      (fun n : ℕ =>
          jumpDiscontinuity (((-1 : ℝ) ^ (2 * n + 1)) /
            ((2 * n + 1).succ : ℝ))) =
        fun _ : ℕ => (-1 : ℝ) := by
    funext n
    exact h_odd_values n
  have h_odd_lim :
      Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 l) :=
    h_odd_const ▸ (hlim.comp h_odd_index)
  have h1 :
      (1 : ℝ) = l :=
    tendsto_nhds_unique (f := fun _ : ℕ => (1 : ℝ))
      tendsto_const_nhds h_even_lim
  have hneg1 :
      (-1 : ℝ) = l :=
    tendsto_nhds_unique (f := fun _ : ℕ => (-1 : ℝ))
      tendsto_const_nhds h_odd_lim
  have : (1 : ℝ) = (-1 : ℝ) := h1.trans hneg1.symm
  exact (by norm_num : (1 : ℝ) ≠ -1) this

lemma example_3_2_10 : ¬ ContinuousAt jumpDiscontinuity 0 := by
  intro hcont
  have h_inv :
      Tendsto (fun n : ℕ => (n.succ : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [Nat.cast_succ, one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hneg :
      Tendsto (fun n : ℕ => -((n.succ : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa using h_inv.neg
  have hcomp :
      Tendsto (fun n : ℕ => jumpDiscontinuity (-((n.succ : ℝ)⁻¹)))
        atTop (𝓝 (jumpDiscontinuity 0)) :=
    hcont.tendsto.comp hneg
  have hvalue :
      jumpDiscontinuity 0 = (-1 : ℝ) :=
    tendsto_nhds_unique
      (f := fun n : ℕ => jumpDiscontinuity (-((n.succ : ℝ)⁻¹)))
      hcomp jumpDiscontinuity_left_sequence
  have hzero : jumpDiscontinuity 0 = (1 : ℝ) := by
    simp [jumpDiscontinuity]
  have : (1 : ℝ) = (-1 : ℝ) := hzero.symm.trans hvalue
  exact (by norm_num : (1 : ℝ) ≠ -1) this

/-- Example 3.2.11. The Dirichlet function `f : ℝ → ℝ` defined by
`f x = 1` when `x` is rational and `f x = 0` when `x` is irrational is
discontinuous at every real number. -/
noncomputable def dirichlet (x : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ q : ℚ, (q : ℝ) = x then 1 else 0

lemma dirichlet_value_rational {x : ℝ}
    (hx : ∃ q : ℚ, (q : ℝ) = x) : dirichlet x = 1 := by
  classical
  simp [dirichlet, hx]

lemma dirichlet_value_irrational {x : ℝ}
    (hx : ¬ ∃ q : ℚ, (q : ℝ) = x) : dirichlet x = 0 := by
  classical
  simp [dirichlet, hx]

lemma dirichlet_irrational_seq_at_rational {c : ℝ}
    (hc : ∃ q : ℚ, (q : ℝ) = c) :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 c) ∧ ∀ n, Irrational (u n) := by
  classical
  obtain ⟨_, _⟩ := hc
  let ε : ℕ → ℝ := fun n => (1 : ℝ) / (n.succ : ℝ)
  have ε_pos : ∀ n, 0 < ε n := fun n => by
    have : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa [ε] using one_div_pos.2 this
  have bound : ∀ n, c - ε n < c + ε n := fun n => by
    have hpos := ε_pos n
    exact (sub_lt_self c hpos).trans (lt_add_of_pos_right c hpos)
  have irr_seq :
      ∀ n, ∃ r, Irrational r ∧ c - ε n < r ∧ r < c + ε n := fun n =>
    exists_irrational_btwn (bound n)
  classical
  choose u hu using irr_seq
  have hu_dist (n : ℕ) : dist (u n) c < ε n := by
    have hleft : -(ε n) < u n - c := by
      simpa [sub_eq_add_neg] using add_lt_add_left (hu n).2.1 (-c)
    have hright : u n - c < ε n := by
      simpa [sub_eq_add_neg] using add_lt_add_left (hu n).2.2 (-c)
    simpa [dist_eq_norm, Real.norm_eq_abs] using abs_lt.2 ⟨hleft, hright⟩
  have hu_nonneg : ∀ n, 0 ≤ dist (u n) c := fun _ => dist_nonneg
  have hu_bound : ∀ n, dist (u n) c ≤ ε n := fun n => (hu_dist n).le
  have hε_lim :
      Tendsto (fun n : ℕ => ε n) atTop (𝓝 (0 : ℝ)) := by
    simpa [ε, Nat.cast_succ, add_comm, add_left_comm, add_assoc] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hdist_lim :
      Tendsto (fun n => dist (u n) c) atTop (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.squeeze tendsto_const_nhds hε_lim hu_nonneg hu_bound
  refine ⟨u, ?_, ?_⟩
  · simpa [tendsto_iff_dist_tendsto_zero] using hdist_lim
  · intro n
    exact (hu n).1

lemma dirichlet_rational_seq_at_irrational {c : ℝ}
    (hc : Irrational c) :
    ∃ v : ℕ → ℝ, Tendsto v atTop (𝓝 c) ∧ ∀ n, ∃ q : ℚ, (q : ℝ) = v n := by
  classical
  have _ : Irrational c := hc
  let ε : ℕ → ℝ := fun n => (1 : ℝ) / (n.succ : ℝ)
  have bound : ∀ n, c - ε n < c + ε n := fun n => by
    have hpos : 0 < ε n := by
      have : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      simpa [ε] using one_div_pos.2 this
    exact (sub_lt_self c hpos).trans (lt_add_of_pos_right c hpos)
  have rat_seq :
      ∀ n, ∃ q : ℚ,
        c - ε n < (q : ℝ) ∧ (q : ℝ) < c + ε n := fun n =>
    exists_rat_btwn (bound n)
  classical
  choose q hq using rat_seq
  let v : ℕ → ℝ := fun n => (q n : ℝ)
  have hv_dist (n : ℕ) : dist (v n) c < ε n := by
    have hleft : -(ε n) < v n - c := by
      simpa [v, sub_eq_add_neg] using add_lt_add_left (hq n).1 (-c)
    have hright : v n - c < ε n := by
      simpa [v, sub_eq_add_neg] using add_lt_add_left (hq n).2 (-c)
    simpa [dist_eq_norm, Real.norm_eq_abs] using abs_lt.2 ⟨hleft, hright⟩
  have hv_nonneg : ∀ n, 0 ≤ dist (v n) c := fun _ => dist_nonneg
  have hv_bound : ∀ n, dist (v n) c ≤ ε n := fun n => (hv_dist n).le
  have hε_lim :
      Tendsto (fun n : ℕ => ε n) atTop (𝓝 (0 : ℝ)) := by
    simpa [ε, Nat.cast_succ, add_comm, add_left_comm, add_assoc] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hdist_lim :
      Tendsto (fun n => dist (v n) c) atTop (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.squeeze tendsto_const_nhds hε_lim hv_nonneg hv_bound
  refine ⟨v, ?_, ?_⟩
  · simpa [tendsto_iff_dist_tendsto_zero] using hdist_lim
  · intro n
    exact ⟨q n, rfl⟩

lemma example_3_2_11 (c : ℝ) : ¬ ContinuousAt dirichlet c := by
  classical
  intro hc
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = c
  · obtain ⟨u, hu_tend, hu_irr⟩ :=
      dirichlet_irrational_seq_at_rational (c := c) hrat
    have hconst : ∀ n, dirichlet (u n) = (0 : ℝ) := by
      intro n
      have hnot : ¬ ∃ q : ℚ, (q : ℝ) = u n := by
        simpa [Irrational] using hu_irr n
      simpa using dirichlet_value_irrational (x := u n) hnot
    have hcomp := hc.tendsto.comp hu_tend
    have hlim_zero :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (dirichlet c)) := by
      convert hcomp using 1
      · funext n
        simp [Function.comp, hconst]
    have hrat_val : dirichlet c = 1 := dirichlet_value_rational hrat
    have hzero :
        (0 : ℝ) = dirichlet c :=
      tendsto_nhds_unique (f := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds hlim_zero
    have : (0 : ℝ) = (1 : ℝ) := hzero.trans hrat_val
    exact (by norm_num : (0 : ℝ) ≠ 1) this
  · have hdc : dirichlet c = 0 := dirichlet_value_irrational hrat
    have hc_irr : Irrational c := by simpa [Irrational] using hrat
    obtain ⟨v, hv_tend, hv_rat⟩ :=
      dirichlet_rational_seq_at_irrational (c := c) hc_irr
    have hconst : ∀ n, dirichlet (v n) = (1 : ℝ) := by
      intro n
      obtain ⟨q, hq⟩ := hv_rat n
      simpa [hq] using dirichlet_value_rational (x := v n) ⟨q, hq⟩
    have hcomp := hc.tendsto.comp hv_tend
    have hlim_one :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (dirichlet c)) := by
      convert hcomp using 1
      · funext n
        simp [Function.comp, hconst]
    have hone :
        (1 : ℝ) = dirichlet c :=
      tendsto_nhds_unique (f := fun _ : ℕ => (1 : ℝ)) tendsto_const_nhds hlim_one
    have : (1 : ℝ) = (0 : ℝ) := hone.trans hdc
    exact (by norm_num : (1 : ℝ) ≠ 0) this

/-- Example 3.2.12. The popcorn (Thomae) function on `(0, 1)` is defined by
`f (m / k) = 1 / k` when `m, k ∈ ℕ` are coprime and `m / k` is in lowest terms,
and `f x = 0` when `x` is irrational. It is continuous at every irrational
`c ∈ (0, 1)` and discontinuous at every rational `c ∈ (0, 1)`. -/
noncomputable def popcorn (x : ℝ) : ℝ :=
  by
    classical
    refine if hx : ∃ q : ℚ, (q : ℝ) = x then ?pos else 0
    exact ((Classical.choose hx).den : ℝ)⁻¹

lemma popcorn_value_rational (q : ℚ) :
    popcorn (q : ℝ) = (q.den : ℝ)⁻¹ := by
  classical
  have hx : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  have hchoose : Classical.choose hx = q := by
    apply Rat.cast_injective (α := ℝ)
    exact Classical.choose_spec hx
  calc
    popcorn (q : ℝ)
        = ((Classical.choose hx).den : ℝ)⁻¹ := by
          simp [popcorn]
    _ = (q.den : ℝ)⁻¹ := by
          simp

lemma popcorn_value_irrational {x : ℝ} (hx : Irrational x) :
    popcorn x = 0 := by
  classical
  have hx' : ¬ ∃ q : ℚ, (q : ℝ) = x := by
    simpa [Irrational] using hx
  simp [popcorn, hx']

lemma finite_rat_interval_small_denom (K : ℕ) :
    {q : ℚ | q ∈ Set.Icc (0 : ℚ) 1 ∧ q.den ≤ K}.Finite := by
  classical
  let S : Set ℚ :=
    {q : ℚ | q ∈ Set.Icc (0 : ℚ) 1 ∧ q.den ≤ K}
  let D := Finset.Icc 1 K
  let M := Finset.range (K + 1)
  let T :
      Finset ℚ :=
    (D.product M).image fun p : ℕ × ℕ => (p.2 : ℚ) / (p.1 : ℚ)
  have hsubset :
      S ⊆ (T : Set ℚ) := by
    intro q hq
    rcases hq with ⟨hqIcc, hden_le⟩
    have hden_pos : 1 ≤ q.den := Nat.succ_le_of_lt (Rat.den_pos q)
    have hden_mem : q.den ∈ D := Finset.mem_Icc.mpr ⟨hden_pos, hden_le⟩
    have hq0 : 0 ≤ q := hqIcc.1
    have hq1 : q ≤ 1 := hqIcc.2
    have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    set m : ℕ := q.num.toNat
    have hm_int : (m : ℤ) = q.num :=
      Int.toNat_of_nonneg hnum_nonneg
    have hx_divInt := q.num_divInt_den
    have hx_mInt : ((m : ℤ) /. q.den) = q := by
      convert hx_divInt using 1
      · simp [hm_int]
    have hx_cast :
        ((m : ℚ) / q.den) = ((m : ℤ) /. q.den) := by
      simpa using (Rat.natCast_div_eq_divInt m q.den)
    have hq_eq' :
        ((m : ℚ) / q.den) = q := by
      simpa [hx_cast] using hx_mInt
    have hq_eq : q = (m : ℚ) / q.den := hq_eq'.symm
    have hm_le_den : m ≤ q.den := by
      have hfrac_le : (m : ℚ) / q.den ≤ (1 : ℚ) := by
        have := hq_eq ▸ hq1
        simpa using this
      have hden_pos' :
          (0 : ℚ) < q.den := by
        exact_mod_cast (Rat.den_pos q)
      have hm_le_rat :
          (m : ℚ) ≤ q.den := by
        have := (div_le_iff₀ hden_pos').mp hfrac_le
        simpa using this
      have hm_le_int :
          (m : ℤ) ≤ (q.den : ℤ) := by
        exact_mod_cast hm_le_rat
      exact_mod_cast hm_le_int
    have hm_le_K : m ≤ K := hm_le_den.trans hden_le
    have hm_mem : m ∈ M := by
      have : m < K + 1 := Nat.lt_succ_of_le hm_le_K
      simpa [M, Finset.mem_range] using this
    have : q ∈ T := by
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨q.den, m⟩, ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨hden_mem, hm_mem⟩
      · simpa using hq_eq'
    exact this
  have hSfinite : S.Finite :=
    (T.finite_toSet.subset hsubset)
  simpa [S] using hSfinite

lemma finite_small_denom_rationals (K : ℕ) :
    {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K}.Finite := by
  classical
  let S : Set ℚ :=
    {q : ℚ | q ∈ Set.Icc (0 : ℚ) 1 ∧ q.den ≤ K}
  have hSfinite : S.Finite := by
    simpa [S] using finite_rat_interval_small_denom K
  have hset :
      {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K} =
        (fun q : ℚ => (q : ℝ)) '' S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxIcc, q, hqx, hden⟩
      have hx0' : ((0 : ℚ) : ℝ) ≤ (q : ℝ) := by
        simpa [hqx.symm] using hxIcc.1
      have hx1' : (q : ℝ) ≤ ((1 : ℚ) : ℝ) := by
        simpa [hqx.symm] using hxIcc.2
      have hq_nonneg : 0 ≤ q := by
        simpa using (Rat.cast_le (K := ℝ)).1 hx0'
      have hq_le_one : q ≤ 1 := by
        simpa using (Rat.cast_le (K := ℝ)).1 hx1'
      have hqIcc : q ∈ Set.Icc (0 : ℚ) 1 := ⟨hq_nonneg, hq_le_one⟩
      refine ⟨q, ⟨hqIcc, hden⟩, ?_⟩
      exact hqx
    · intro hx
      rcases hx with ⟨q, hqS, hx⟩
      rcases hqS with ⟨hqIcc, hden⟩
      have hxIcc :
          (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        have hx0 : 0 ≤ (q : ℝ) := by
          exact_mod_cast hqIcc.1
        have hx1 : (q : ℝ) ≤ 1 := by
          exact_mod_cast hqIcc.2
        exact ⟨hx0, hx1⟩
      have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := by
        convert hxIcc using 1
        simp [hx]
      refine ⟨hx_mem, ⟨q, hx, hden⟩⟩
  have himage :
      ((fun q : ℚ => (q : ℝ)) '' S).Finite :=
    hSfinite.image _
  exact hset ▸ himage

lemma popcorn_discontinuous_at_rational {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hc : ∃ q : ℚ, (q : ℝ) = c) : ¬ ContinuousAt popcorn c := by
  classical
  intro hcont
  have hc_between : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc0, hc1⟩
  obtain ⟨q, hq⟩ := hc
  obtain ⟨u, hu_tend, hu_irr⟩ :=
    dirichlet_irrational_seq_at_rational (c := c) ⟨q, hq⟩
  have hconst : ∀ n, popcorn (u n) = 0 := by
    intro n
    have hirr : Irrational (u n) := hu_irr n
    simpa using popcorn_value_irrational hirr
  have hcomp := hcont.tendsto.comp hu_tend
  have hlim_zero :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (popcorn c)) := by
    convert hcomp using 1
    · funext n
      simp [Function.comp, hconst]
  have hval : popcorn c = (q.den : ℝ)⁻¹ := by
    have h := popcorn_value_rational q
    simp [hq] at h
    exact h
  have hpos : 0 < popcorn c := by
    have hden_pos : 0 < (q.den : ℝ) := by
      exact_mod_cast (Rat.den_pos q)
    simpa [hval] using inv_pos.mpr hden_pos
  have hzero :
      (0 : ℝ) = popcorn c :=
    tendsto_nhds_unique (f := fun _ : ℕ => (0 : ℝ))
      tendsto_const_nhds hlim_zero
  have : popcorn c = 0 := hzero.symm
  exact hpos.ne' this

lemma popcorn_continuous_at_irrational {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hc : Irrational c) : ContinuousAt popcorn c := by
  classical
  have hpc : popcorn c = 0 := popcorn_value_irrational hc
  refine Metric.continuousAt_iff.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let K := N + 1
  have hKpos_nat : 0 < K := Nat.succ_pos _
  have hK_inv_lt : (1 / (K : ℝ)) < ε := by
    simpa [K] using hN
  have hF_fin :
      {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K}.Finite :=
    finite_small_denom_rationals K
  have hc_not_mem : c ∉ {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K} := by
    intro hmem
    rcases hmem with ⟨-, ⟨q, hq, -⟩⟩
    have : ¬ ∃ q : ℚ, (q : ℝ) = c := by
      simpa [Irrational] using hc
    exact this ⟨q, by simpa using hq⟩
  have hFclosed :
      IsClosed {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K} :=
    hF_fin.isClosed
  have hcompl_open :
      IsOpen ({x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K}ᶜ) :=
    hFclosed.isOpen_compl
  have hc_mem :
      c ∈ ({x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K}ᶜ) := by
    simpa using hc_not_mem
  obtain ⟨δ1, hδ1_pos, hδ1_subset⟩ :=
    Metric.mem_nhds_iff.1 (hcompl_open.mem_nhds hc_mem)
  let δ0 := min c (1 - c)
  have hδ0_pos :
      0 < δ0 :=
    (lt_min_iff).2 ⟨hc0, sub_pos.2 hc1⟩
  let δ := min δ0 δ1
  have hδ_pos :
      0 < δ :=
    (lt_min_iff).2 ⟨hδ0_pos, hδ1_pos⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx
  have hxabs : |x - c| < δ := by
    simpa [Real.dist_eq, abs_sub_comm] using hx
  have hxδ0 :
      |x - c| < δ0 :=
    lt_of_lt_of_le hxabs (min_le_left _ _)
  have hxδ1 :
      |x - c| < δ1 :=
    lt_of_lt_of_le hxabs (min_le_right _ _)
  have hx_bounds := abs_lt.1 hxδ0
  have hx_lower :
      c - δ0 < x := by
    have h := hx_bounds.1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using add_lt_add_right h c
  have hx_upper :
      x < c + δ0 := by
    have h := hx_bounds.2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using add_lt_add_right h c
  have hδ0_le_c : δ0 ≤ c := min_le_left _ _
  have hδ0_le_one : δ0 ≤ 1 - c := min_le_right _ _
  have hx_pos : 0 < x := by
    have hnonneg : 0 ≤ c - δ0 := sub_nonneg.mpr hδ0_le_c
    exact lt_of_le_of_lt hnonneg hx_lower
  have hx_lt_one : x < 1 := by
    have hsum_le :
        c + δ0 ≤ 1 := by
      have := add_le_add_left hδ0_le_one c
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hx_upper hsum_le
  have hxIcc :
      x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_pos.le, hx_lt_one.le⟩
  have hx_not_mem :
      x ∉ {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K} := by
    have hx_ball :
        x ∈ Metric.ball c δ1 := by
      simpa [Real.dist_eq, abs_sub_comm] using hxδ1
    have : x ∈
        ({x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
            ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ K}ᶜ) :=
      hδ1_subset hx_ball
    exact this
  by_cases hx_rat : ∃ q : ℚ, (q : ℝ) = x
  · rcases hx_rat with ⟨q, hqx⟩
    have hden_gt : K < q.den := by
      have hden_not_le :
          ¬ q.den ≤ K := by
        intro hle
        have : x ∈
            {x : ℝ |
              x ∈ Set.Icc (0 : ℝ) 1 ∧
                ∃ q' : ℚ, (q' : ℝ) = x ∧ q'.den ≤ K} := by
          refine ⟨hxIcc, ?_⟩
          exact ⟨q, hqx, hle⟩
        exact hx_not_mem this
      exact Nat.lt_of_not_ge hden_not_le
    have hpop_val :
        popcorn x = (q.den : ℝ)⁻¹ := by
      have h := popcorn_value_rational q
      simp [hqx] at h
      exact h
    have hden_pos : 0 < (q.den : ℝ) := by
      exact_mod_cast (Rat.den_pos q)
    have hKpos : 0 < (K : ℝ) :=
      by exact_mod_cast hKpos_nat
    have hden_gt' : (K : ℝ) < (q.den : ℝ) := by
      exact_mod_cast hden_gt
    have hrecip_lt :
        (q.den : ℝ)⁻¹ < (K : ℝ)⁻¹ := by
      have := (one_div_lt_one_div_of_lt hKpos) hden_gt'
      simpa [one_div] using this
    have hpop_lt :
        popcorn x < (1 / (K : ℝ)) := by
      simpa [hpop_val] using hrecip_lt
    have hnonneg :
        0 ≤ popcorn x := by
      have hpos :
          0 < popcorn x := by
        simpa [hpop_val] using inv_pos.mpr hden_pos
      exact hpos.le
    have hpop_abs :
        |popcorn x| = popcorn x := by
      simp [abs_of_nonneg hnonneg]
    have hx_bound :
        |popcorn x| < ε := by
      simpa [hpop_abs] using lt_trans hpop_lt hK_inv_lt
    simpa [Real.dist_eq, hpc] using hx_bound
  · have hx_irr : Irrational x := by
      simpa [Irrational] using hx_rat
    have hzero :
        popcorn x = 0 :=
      popcorn_value_irrational hx_irr
    have hx_bound :
        |popcorn x| < ε := by
      simpa [hzero] using hε
    simpa [Real.dist_eq, hpc, hzero] using hx_bound

/-- Example 3.2.13. Define `g : ℝ → ℝ` by `g x = 0` for `x ≠ 0` and `g 0 = 1`.
Then `g` is not continuous at `0` but it is continuous at every other point.
The point `0` is a removable discontinuity since redefining `g 0 = 0` would
make the function continuous. Let `A = {0}` and `B = ℝ \ {0}`; the restriction
`g |_ A` is continuous even though `g` fails to be continuous at `0`, while
`g |_ B` (and `g` on `B`) is continuous. -/
noncomputable def removableDiscontinuityExample (x : ℝ) : ℝ :=
  if x = 0 then 1 else 0

lemma removableDiscontinuityExample_not_continuous_at_zero :
    ¬ ContinuousAt removableDiscontinuityExample 0 := by
  classical
  intro hcont
  -- take a sequence of nonzero points converging to `0`
  let u : ℕ → ℝ := fun n => (Nat.succ n : ℝ)⁻¹
  have hu_tend :
      Tendsto u atTop (𝓝 (0 : ℝ)) := by
    simpa [u, Nat.cast_succ, one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hcomp := hcont.tendsto.comp hu_tend
  have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
    intro n
    have : (0 : ℝ) < (Nat.succ n : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact inv_ne_zero (ne_of_gt this)
  have hconst : ∀ n, removableDiscontinuityExample (u n) = 0 := by
    intro n
    have : u n ≠ 0 := hu_ne n
    simp [removableDiscontinuityExample, this]
  have hconst_eventually :
      removableDiscontinuityExample ∘ u =ᶠ[atTop] fun _ : ℕ => (0 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp [Function.comp, hconst n]
  have hlim :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (removableDiscontinuityExample 0)) := by
    exact (Tendsto.congr' hconst_eventually) hcomp
  have hzero :
      (0 : ℝ) = removableDiscontinuityExample 0 :=
    tendsto_nhds_unique (f := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds hlim
  have hzero' : (0 : ℝ) = 1 := by
    convert hzero using 1
    simp [removableDiscontinuityExample]
  have hcontr : (0 : ℝ) = 1 := hzero'
  exact (by norm_num : (0 : ℝ) ≠ 1) hcontr

lemma removableDiscontinuityExample_continuous_away_zero {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt removableDiscontinuityExample x := by
  classical
  have hxevent :
      ∀ᶠ y in 𝓝 x, y ∈ ({0}ᶜ : Set ℝ) := by
    have hopen : IsOpen ({0}ᶜ : Set ℝ) :=
      isClosed_singleton.isOpen_compl
    have hxmem : x ∈ ({0}ᶜ : Set ℝ) := by
      simpa [Set.mem_compl, Set.mem_singleton_iff] using hx
    exact hopen.mem_nhds hxmem
  have hconst :
      removableDiscontinuityExample =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    refine hxevent.mono ?_
    intro y hy
    have hyne : y ≠ 0 := by
      simpa [Set.mem_compl, Set.mem_singleton_iff] using hy
    simp [removableDiscontinuityExample, hyne]
  have hx_val : removableDiscontinuityExample x = 0 := by
    simp [removableDiscontinuityExample, hx]
  have hlim :
      Tendsto removableDiscontinuityExample (𝓝 x) (𝓝 (0 : ℝ)) :=
    (Tendsto.congr' hconst.symm) tendsto_const_nhds
  simpa [ContinuousAt, hx_val] using hlim

lemma removableDiscontinuityExample_limit :
    Tendsto removableDiscontinuityExample (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  classical
  refine tendsto_def.mpr ?_
  intro s hs
  have h0 : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  have haux :
      {x : ℝ | x ≠ 0 → removableDiscontinuityExample x ∈ s} ∈ 𝓝 (0 : ℝ) := by
    have : {x : ℝ | x ≠ 0 → removableDiscontinuityExample x ∈ s} = Set.univ := by
      ext x
      by_cases hx : x = 0
      · simp [hx]
      · have hxne : x ≠ 0 := hx
        simp [removableDiscontinuityExample, hxne, h0]
    simp [this]
  have hpre :
      removableDiscontinuityExample ⁻¹' s ∈ 𝓝[≠] (0 : ℝ) := by
    have :
        {x : ℝ |
            x ∈ ({0}ᶜ : Set ℝ) → x ∈ removableDiscontinuityExample ⁻¹' s} ∈
          𝓝 (0 : ℝ) := by
      simpa [Set.preimage, Set.mem_setOf_eq, Set.mem_compl, Set.mem_singleton_iff] using haux
    have :=
      (mem_inf_principal :
          removableDiscontinuityExample ⁻¹' s ∈
              𝓝 (0 : ℝ) ⊓ 𝓟 (({0}ᶜ : Set ℝ)) ↔
                {x : ℝ |
                    x ∈ ({0}ᶜ : Set ℝ) →
                      x ∈ removableDiscontinuityExample ⁻¹' s} ∈ 𝓝 (0 : ℝ)).2 this
    simpa [nhdsWithin] using this
  exact hpre

lemma removableDiscontinuityExample_restrict_singleton :
    Continuous fun x : {x : ℝ // x = 0} => removableDiscontinuityExample x := by
  classical
  have hconst :
      (fun x : {x : ℝ // x = 0} => removableDiscontinuityExample x) =
        fun _ : {x : ℝ // x = 0} => (1 : ℝ) := by
    funext x
    simp [removableDiscontinuityExample, x.property]
  simpa [hconst] using
    (continuous_const : Continuous fun _ : {x : ℝ // x = 0} => (1 : ℝ))

lemma removableDiscontinuityExample_continuous_on_complement :
    ContinuousOn removableDiscontinuityExample ({0}ᶜ : Set ℝ) := by
  intro x hx
  have hx_ne : x ≠ 0 := by
    simpa [Set.mem_compl, Set.mem_singleton_iff] using hx
  exact (removableDiscontinuityExample_continuous_away_zero hx_ne).continuousWithinAt

end Section02
end Chap03
