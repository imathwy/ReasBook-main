/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part5

noncomputable section

section Chap02
section Section10

open scoped BigOperators Pointwise

/-- A Lipschitz function on `univ` has at most linear growth along rays, hence
`liminf_{t → ∞} g (t • y) / t < ⊤`. -/
lemma Section10.liminf_div_lt_top_of_lipschitzRelativeTo_univ {n : ℕ}
    {g : EuclideanSpace Real (Fin n) → Real}
    (hg : Function.LipschitzRelativeTo g (Set.univ : Set (EuclideanSpace Real (Fin n)))) :
    ∀ y : EuclideanSpace Real (Fin n),
      Filter.liminf (fun t : ℝ => ((g (t • y) / t : Real) : EReal)) Filter.atTop < (⊤ : EReal) := by
  intro y
  rcases hg with ⟨K, hK⟩
  classical
  let C : Real := |g 0| + (K : Real) * ‖y‖
  have h_event :
      ∀ᶠ t : ℝ in Filter.atTop, ((g (t • y) / t : Real) : EReal) ≤ (C : EReal) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have htne : t ≠ 0 := ne_of_gt htpos
    have hnorm :
        ‖g (t • y) - g 0‖ ≤ (K : Real) * ‖t • y‖ := by
      simpa [sub_zero] using
        (LipschitzOnWith.norm_sub_le (s := (Set.univ : Set (EuclideanSpace Real (Fin n))))
          (f := g) (C := K) hK (x := t • y) (by simp) (y := 0) (by simp))
    have habs :
        |g (t • y) - g 0| ≤ (K : Real) * ‖t • y‖ := by
      simpa [Real.norm_eq_abs] using hnorm
    have hupper :
        g (t • y) ≤ g 0 + (K : Real) * ‖t • y‖ := by
      have hsub : g (t • y) - g 0 ≤ (K : Real) * ‖t • y‖ := (abs_le.mp habs).2
      linarith
    have hdiv :
        g (t • y) / t ≤ (g 0 + (K : Real) * ‖t • y‖) / t :=
      div_le_div_of_nonneg_right hupper ht0
    have hnorm_smul : ‖t • y‖ = t * ‖y‖ := by
      simpa [Real.norm_of_nonneg ht0, mul_assoc] using (norm_smul t y)
    have hterm : ((K : Real) * ‖t • y‖) / t = (K : Real) * ‖y‖ := by
      calc
        ((K : Real) * ‖t • y‖) / t = ((K : Real) * (t * ‖y‖)) / t := by simp [hnorm_smul]
        _ = (K : Real) * ((t * ‖y‖) / t) := by
          simpa [mul_assoc] using (mul_div_assoc (K : Real) (t * ‖y‖) t)
        _ = (K : Real) * ‖y‖ := by
          have : t * ‖y‖ / t = ‖y‖ := by
            simpa using (mul_div_cancel_left₀ ‖y‖ htne)
          simp [this]
    have hdiv0 : g 0 / t ≤ |g 0| := by
      have h1 : g 0 / t ≤ |g 0| / t :=
        div_le_div_of_nonneg_right (le_abs_self (g 0)) (le_of_lt htpos)
      have h2 : |g 0| / t ≤ |g 0| := by
        exact div_le_self (abs_nonneg (g 0)) ht
      exact le_trans h1 h2
    have hbound_real : g (t • y) / t ≤ C := by
      have :
          g (t • y) / t ≤ g 0 / t + ((K : Real) * ‖t • y‖) / t := by
        simpa [add_div] using hdiv
      calc
        g (t • y) / t ≤ g 0 / t + ((K : Real) * ‖t • y‖) / t := this
        _ = g 0 / t + (K : Real) * ‖y‖ := by simp [hterm]
        _ ≤ |g 0| + (K : Real) * ‖y‖ := by
          simpa [C] using (add_le_add_right hdiv0 ((K : Real) * ‖y‖))
    exact EReal.coe_le_coe hbound_real
  have hle :
      Filter.liminf (fun t : ℝ => ((g (t • y) / t : Real) : EReal)) Filter.atTop ≤ (C : EReal) := by
    have :=
      Section10.liminf_le_liminf_of_eventually_le (l := Filter.atTop)
        (u := fun t : ℝ => ((g (t • y) / t : Real) : EReal)) (v := fun _ : ℝ => (C : EReal))
        h_event
    simpa [Filter.liminf_const] using this
  exact lt_of_le_of_lt hle (EReal.coe_lt_top C)

/-- If `f ≤ g` and `g` is Lipschitz on `univ`, then the growth condition
`liminf_{t → ∞} f (t • y) / t < ⊤` also holds for `f`. -/
lemma Section10.liminf_div_lt_top_of_le_and_lipschitzRelativeTo_univ {n : ℕ}
    {f g : EuclideanSpace Real (Fin n) → Real}
    (hglip : Function.LipschitzRelativeTo g (Set.univ : Set (EuclideanSpace Real (Fin n))))
    (hfg : ∀ x, f x ≤ g x) :
    ∀ y : EuclideanSpace Real (Fin n),
      Filter.liminf (fun t : ℝ => ((f (t • y) / t : Real) : EReal)) Filter.atTop < (⊤ : EReal) := by
  intro y
  have hlim_g :=
    Section10.liminf_div_lt_top_of_lipschitzRelativeTo_univ (n := n) (g := g) hglip y
  have h_event :
      ∀ᶠ t : ℝ in Filter.atTop,
        ((f (t • y) / t : Real) : EReal) ≤ ((g (t • y) / t : Real) : EReal) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    exact EReal.coe_le_coe (div_le_div_of_nonneg_right (hfg (t • y)) ht0)
  have hle :
      Filter.liminf (fun t : ℝ => ((f (t • y) / t : Real) : EReal)) Filter.atTop ≤
        Filter.liminf (fun t : ℝ => ((g (t • y) / t : Real) : EReal)) Filter.atTop :=
    Section10.liminf_le_liminf_of_eventually_le (l := Filter.atTop) h_event
  exact lt_of_le_of_lt hle hlim_g

/-- Corollary 10.5.2. Let `g` be any finite convex function Lipschitzian relative to `ℝ^n`
(for instance, `g(x) = α ‖x‖ + β` with `α > 0`). Then every finite convex function `f` such that
`f ≤ g` is likewise Lipschitzian relative to `ℝ^n`. -/
theorem convexOn_lipschitzRelativeTo_univ_of_le_of_lipschitzRelativeTo {n : ℕ}
    {f g : EuclideanSpace Real (Fin n) → Real}
    (hgconv : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) g)
    (hglip : Function.LipschitzRelativeTo g (Set.univ : Set (EuclideanSpace Real (Fin n))))
    (hfconv : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f)
    (hfg : ∀ x, f x ≤ g x) :
    Function.LipschitzRelativeTo f (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
  -- Use convexity of `g` only to match the textbook assumptions (the proof needs `g` Lipschitz).
  have hglip' :
      Function.LipschitzRelativeTo g (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
    refine convexOn_lipschitzRelativeTo_univ_of_liminf_div_lt_top (n := n) (f := g) hgconv ?_
    intro y
    exact Section10.liminf_div_lt_top_of_lipschitzRelativeTo_univ (n := n) (g := g) hglip y
  refine convexOn_lipschitzRelativeTo_univ_of_liminf_div_lt_top (n := n) (f := f) hfconv ?_
  intro y
  simpa using
    Section10.liminf_div_lt_top_of_le_and_lipschitzRelativeTo_univ (n := n) (f := f) (g := g)
      hglip' hfg y

/-- Definition 10.5.3. Let `S ⊆ ℝ^n` and let `{f i | i ∈ I}` be a family of real-valued functions
defined on `S`. The family is *equi-Lipschitzian relative to `S`* if there exists a constant
`α ≥ 0` such that
`|f i y - f i x| ≤ α * ‖y - x‖` for all `x ∈ S`, `y ∈ S`, and all indices `i`. -/
def Function.EquiLipschitzRelativeTo {n : ℕ} {I : Type*}
    (f : I → EuclideanSpace Real (Fin n) → Real) (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ∃ K : NNReal, ∀ i : I, LipschitzOnWith K (f i) S

end Section10
end Chap02
