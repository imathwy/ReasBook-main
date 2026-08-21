/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part1

noncomputable section

section Chap02
section Section10

open scoped BigOperators

/-- Theorem 10.1.4 (lower semicontinuity at `(0,0)`). -/
theorem lowerSemicontinuousAt_quadraticOverLinearEReal_zero :
    LowerSemicontinuousAt quadraticOverLinearEReal (0 : Fin 2 → Real) := by
  intro y hy
  have hy0 : y < (0 : EReal) := by
    simpa [quadraticOverLinearEReal] using hy
  refine Filter.Eventually.of_forall ?_
  intro ξ
  exact lt_of_lt_of_le hy0 (zero_le_quadraticOverLinearEReal ξ)

/-- Theorem 10.1.4 (path limit, auxiliary): for `α > 0`, along the parabola and excluding `t = 0`,
the values tend to `α`. -/
lemma tendsto_quadraticOverLinearEReal_along_parabola_aux {α : Real} (hα : 0 < α) :
    Filter.Tendsto
      (fun t : Real =>
        quadraticOverLinearEReal
          (![t ^ 2 / (2 * α), t] : Fin 2 → Real))
      (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds (α : EReal)) := by
  have hne : ∀ᶠ t : Real in nhdsWithin (0 : Real) ({0}ᶜ), t ≠ 0 := by
    simpa using (self_mem_nhdsWithin : ({0}ᶜ : Set Real) ∈ nhdsWithin (0 : Real) ({0}ᶜ))
  have hEq :
      (fun t : Real =>
          quadraticOverLinearEReal (![t ^ 2 / (2 * α), t] : Fin 2 → Real)) =ᶠ[
        nhdsWithin (0 : Real) ({0}ᶜ)] fun _ => (α : EReal) := by
    filter_upwards [hne] with t ht
    have ht2 : 0 < t ^ 2 := by
      simpa [pow_two] using sq_pos_of_ne_zero ht
    have hξpos : (t ^ 2 / (2 * α)) > 0 := by
      exact div_pos ht2 (by nlinarith)
    have hreal : t ^ 2 / (2 * (t ^ 2 / (2 * α))) = α := by
      have ht2ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp [ht2ne, hαne]
    simp [quadraticOverLinearEReal, hξpos, hreal]
  have htend :
      Filter.Tendsto (fun _ : Real => (α : EReal))
        (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds (α : EReal)) :=
    tendsto_const_nhds
  exact htend.congr' hEq.symm

/-- Theorem 10.1.4 (failure of continuity at `(0,0)`). -/
theorem not_continuousAt_quadraticOverLinearEReal_zero :
    ¬ ContinuousAt quadraticOverLinearEReal (0 : Fin 2 → Real) := by
  intro hcont
  -- Use the parabola approach with `α = 1` to get a limit different from `f 0 = 0`.
  have hpar :
      Filter.Tendsto
        (fun t : Real =>
          quadraticOverLinearEReal (![t ^ 2 / (2 * (1 : Real)), t] : Fin 2 → Real))
        (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds ((1 : Real) : EReal)) :=
    (tendsto_quadraticOverLinearEReal_along_parabola_aux (α := (1 : Real)) (by norm_num))
  -- Continuity at `0` would force the same path to tend to `f 0 = 0`.
  let g : Real → Fin 2 → Real := fun t => (![t ^ 2 / (2 * (1 : Real)), t] : Fin 2 → Real)
  have hg : Filter.Tendsto g (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds (0 : Fin 2 → Real)) := by
    have hg' : ContinuousAt g (0 : Real) := by
      -- Prove continuity componentwise.
      refine (continuousAt_pi.2 ?_)
      intro i
      fin_cases i
      · -- First coordinate: `t ↦ t^2 / 2`.
        have hpow : ContinuousAt (fun t : Real => t ^ 2) (0 : Real) :=
          (continuousAt_id.pow 2)
        have hmul :
            ContinuousAt (fun t : Real => t ^ 2 * (2 * (1 : Real))⁻¹) (0 : Real) :=
          hpow.mul continuousAt_const
        simpa [g, div_eq_mul_inv, mul_assoc] using hmul
      · -- Second coordinate: `t ↦ t`.
        simpa [g] using (continuousAt_id : ContinuousAt (fun t : Real => t) (0 : Real))
    have : Filter.Tendsto g (nhds (0 : Real)) (nhds (g 0)) := hg'.tendsto
    have hg0 : g 0 = (0 : Fin 2 → Real) := by
      ext i
      fin_cases i <;> simp [g]
    have := this.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set Real)))
    simpa [hg0] using this
  have hcomp :
      Filter.Tendsto (fun t => quadraticOverLinearEReal (g t))
        (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds (quadraticOverLinearEReal (0 : Fin 2 → Real))) :=
    (hcont.tendsto.comp hg)
  have huniq := tendsto_nhds_unique hpar (by simpa [g] using hcomp)
  have hf0 : quadraticOverLinearEReal (0 : Fin 2 → Real) = (0 : EReal) := by
    simp [quadraticOverLinearEReal]
  have huniq' : ((1 : Real) : EReal) = (0 : EReal) := by
    have huniq' := huniq
    simp [hf0] at huniq'
  have : (1 : Real) = 0 := EReal.coe_injective huniq'
  exact one_ne_zero this

/-- Theorem 10.1.4 (path limit): for any `α > 0`, `lim_{t → 0} f(t^2/(2α), t) = α`. -/
theorem tendsto_quadraticOverLinearEReal_along_parabola {α : Real} (hα : 0 < α) :
    Filter.Tendsto
      (fun t : Real =>
        quadraticOverLinearEReal
          (![t ^ 2 / (2 * α), t] : Fin 2 → Real))
      (nhdsWithin (0 : Real) ({0}ᶜ)) (nhds (α : EReal)) := by
  exact tendsto_quadraticOverLinearEReal_along_parabola_aux (α := α) hα

/-- Theorem 10.1.4 (path limit): for `x₁ > 0`, `lim_{t ↓ 0} f(t • x) = 0`. -/
theorem tendsto_quadraticOverLinearEReal_smul_of_pos {x : Fin 2 → Real} (hx : x 0 > 0) :
    Filter.Tendsto (fun t : Real => quadraticOverLinearEReal (t • x))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (0 : EReal)) := by
  have htpos : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Set.Ioi 0), 0 < t := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : Real) ∈ nhdsWithin (0 : Real) (Set.Ioi 0))
  have hEq :
      (fun t : Real => quadraticOverLinearEReal (t • x)) =ᶠ[
        nhdsWithin (0 : Real) (Set.Ioi 0)]
        fun t => ((t * ((x 1) ^ 2 / (2 * x 0)) : Real) : EReal) := by
    filter_upwards [htpos] with t ht
    have hξpos : t * x 0 > 0 := mul_pos ht hx
    have htne : t ≠ 0 := ne_of_gt ht
    have hx0ne : x 0 ≠ 0 := ne_of_gt hx
    have hreal :
        ((t * x 1) ^ 2) / (2 * (t * x 0)) = t * ((x 1) ^ 2 / (2 * x 0)) := by
      field_simp [htne, hx0ne]
    have hval :
        quadraticOverLinearEReal (t • x) =
          (((t * x 1) ^ 2 / (2 * (t * x 0)) : Real) : EReal) := by
      simp [quadraticOverLinearEReal, Pi.smul_apply, smul_eq_mul, hξpos]
    -- Rewrite the real expression to get the claimed form.
    simp [hval, hreal]
  have ht0 :
      Filter.Tendsto (fun t : Real => t * ((x 1) ^ 2 / (2 * x 0)))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (0 : Real)) := by
    have ht' :
        Filter.Tendsto (fun t : Real => t) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (0 : Real)) :=
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds)
    simpa [mul_assoc] using ht'.mul_const ((x 1) ^ 2 / (2 * x 0))
  have hcoe :
      Filter.Tendsto (fun r : Real => (r : EReal)) (nhds (0 : Real)) (nhds (0 : EReal)) :=
    (continuous_coe_real_ereal.tendsto 0)
  have hlim :
      Filter.Tendsto (fun t : Real => ((t * ((x 1) ^ 2 / (2 * x 0)) : Real) : EReal))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (0 : EReal)) :=
    hcoe.comp ht0
  exact hlim.congr' hEq.symm

/-- Definition 10.1.5. A subset `S ⊆ ℝ^n` is locally simplicial if for each `x ∈ S` there exist
finitely many simplices `S₁, …, Sₘ ⊆ S` and a neighborhood `U` of `x` such that
`U ∩ (S₁ ∪ ⋯ ∪ Sₘ) = U ∩ S`. -/
def Set.LocallySimplicial (n : ℕ) (S : Set (Fin n → Real)) : Prop :=
  ∀ x ∈ S,
    ∃ (𝒮 : Set (Set (Fin n → Real))) (U : Set (Fin n → Real)),
      𝒮.Finite ∧
        U ∈ nhds x ∧
          (∀ P ∈ 𝒮, ∃ m : ℕ, IsSimplex n m P ∧ P ⊆ S) ∧
            U ∩ (⋃₀ 𝒮) = U ∩ S

/-- Replacing `b j` by `x` produces exactly the vertex set `{x} ∪ {b (succAbove j i) | i : Fin m}`. -/
lemma range_update_eq_insert_range_succAbove {n m : ℕ} (b : Fin (m + 1) → Fin n → Real)
    (j : Fin (m + 1)) (x : Fin n → Real) :
    Set.range (Function.update b j x) =
      Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)) := by
  classical
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    by_cases hk : k = j
    · -- The updated value at `k = j` is exactly the inserted vertex `x`.
      have hxk : Function.update b j x k = x := by
        simp [Function.update, hk]
      -- Reduce to `x ∈ insert x _`.
      rw [hxk]
      exact Set.mem_insert x _
    · rcases Fin.exists_succAbove_eq hk with ⟨i, rfl⟩
      refine Set.mem_insert_of_mem x ?_
      exact ⟨i, by simp [Function.update, Fin.succAbove_ne]⟩
  · intro hy
    rcases hy with (rfl | hy)
    · exact ⟨j, by simp [Function.update]⟩
    · rcases hy with ⟨i, rfl⟩
      exact ⟨j.succAbove i, by simp [Function.update, Fin.succAbove_ne]⟩

/-- Given two barycentric weight functions `μ` and `ν` with `μ ≥ 0` and `∑ μ = 1`, choose an index
`j` with `μ j > 0` minimizing `ν i / μ i` among `μ i > 0`. The resulting `j` satisfies the
cross-multiplied inequalities `ν j * μ i ≤ ν i * μ j`. -/
lemma exists_index_min_ratio_barycentric {m : ℕ} {μ ν : Fin (m + 1) → Real}
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : (∑ i, μ i) = 1) (hν0 : ∀ i, 0 ≤ ν i) :
    ∃ j : Fin (m + 1), 0 < μ j ∧ ∀ i, ν j * μ i ≤ ν i * μ j := by
  classical
  let s : Finset (Fin (m + 1)) := Finset.univ.filter fun i => 0 < μ i
  have hs : s.Nonempty := by
    have hex : ∃ i : Fin (m + 1), μ i ≠ 0 := by
      by_contra h
      push_neg at h
      have : (∑ i : Fin (m + 1), μ i) = 0 := by simp [h]
      simp [hμ1] at this
    rcases hex with ⟨i, hi0⟩
    have hi_pos : 0 < μ i := lt_of_le_of_ne (hμ0 i) (Ne.symm hi0)
    exact ⟨i, by simp [s, hi_pos]⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image s (fun i => ν i / μ i) hs
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro i
  by_cases hμi : 0 < μ i
  · have hi : i ∈ s := by simp [s, hμi]
    have hratio : ν j / μ j ≤ ν i / μ i := hjmin i hi
    exact (div_le_div_iff₀ (b := μ j) (d := μ i) (a := ν j) (c := ν i)
      (Finset.mem_filter.mp hj).2 hμi).1 hratio
  · have hμi0 : μ i = 0 := le_antisymm (le_of_not_gt hμi) (hμ0 i)
    have : 0 ≤ ν i * μ j := mul_nonneg (hν0 i) (le_of_lt (Finset.mem_filter.mp hj).2)
    simpa [hμi0] using this

/-- If `x` is an affine combination of an affinely independent family `b` with a positive weight
at `j`, then `x` does not lie in the affine span of the other vertices. -/
lemma not_mem_affineSpan_facet_of_barycentric_weight_pos {n m : ℕ}
    {b : Fin (m + 1) → Fin n → Real} (hb : AffineIndependent Real b) {x : Fin n → Real}
    {μ : Fin (m + 1) → Real} (hμ1 : (∑ i, μ i) = 1) (hx : x = ∑ i, μ i • b i)
    {j : Fin (m + 1)} (hμj : 0 < μ j) :
    x ∉ affineSpan Real (b '' { i | i ≠ j }) := by
  classical
  intro hxspan
  have hw : (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), μ i) = (1 : Real) := by
    simpa using hμ1
  have hxcomb :
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b μ = x := by
    calc
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b μ
          = ∑ i : Fin (m + 1), μ i • b i := by
              simp [Finset.affineCombination_eq_linear_combination, hw]
      _ = x := by simpa using hx.symm
  have hm :
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b μ ∈
        affineSpan Real (b '' { i | i ≠ j }) := by
    simpa [hxcomb] using hxspan
  have hμj0 :
      μ j = 0 :=
    hb.eq_zero_of_affineCombination_mem_affineSpan (fs := Finset.univ) (w := μ) (s := { i | i ≠ j })
      hw hm (by simp) (by simp)
  exact (ne_of_gt hμj) hμj0

/-- If `x` and `y` have barycentric coordinates `μ` and `ν` in a simplex, and `j` is chosen by the
min-ratio condition, then `y` lies in the convex hull of `x` and the facet opposite `j`. -/
lemma mem_cone_facet_of_min_ratio {n m : ℕ} {b : Fin (m + 1) → Fin n → Real} {x y : Fin n → Real}
    {μ ν : Fin (m + 1) → Real} (hμ1 : (∑ i, μ i) = 1) (hν0 : ∀ i, 0 ≤ ν i)
    (hν1 : (∑ i, ν i) = 1) (hx : x = ∑ i, μ i • b i) (hy : y = ∑ i, ν i • b i)
    {j : Fin (m + 1)} (hμj : 0 < μ j) (hcross : ∀ i, ν j * μ i ≤ ν i * μ j) :
    y ∈
      convexHull Real
        (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i))) := by
  classical
  let t : Real := ν j / μ j
  have htμj : t * μ j = ν j := by
    have hμjne : μ j ≠ 0 := ne_of_gt hμj
    dsimp [t]
    field_simp [hμjne]
  let b0 : Fin (m + 1) → Fin n → Real := Function.update b j x
  let g : Fin (m + 1) → Real := fun i => ν i - t * μ i
  let w : Fin (m + 1) → Real := Function.update g j t
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    by_cases hi : i = j
    · have ht0 : 0 ≤ t := div_nonneg (hν0 j) (le_of_lt hμj)
      simp [w, hi, ht0]
    · have hdiv : (ν j * μ i) / μ j ≤ ν i := by
        exact (div_le_iff₀ hμj).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcross i)
      have htμ : t * μ i ≤ ν i := by
        have htμ_eq : t * μ i = (ν j * μ i) / μ j := by
          simp [t, div_eq_mul_inv, mul_assoc, mul_comm]
        simpa [htμ_eq] using hdiv
      have : 0 ≤ g i := sub_nonneg.mpr htμ
      simpa [w, g, hi] using this
  have hw1 : (∑ i : Fin (m + 1), w i) = 1 := by
    have hjmem : j ∈ (Finset.univ : Finset (Fin (m + 1))) := by simp
    have hErase :
        (Finset.univ.erase j).sum g = (∑ i : Fin (m + 1), g i) - g j := by
      refine eq_sub_of_add_eq ?_
      exact
        Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (m + 1)))) (f := g) (a := j)
          (Finset.mem_univ j)
    have hsumg : (∑ i : Fin (m + 1), g i) = (1 : Real) - t := by
      have htm : (∑ i : Fin (m + 1), t * μ i) = t * (∑ i : Fin (m + 1), μ i) := by
        simpa using
          (Finset.mul_sum t (s := (Finset.univ : Finset (Fin (m + 1)))) (f := μ)).symm
      calc
        (∑ i : Fin (m + 1), g i) = (∑ i : Fin (m + 1), (ν i - t * μ i)) := by rfl
        _ = (∑ i : Fin (m + 1), ν i) - (∑ i : Fin (m + 1), t * μ i) := by
              simp [Finset.sum_sub_distrib]
        _ = (1 : Real) - t := by
              simp [hν1, hμ1, htm]
    calc
      (∑ i : Fin (m + 1), w i) = t + (Finset.univ.erase j).sum g := by
        simp [w, Finset.sum_update_of_mem hjmem]
      _ = t + ((∑ i : Fin (m + 1), g i) - g j) := by simp [hErase]
      _ = t + ((1 - t) - (ν j - t * μ j)) := by simp [hsumg, g]
      _ = 1 := by
        nlinarith [htμj]
  have hyw : y = ∑ i : Fin (m + 1), w i • b0 i := by
    have hjmem : j ∈ (Finset.univ : Finset (Fin (m + 1))) := by simp
    have hEq :
        (fun i : Fin (m + 1) => w i • b0 i) =
          Function.update (fun i => g i • b0 i) j (t • b0 j) := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp [w, b0, g]
      · simp [w, b0, g, hi]
    have hsum0 :
        (∑ i : Fin (m + 1), w i • b0 i) =
          t • b0 j + (Finset.univ.erase j).sum (fun i => g i • b0 i) := by
      simp [hEq, Finset.sum_update_of_mem hjmem]
    have hsum1 :
        (∑ i : Fin (m + 1), w i • b0 i) =
          t • x + (Finset.univ.erase j).sum (fun i => g i • b i) := by
      have hb0j : b0 j = x := by simp [b0]
      have hrest :
          (Finset.univ.erase j).sum (fun i => g i • b0 i) =
            (Finset.univ.erase j).sum (fun i => g i • b i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        simp [b0, hij]
      simp [hsum0, hb0j, hrest]
    have hsum_g :
        (Finset.univ.erase j).sum (fun i => g i • b i) =
          (Finset.univ.erase j).sum (fun i => ν i • b i) -
            (Finset.univ.erase j).sum (fun i => (t * μ i) • b i) := by
      calc
        (Finset.univ.erase j).sum (fun i => g i • b i)
            = (Finset.univ.erase j).sum (fun i => (ν i - t * μ i) • b i) := by rfl
        _ = (Finset.univ.erase j).sum (fun i => (ν i • b i - (t * μ i) • b i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [sub_smul]
        _ =
            (Finset.univ.erase j).sum (fun i => ν i • b i) -
              (Finset.univ.erase j).sum (fun i => (t * μ i) • b i) := by
              simp [Finset.sum_sub_distrib]
    have htx :
        t • x = ∑ i : Fin (m + 1), (t * μ i) • b i := by
      calc
        t • x = t • (∑ i : Fin (m + 1), μ i • b i) := by simp [hx]
        _ = ∑ i : Fin (m + 1), t • (μ i • b i) := by
              simpa using
                (Finset.smul_sum (s := (Finset.univ : Finset (Fin (m + 1))))
                  (f := fun i : Fin (m + 1) => μ i • b i) (r := t))
        _ = ∑ i : Fin (m + 1), (t * μ i) • b i := by
              simp [smul_smul]
    have hsplit :
        (∑ i : Fin (m + 1), (t * μ i) • b i) =
          (Finset.univ.erase j).sum (fun i => (t * μ i) • b i) + (t * μ j) • b j := by
      have := (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (m + 1))))
        (f := fun i : Fin (m + 1) => (t * μ i) • b i) (a := j) (by simp : j ∈ (Finset.univ : Finset (Fin (m + 1)))))
      -- `sum_erase_add` gives `erase` sum + term = full sum.
      exact this.symm
    have hy' : y = ∑ i : Fin (m + 1), ν i • b i := hy
    have hνsplit :
        (∑ i : Fin (m + 1), ν i • b i) =
          (Finset.univ.erase j).sum (fun i => ν i • b i) + (ν j) • b j := by
      have := (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (m + 1))))
        (f := fun i : Fin (m + 1) => ν i • b i) (a := j) (by simp : j ∈ (Finset.univ : Finset (Fin (m + 1)))))
      exact this.symm
    -- Put everything together.
    have :
        (∑ i : Fin (m + 1), w i • b0 i) = ∑ i : Fin (m + 1), ν i • b i := by
      calc
        (∑ i : Fin (m + 1), w i • b0 i)
            = t • x + (Finset.univ.erase j).sum (fun i => g i • b i) := hsum1
        _ = t • x +
              (((Finset.univ.erase j).sum (fun i => ν i • b i)) -
                ((Finset.univ.erase j).sum (fun i => (t * μ i) • b i))) := by
              simp [hsum_g]
        _ = (∑ i : Fin (m + 1), (t * μ i) • b i) +
              (((Finset.univ.erase j).sum (fun i => ν i • b i)) -
                ((Finset.univ.erase j).sum (fun i => (t * μ i) • b i))) := by
              simp [htx]
        _ = (((Finset.univ.erase j).sum (fun i => (t * μ i) • b i)) + (t * μ j) • b j) +
              (((Finset.univ.erase j).sum (fun i => ν i • b i)) -
                ((Finset.univ.erase j).sum (fun i => (t * μ i) • b i))) := by
              rw [hsplit]
        _ = (t * μ j) • b j + (Finset.univ.erase j).sum (fun i => ν i • b i) := by
              abel
        _ = (ν j) • b j + (Finset.univ.erase j).sum (fun i => ν i • b i) := by
              simp [htμj]
        _ = ∑ i : Fin (m + 1), ν i • b i := by
              -- reorder using `hνsplit`.
              have hcomm :
                  (ν j) • b j + (Finset.univ.erase j).sum (fun i => ν i • b i) =
                    (Finset.univ.erase j).sum (fun i => ν i • b i) + (ν j) • b j := by
                ac_rfl
              -- `hνsplit` was proved as `sum = erase + term`, so use its symmetric form.
              exact hcomm.trans hνsplit.symm
    simpa [hy'] using this.symm
  -- Interpret `y` as a convex combination of the updated vertex family.
  have hy_mem :
      y ∈ convexHull Real (Set.range b0) := by
    have :
        y ∈ {y : Fin n → Real |
          ∃ w' : Fin (m + 1) → Real, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i = (1 : Real)) ∧
            y = ∑ i, w' i • b0 i} :=
      ⟨w, hw0, hw1, hyw⟩
    simpa [convexHull_range_eq_setOf_weighted_sum] using this
  -- Rewrite `Set.range b0` to match the desired facet-vertex description.
  have hrange :
      Set.range b0 =
        Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)) := by
    simpa [b0] using (range_update_eq_insert_range_succAbove (b := b) (j := j) (x := x))
  simpa [b0, hrange] using hy_mem

/-- The convex hull of `x` and a facet of an `m`-simplex is again an `m`-simplex, provided `x` is
not in the affine span of that facet. -/
lemma isSimplex_cone_over_facet {n m : ℕ} {b : Fin (m + 1) → Fin n → Real} (hb : AffineIndependent Real b)
    {x : Fin n → Real} {μ : Fin (m + 1) → Real} (hμ1 : (∑ i, μ i) = 1)
    (hx : x = ∑ i, μ i • b i) {j : Fin (m + 1)} (hμj : 0 < μ j) :
    let P : Set (Fin n → Real) :=
      convexHull Real (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))
    IsSimplex n m P := by
  classical
  intro P
  let b0 : Fin (m + 1) → Fin n → Real := Function.update b j x
  have hrange :
      Set.range b0 =
        Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)) := by
    simpa [b0] using (range_update_eq_insert_range_succAbove (b := b) (j := j) (x := x))
  have hnot :
      x ∉ affineSpan Real (b0 '' { i | i ≠ j }) := by
    have hnot' :
        x ∉ affineSpan Real (b '' { i | i ≠ j }) :=
      not_mem_affineSpan_facet_of_barycentric_weight_pos (b := b) hb hμ1 hx hμj
    have himage : b0 '' { i | i ≠ j } = b '' { i | i ≠ j } := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, hi, ?_⟩
        have hij : i ≠ j := by simpa using hi
        simp [b0, hij]
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, hi, ?_⟩
        have hij : i ≠ j := by simpa using hi
        simp [b0, hij]
    simpa [himage, b0] using hnot'
  have hrest : AffineIndependent Real (fun i : { y : Fin (m + 1) // y ≠ j } => b0 i) := by
    let e : { y : Fin (m + 1) // y ≠ j } ↪ Fin (m + 1) := ⟨Subtype.val, Subtype.val_injective⟩
    have : (fun i : { y : Fin (m + 1) // y ≠ j } => b0 i) = fun i => b (e i) := by
      funext i
      simp [b0, e, i.property]
    simpa [this] using hb.comp_embedding e
  have hb0 : AffineIndependent Real b0 :=
    (AffineIndependent.affineIndependent_of_notMem_span (p := b0) (i := j) hrest (by
      simpa [b0] using hnot))
  refine ⟨b0, hb0, ?_⟩
  -- Match the simplex set definition.
  simp [P, b0, hrange]

/-- Theorem 10.1.6. Let `C ⊆ ℝ^n` be a simplex with vertices `x₀, x₁, …, x_m`, and let `x ∈ C`.
Then `C` can be triangulated into finitely many simplices having `x` as a vertex. More precisely,
for every `y ∈ C` there exists a simplex `P ⊆ C` whose vertices consist of `x` together with `m`
of the `m+1` vertices of `C`, and such that `y ∈ P`. -/
theorem simplex_exists_subsimplex_through_point {n m : ℕ} {C : Set (Fin n → Real)}
    {x : Fin n → Real} (hC : IsSimplex n m C) (hx : x ∈ C) :
    ∃ b : Fin (m + 1) → Fin n → Real,
      AffineIndependent Real b ∧
        C = convexHull Real (Set.range b) ∧
          ∀ y ∈ C,
            ∃ j : Fin (m + 1),
              let P : Set (Fin n → Real) :=
                convexHull Real
                  (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))
              P ⊆ C ∧ IsSimplex n m P ∧ x ∈ P ∧ y ∈ P := by
  classical
  rcases hC with ⟨b, hb, rfl⟩
  refine ⟨b, hb, rfl, ?_⟩
  intro y hy
  -- Barycentric coordinates for `x` and `y` in the simplex `convexHull (range b)`.
  have hxw :
      ∃ μ : Fin (m + 1) → Real, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i = (1 : Real)) ∧
        x = ∑ i, μ i • b i := by
    have : x ∈ {y : Fin n → Real |
        ∃ w : Fin (m + 1) → Real, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧
          x = ∑ i, w i • b i} := by
      simpa [convexHull_range_eq_setOf_weighted_sum] using hx
    simpa using this
  have hyw :
      ∃ ν : Fin (m + 1) → Real, (∀ i, 0 ≤ ν i) ∧ (∑ i, ν i = (1 : Real)) ∧
        y = ∑ i, ν i • b i := by
    have : y ∈ {y : Fin n → Real |
        ∃ w : Fin (m + 1) → Real, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧
          y = ∑ i, w i • b i} := by
      simpa [convexHull_range_eq_setOf_weighted_sum] using hy
    simpa using this
  rcases hxw with ⟨μ, hμ0, hμ1, hxμ⟩
  rcases hyw with ⟨ν, hν0, hν1, hyν⟩
  rcases exists_index_min_ratio_barycentric (μ := μ) (ν := ν) hμ0 hμ1 hν0 with ⟨j, hμj, hcross⟩
  refine ⟨j, ?_⟩
  -- Define the candidate subsimplex.
  let P : Set (Fin n → Real) :=
    convexHull Real (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))
  have hPC : P ⊆ convexHull Real (Set.range b) := by
    refine convexHull_min ?_ (convex_convexHull Real (Set.range b))
    intro z hz
    rcases hz with (rfl | hz)
    · exact hx
    · rcases hz with ⟨i, rfl⟩
      exact (subset_convexHull (𝕜 := Real) (s := Set.range b)) ⟨j.succAbove i, rfl⟩
  have hxP : x ∈ P := by
    refine (subset_convexHull (𝕜 := Real)
      (s := Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))) ?_
    exact Set.mem_insert x _
  have hyP : y ∈ P := by
    simpa [P] using
      (mem_cone_facet_of_min_ratio (b := b) (x := x) (y := y) (μ := μ) (ν := ν)
        hμ1 hν0 hν1 hxμ hyν hμj hcross)
  have hsimplexP : IsSimplex n m P := by
    simpa [P] using
      (isSimplex_cone_over_facet (b := b) hb (x := x) (μ := μ) hμ1 hxμ (j := j) hμj)
  exact ⟨hPC, hsimplexP, hxP, hyP⟩

/-- Upper semicontinuity within a finite union (binary case). -/
lemma upperSemicontinuousWithinAt_union {α : Type*} [TopologicalSpace α] {β : Type*} [Preorder β]
    {f : α → β} {s t : Set α} {x : α} :
    UpperSemicontinuousWithinAt f s x → UpperSemicontinuousWithinAt f t x →
      UpperSemicontinuousWithinAt f (s ∪ t) x := by
  intro hs ht y hxy
  have hs' : ∀ᶠ x' in nhdsWithin x s, f x' < y := hs y hxy
  have ht' : ∀ᶠ x' in nhdsWithin x t, f x' < y := ht y hxy
  have : ∀ᶠ x' in nhdsWithin x s ⊔ nhdsWithin x t, f x' < y :=
    (Filter.eventually_sup.2 ⟨hs', ht'⟩)
  simpa [UpperSemicontinuousWithinAt, nhdsWithin_union] using this

/-- Upper semicontinuity within a `sUnion` of finitely many sets. -/
lemma upperSemicontinuousWithinAt_sUnion_of_finite {α : Type*} [TopologicalSpace α] {β : Type*}
    [Preorder β] {f : α → β} {x : α} {𝒮 : Set (Set α)} (h𝒮 : 𝒮.Finite)
    (husc : ∀ s ∈ 𝒮, UpperSemicontinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f (⋃₀ 𝒮) x := by
  intro y hxy
  have h' : ∀ s, ∀ hs : s ∈ 𝒮, ∀ᶠ x' in nhdsWithin x s, f x' < y :=
    fun s hs => husc s hs y hxy
  have : ∀ᶠ x' in ⨆ s ∈ 𝒮, nhdsWithin x s, f x' < y :=
    (Filter.eventually_iSup.2 fun s => (Filter.eventually_iSup.2 fun hs => h' s hs))
  simpa [UpperSemicontinuousWithinAt, nhdsWithin_sUnion h𝒮] using this

/-- Upper semicontinuity withinAt is invariant under local equality of the underlying set. -/
lemma upperSemicontinuousWithinAt_congr_of_local_eq {α : Type*} [TopologicalSpace α] {β : Type*}
    [Preorder β] {f : α → β} {s t U : Set α} {x : α} (hU : U ∈ nhds x)
    (hEq : U ∩ s = U ∩ t) :
    UpperSemicontinuousWithinAt f s x ↔ UpperSemicontinuousWithinAt f t x := by
  have hEvent : s =ᶠ[nhds x] t := by
    refine Filter.mem_of_superset hU ?_
    intro y hyU
    have : (y ∈ s ↔ y ∈ t) := by
      constructor
      · intro hys
        have : y ∈ U ∩ s := ⟨hyU, hys⟩
        have : y ∈ U ∩ t := by simpa [hEq] using this
        exact this.2
      · intro hyt
        have : y ∈ U ∩ t := ⟨hyU, hyt⟩
        have : y ∈ U ∩ s := by simpa [hEq] using this
        exact this.2
    exact propext this
  have hnhds : nhdsWithin x s = nhdsWithin x t :=
    (nhdsWithin_eq_iff_eventuallyEq (s := s) (t := t) (x := x)).2 hEvent
  constructor
  · intro hs y hxy
    simpa [UpperSemicontinuousWithinAt, hnhds] using hs y hxy
  · intro ht y hxy
    simpa [UpperSemicontinuousWithinAt, hnhds] using ht y hxy

/-- A finite affine-combination inequality from epigraph convexity: if `f (x i) ≤ μ i` for
`i ∈ s`, then `f` at the affine combination is bounded above by the real affine combination of
the `μ i`. -/
lemma Section10.convexFunctionOn_le_affineCombination_real {n : ℕ} {ι : Type*}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (s : Finset ι) (x : ι → Fin n → Real) (μ w : ι → Real)
    (hμ : ∀ i ∈ s, f (x i) ≤ (μ i : EReal)) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : s.sum w = 1) :
    f (s.affineCombination ℝ x w) ≤ ((∑ i ∈ s, w i * μ i : Real) : EReal) := by
  classical
  have hconv : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunctionOn] using hf
  let z : ι → (Fin n → Real) × Real := fun i => (x i, μ i)
  have hz : ∀ i ∈ s, z i ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    intro i hi
    refine ⟨by trivial, ?_⟩
    simpa [z] using hμ i hi
  have hmem :
      (∑ i ∈ s, w i • z i) ∈ epigraph (Set.univ : Set (Fin n → Real)) f :=
    hconv.sum_mem (t := s) (w := w) (z := z) hw0 hw1 hz
  have hle :
      f (∑ i ∈ s, w i • (z i)).1 ≤ ((∑ i ∈ s, w i • (z i)).2 : EReal) := by
    simpa [epigraph] using hmem.2
  -- Unpack the two coordinates of the weighted sum.
  have hfst :
      (∑ i ∈ s, w i • z i).1 = s.affineCombination ℝ x w := by
    have hfst' : (∑ i ∈ s, w i • z i).1 = ∑ i ∈ s, w i • x i := by
      simp [Prod.fst_sum, z]
    have hcomb : s.affineCombination ℝ x w = ∑ i ∈ s, w i • x i := by
      simp [Finset.affineCombination_eq_linear_combination, hw1]
    simpa [hcomb] using hfst'
  have hsnd :
      (∑ i ∈ s, w i • z i).2 = (∑ i ∈ s, w i * μ i : Real) := by
    simp [Prod.snd_sum, z, smul_eq_mul]
  simpa [hfst, hsnd] using hle

/-- A simplex contained in the effective domain admits a uniform *real* upper bound. -/
lemma Section10.simplex_real_upper_bound_of_dom {n m : ℕ} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {P : Set (Fin n → Real)}
    (hP : IsSimplex n m P) (hPdom : P ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ∃ M : Real, ∀ z ∈ P, f z ≤ (M : EReal) := by
  classical
  rcases hP with ⟨b, hb, rfl⟩
  -- Choose a real bound from the finitely many vertex values.
  let s : Finset Real :=
    (Finset.univ : Finset (Fin (m + 1))).image fun i => (f (b i)).toReal
  have hs : s.Nonempty := by
    refine (Finset.image_nonempty).2 ?_
    exact (Finset.univ_nonempty : (Finset.univ : Finset (Fin (m + 1))).Nonempty)
  let M : Real := s.max' hs
  refine ⟨M, ?_⟩
  intro z hz
  have hvertex_le : ∀ i : Fin (m + 1), f (b i) ≤ (M : EReal) := by
    intro i
    have hbi : b i ∈ convexHull Real (Set.range b) :=
      (subset_convexHull (𝕜 := Real) (s := Set.range b)) ⟨i, rfl⟩
    have hbi_dom : b i ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
      hPdom hbi
    have hltTop : f (b i) < (⊤ : EReal) := by
      have : b i ∈ (Set.univ : Set (Fin n → Real)) ∧ f (b i) < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hbi_dom
      exact this.2
    have hneTop : f (b i) ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hltTop
    have hle_toReal : f (b i) ≤ ((f (b i)).toReal : EReal) :=
      EReal.le_coe_toReal (x := f (b i)) hneTop
    have htoReal_mem : (f (b i)).toReal ∈ s := by
      refine Finset.mem_image.2 ?_
      exact ⟨i, Finset.mem_univ i, rfl⟩
    have htoReal_le : (f (b i)).toReal ≤ M := s.le_max' _ htoReal_mem
    have hcoe_le : ((f (b i)).toReal : EReal) ≤ (M : EReal) := by
      exact_mod_cast htoReal_le
    exact le_trans hle_toReal hcoe_le
  -- Represent `z` as a convex combination of vertices.
  rcases (by
    simpa [convexHull_range_eq_setOf_weighted_sum] using hz) with ⟨w, hw0, hw1, rfl⟩
  have hμ' :
      ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
        f (b i) ≤ (M : EReal) := by
    intro i hi
    simpa using hvertex_le i
  have hw0' : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w i := by
    intro i hi
    exact hw0 i
  have hw1' : (Finset.univ : Finset (Fin (m + 1))).sum w = 1 := by
    simpa using hw1
  have hle :=
    Section10.convexFunctionOn_le_affineCombination_real (hf := hf)
      (s := (Finset.univ : Finset (Fin (m + 1)))) (x := b) (μ := fun _ => M) (w := w)
      hμ' hw0' hw1'
  -- Simplify the right-hand side to `M`.
  have hsum :
      (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * M : Real) = M := by
    have hw1'' :
        (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := by
      simpa using hw1
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * M : Real)
          = (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) * M := by
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset (Fin (m + 1)))) (f := w) (a := M)).symm
      _ = (1 : Real) * M := by simp [hw1'']
      _ = M := by simp
  have hle' :
      f (∑ i : Fin (m + 1), w i • b i) ≤ ((∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * M : Real) : EReal) := by
    -- Convert the affine combination back to a linear combination (sum weights = 1).
    have hw1'' :
        (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := by
      simpa using hw1
    simpa [Finset.affineCombination_eq_linear_combination, hw1''] using hle
  simpa [hsum] using hle'

/-- Given an affinely independent family of vertices, build an `AffineBasis` for their affine span. -/
noncomputable def Section10.simplex_affineBasis_on_affineSpan {n m : ℕ}
    {b : Fin (m + 1) → Fin n → Real} (hb : AffineIndependent Real b) :
    AffineBasis (Fin (m + 1)) Real (affineSpan Real (Set.range b)) := by
  classical
  let s : AffineSubspace Real (Fin n → Real) := affineSpan Real (Set.range b)
  haveI : Nonempty (Set.range b) := ⟨⟨b 0, ⟨0, rfl⟩⟩⟩
  haveI : Nonempty (affineSpan Real (Set.range b)) :=
    ⟨⟨b 0, subset_affineSpan Real (Set.range b) ⟨0, rfl⟩⟩⟩
  let b' : Fin (m + 1) → affineSpan Real (Set.range b) := fun i =>
    ⟨b i, subset_affineSpan Real (Set.range b) ⟨i, rfl⟩⟩
  have hb' : AffineIndependent Real b' := by
    have hinj : Function.Injective (s.subtype) := AffineSubspace.subtype_injective s
    have : AffineIndependent Real (s.subtype ∘ b') := by
      simpa [s, b', Function.comp] using hb
    exact (AffineMap.affineIndependent_iff (f := s.subtype) hinj).1 this
  have hrange :
      (((↑) : affineSpan Real (Set.range b) → Fin n → Real) ⁻¹' Set.range b) = Set.range b' := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      simpa [b'] using hi
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have htot : affineSpan Real (Set.range b') = ⊤ := by
    simpa [hrange] using (affineSpan_coe_preimage_eq_top (k := Real) (A := Set.range b))
  exact ⟨b', hb', htot⟩

set_option maxHeartbeats 2000000 in
-- Needed to avoid timeouts in the continuity argument for barycentric coordinates.
/-- In the relative topology of a simplex, the barycentric coordinate at a vertex tends to `1`. -/
lemma Section10.vertex_coord_eventually_gt {n m : ℕ} {b : Fin (m + 1) → Fin n → Real}
    (hb : AffineIndependent Real b) (j : Fin (m + 1)) {δ : Real} (hδ : 0 < δ) :
    ∀ᶠ z : {z // z ∈ convexHull Real (Set.range b)} in
      nhds
        (⟨b j,
          (subset_convexHull (𝕜 := Real) (s := Set.range b) ⟨j, rfl⟩)⟩ :
          {z // z ∈ convexHull Real (Set.range b)}),
      (1 - δ) <
        (Section10.simplex_affineBasis_on_affineSpan (b := b) hb).coord j
          ⟨z.1, convexHull_subset_affineSpan (𝕜 := Real) (s := Set.range b) z.2⟩ := by
  classical
  set S : Set (Fin n → Real) := convexHull Real (Set.range b)
  set B : AffineBasis (Fin (m + 1)) Real (affineSpan Real (Set.range b)) :=
    Section10.simplex_affineBasis_on_affineSpan (b := b) hb
  set z0 : {z // z ∈ S} :=
    (⟨b j, (subset_convexHull (𝕜 := Real) (s := Set.range b) ⟨j, rfl⟩)⟩ : {z // z ∈ S})
  let incl : {z // z ∈ S} → affineSpan Real (Set.range b) :=
    fun z => ⟨z.1, convexHull_subset_affineSpan (𝕜 := Real) (s := Set.range b) z.2⟩
  let g : {z // z ∈ S} → Real := fun z => B.coord j (incl z)
  have hcont_incl : Continuous incl :=
    (continuous_subtype_val.subtype_mk fun z =>
      convexHull_subset_affineSpan (𝕜 := Real) (s := Set.range b) z.2)
  have hcont_g : Continuous g := by
    simpa [g, Function.comp] using
      ((B.coord j).continuous_of_finiteDimensional.comp hcont_incl)
  have hg0 : g z0 = 1 := by
    have hincl : incl z0 = B j := by
      ext
      rfl
    simp [g, hincl]
  have hI : Set.Ioi (1 - δ) ∈ nhds (1 : Real) := Ioi_mem_nhds (by linarith)
  have hI' : Set.Ioi (1 - δ) ∈ nhds (g z0) := by
    simpa [hg0] using hI
  have : g ⁻¹' Set.Ioi (1 - δ) ∈ nhds z0 := by
    simpa using (hcont_g.continuousAt.tendsto hI')
  simpa [Filter.Eventually, g, Set.preimage, Set.mem_Ioi, S, z0] using this

end Section10
end Chap02
