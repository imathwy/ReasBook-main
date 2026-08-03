import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_12
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 14 16: the conjugate of a `Γ₀(H)` function has nonempty domain. -/
private theorem dom_conjugate_nonempty_of_mem_gammaZero_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (dom f.asEReal∗).Nonempty := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  rcases hfConj.2.nonempty with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [gammaZeroConjugate_apply, effectiveDomain, dom] using hu

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 16: a strict liminf lower bound for `f x / ‖x‖` yields a radius
outside which `f x` dominates `α ‖x‖`. -/
private theorem eventually_mul_lower_bound_of_lt_liminf_div_norm
    (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ)
    (hliminf :
      (α : EReal) <
        Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)) :
    ∃ R : ℝ,
      ∀ x : H, R ≤ ‖x‖ → (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
  have hquot :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
        (α : EReal) < f.asEReal x / ‖x‖ :=
    Filter.eventually_lt_of_lt_liminf hliminf
  rcases Filter.mem_comap.1 hquot with ⟨s, hs, hs_subset⟩
  rcases Filter.mem_atTop_sets.1 hs with ⟨R0, hR0⟩
  refine ⟨max R0 1, ?_⟩
  intro x hx
  have hxR0 : R0 ≤ ‖x‖ := le_trans (le_max_left _ _) hx
  have hxone : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) hx
  have hxmem : ‖x‖ ∈ s := hR0 _ hxR0
  have hquotx : (α : EReal) < f.asEReal x / ‖x‖ := hs_subset hxmem
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hxone
  exact le_of_lt <| (EReal.lt_div_iff hnorm_pos (by simp)).1 hquotx

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 16: a real lower bound on a closed ball can be upgraded to an
affine-norm lower bound there after decreasing the intercept by `|α| R`. -/
private theorem affine_lower_bound_on_closedBall_of_real_lowerBound
    (f : H → Set.Ioi (⊥ : EReal)) (α m R : ℝ)
    (hm : ∀ x ∈ Metric.closedBall (0 : H) R, (m : EReal) ≤ f.asEReal x) :
    ∀ x ∈ Metric.closedBall (0 : H) R,
      (((α * ‖x‖ + min 0 (m - |α| * R) : ℝ) : EReal)) ≤ f.asEReal x := by
  intro x hx
  have hxnorm : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hmul : α * ‖x‖ ≤ |α| * R := by
    calc
      α * ‖x‖ ≤ |α| * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (le_abs_self α) (norm_nonneg x)
      _ ≤ |α| * R := by
        exact mul_le_mul_of_nonneg_left hxnorm (abs_nonneg α)
  have hreal : α * ‖x‖ + min 0 (m - |α| * R) ≤ m := by
    nlinarith [min_le_right 0 (m - |α| * R), hmul]
  have hcast :
      (((α * ‖x‖ + min 0 (m - |α| * R) : ℝ) : EReal)) ≤ (m : EReal) := by
    exact_mod_cast hreal
  exact le_trans hcast (hm x hx)

/-- Helper for Proposition 14 16: a positive asymptotic slope yields a global affine lower
bound with the same slope. -/
private theorem exists_affine_lowerBound_of_positive_liminf
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (α : ℝ)
    (hliminf :
      (α : EReal) <
        Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)) :
    ∃ β : ℝ,
      (fun x : H ↦ ((α * ‖x‖ + β : ℝ) : EReal)) ≤ f.asEReal := by
  rcases eventually_mul_lower_bound_of_lt_liminf_div_norm f α hliminf with ⟨R0, hR0⟩
  let R : ℝ := max R0 0
  have houtside :
      ∀ x : H, R ≤ ‖x‖ → (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
    intro x hx
    exact hR0 x (le_trans (le_max_left _ _) hx)
  have hdom : (dom f.asEReal∗).Nonempty := dom_conjugate_nonempty_of_mem_gammaZero_local f hf
  have hball_bounded : Bornology.IsBounded (Metric.closedBall (0 : H) R) :=
    Metric.isBounded_closedBall
  rcases exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
      f.asEReal hdom (Metric.closedBall (0 : H) R) hball_bounded with ⟨m, hm⟩
  refine ⟨min 0 (m - |α| * R), ?_⟩
  intro x
  by_cases hxnorm : ‖x‖ ≤ R
  · have hxball : x ∈ Metric.closedBall (0 : H) R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxnorm
    exact affine_lower_bound_on_closedBall_of_real_lowerBound f α m R hm x hxball
  · have hRle : R ≤ ‖x‖ := le_of_not_ge hxnorm
    have htail : (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := houtside x hRle
    have hreal : α * ‖x‖ + min 0 (m - |α| * R) ≤ α * ‖x‖ := by
      nlinarith [min_le_left 0 (m - |α| * R)]
    have hshift :
        (((α * ‖x‖ + min 0 (m - |α| * R) : ℝ) : EReal)) ≤
          (((α * ‖x‖ : ℝ) : EReal)) := by
      exact_mod_cast hreal
    exact le_trans hshift htail

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 16: an affine lower bound with positive slope forces the quotient
`f x / ‖x‖` to dominate every smaller real level eventually. -/
private theorem eventually_lt_div_norm_of_affine_lowerBound
    (f : H → Set.Ioi (⊥ : EReal)) (α : Set.Ioi (0 : ℝ)) (β : ℝ)
    (hbound :
      (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal)
    {y : ℝ} (hy : y < (α : ℝ)) :
    ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
      (y : EReal) < f.asEReal x / ‖x‖ := by
  let R : ℝ := max 1 (|β| / ((α : ℝ) - y) + 1)
  have hR :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, R ≤ ‖x‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop R
  filter_upwards [hR] with x hx
  have hxone : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_left _ _) hx
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hxone
  have hboundx :
      ((((α : ℝ) * ‖x‖ + β : ℝ) : EReal)) ≤ f.asEReal x := by
    simpa [scaledNormKernelOfPos_apply, add_comm, add_left_comm, add_assoc] using hbound x
  have hδpos : 0 < (α : ℝ) - y := sub_pos.mpr hy
  have hβlt : |β| < ((α : ℝ) - y) * ‖x‖ := by
    have hxR : |β| / ((α : ℝ) - y) + 1 ≤ ‖x‖ := le_trans (le_max_right _ _) hx
    have hβdivlt : |β| / ((α : ℝ) - y) < ‖x‖ := by
      linarith
    simpa [mul_comm] using (div_lt_iff₀ hδpos).mp hβdivlt
  have hβlower : -((α : ℝ) - y) * ‖x‖ < β := by
    have hnegabs : -|β| ≤ β := neg_abs_le β
    nlinarith
  have hylt : y * ‖x‖ < (α : ℝ) * ‖x‖ + β := by
    nlinarith
  have hprod : (y : EReal) * ‖x‖ < f.asEReal x := by
    exact lt_of_lt_of_le (by exact_mod_cast hylt) hboundx
  exact (EReal.lt_div_iff hnorm_pos (by simp)).2 hprod

omit [CompleteSpace H] in
/-- Helper for Proposition 14 16: a positive affine lower bound is equivalent to boundedness of
the conjugate on the closed ball centered at `0` with the same radius. -/
private theorem exists_affine_lowerBound_iff_conjugate_boundedAbove_on_closedBall
    (f : H → Set.Ioi (⊥ : EReal)) (α : Set.Ioi (0 : ℝ)) :
    (∃ β : ℝ,
      (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal) ↔
      ∃ γ : ℝ,
        ∀ u ∈ Metric.closedBall (0 : H) (α : ℝ), f.asEReal∗ u ≤ (γ : EReal) := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨-β, ?_⟩
    intro u hu
    have hu_norm : ‖u‖ ≤ (α : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have hepigraph : (u, -β) ∈ epigraph f.asEReal∗ := by
      refine (mem_epigraph_conjugate_iff f.asEReal u (-β)).2 ?_
      intro x
      have hinner : ⟪x, u⟫_ℝ ≤ (α : ℝ) * ‖x‖ := by
        nlinarith [real_inner_le_norm x u, hu_norm, norm_nonneg x]
      have hboundx :
          ((((α : ℝ) * ‖x‖ + β : ℝ) : EReal)) ≤ f.asEReal x := by
        simpa [scaledNormKernelOfPos_apply, add_comm, add_left_comm, add_assoc] using hβ x
      have hreal : ⟪x, u⟫_ℝ + β ≤ (α : ℝ) * ‖x‖ + β := by
        linarith
      have hcast :
          (((⟪x, u⟫_ℝ + β : ℝ) : EReal)) ≤
            ((((α : ℝ) * ‖x‖ + β : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using le_trans hcast hboundx
    simpa [mem_epigraph_iff] using hepigraph
  · rintro ⟨γ, hγ⟩
    refine ⟨-γ, ?_⟩
    intro x
    by_cases hx : x = 0
    · have hzero_ball : (0 : H) ∈ Metric.closedBall (0 : H) (α : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using α.2.le
      have h0epi : ((0 : H), γ) ∈ epigraph f.asEReal∗ := by
        simpa [mem_epigraph_iff] using hγ 0 hzero_ball
      have h0minor := (mem_epigraph_conjugate_iff f.asEReal (0 : H) γ).1 h0epi (0 : H)
      simpa [hx, scaledNormKernelOfPos_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using h0minor
    · let u : H := ((α : ℝ) / ‖x‖) • x
      have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu_mem : u ∈ Metric.closedBall (0 : H) (α : ℝ) := by
        have hratio : (((α : ℝ) / ‖x‖) : ℝ) * ‖x‖ = (α : ℝ) := by
          field_simp [hxnorm_pos.ne']
        have hu_norm : ‖u‖ ≤ (α : ℝ) := by
          have hnonneg : 0 ≤ ((α : ℝ) / ‖x‖) := div_nonneg α.2.le (norm_nonneg x)
          calc
            ‖u‖ = ‖((α : ℝ) / ‖x‖)‖ * ‖x‖ := by
              simpa [u] using norm_smul (((α : ℝ) / ‖x‖)) x
            _ = (α : ℝ) := by
              rw [Real.norm_of_nonneg hnonneg, hratio]
            _ ≤ (α : ℝ) := le_rfl
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_norm
      have hux : ⟪x, u⟫_ℝ = (α : ℝ) * ‖x‖ := by
        calc
          ⟪x, u⟫_ℝ = ((α : ℝ) / ‖x‖) * ⟪x, x⟫_ℝ := by
            simp [u, real_inner_smul_right]
          _ = ((α : ℝ) / ‖x‖) * ‖x‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
          _ = (α : ℝ) * ‖x‖ := by
            simp [pow_two, div_eq_mul_inv, mul_assoc, hxnorm_pos.ne']
      have hux_epi : (u, γ) ∈ epigraph f.asEReal∗ := by
        simpa [mem_epigraph_iff] using hγ u hu_mem
      have hux_minor := (mem_epigraph_conjugate_iff f.asEReal u γ).1 hux_epi x
      simpa [scaledNormKernelOfPos_apply, hux, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hux_minor

/-- Helper for Proposition 14 16: Corollary 8.39 identifies the continuity points on the
effective domain of a `Γ₀(H)` function with the interior of that effective domain. -/
private theorem continuous_points_eq_interior_effectiveDomain_of_mem_gammaZero
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain g ∧
      ContinuousAt (fun y : H ↦ (g y : EReal).toReal) x} = interior (effectiveDomain g) := by
  exact
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      g hg.2 (Or.inr (Or.inl hg.1))

/-- Helper for Proposition 14 16: if one real lower level set is bounded, then convexity upgrades
that boundedness to a global affine lower bound with strictly positive norm slope. -/
private theorem exists_affine_lowerBound_of_bounded_lowerLevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hlevel : ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f.asEReal ξ)) :
    ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
      (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal := by
  rcases hf.2.nonempty with ⟨p, hp⟩
  let m : ℝ := (f p : EReal).toReal
  let ξ : ℝ := m + 1
  have hp_le : f.asEReal p ≤ (ξ : EReal) := by
    have hp_top : f.asEReal p ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
    have hp_bot : f.asEReal p ≠ ⊥ := ne_of_gt (f p).2
    rw [← EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)
  have hp_level : p ∈ lowerLevelSet f.asEReal ξ := by
    rw [mem_lowerLevelSet_iff]
    exact hp_le
  have hξ_bounded : Bornology.IsBounded (lowerLevelSet f.asEReal ξ) := hlevel ξ
  rcases hξ_bounded.subset_ball p with ⟨R, hR⟩
  have hR_pos : 0 < R := by
    have hp_ball : p ∈ Metric.ball p R := hR hp_level
    simpa [Metric.mem_ball] using hp_ball
  have hdom_conj : (dom f.asEReal∗).Nonempty :=
    dom_conjugate_nonempty_of_mem_gammaZero_local f hf
  rcases exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
      f.asEReal hdom_conj (lowerLevelSet f.asEReal ξ) hξ_bounded with ⟨c, hc⟩
  let α : Set.Ioi (0 : ℝ) := ⟨R⁻¹, inv_pos.mpr hR_pos⟩
  let β_out : ℝ := m - (α : ℝ) * ‖p‖
  let β_in : ℝ := c - (α : ℝ) * (‖p‖ + R)
  refine ⟨α, min β_out β_in, ?_⟩
  intro x
  by_cases hx_level : x ∈ lowerLevelSet f.asEReal ξ
  · have hx_ball : x ∈ Metric.ball p R := hR hx_level
    have hx_norm_ball : ‖x - p‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx_ball
    have hx_norm : ‖x‖ ≤ ‖p‖ + R := by
      calc
        ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm] using norm_add_le (x - p) p
        _ ≤ ‖p‖ + R := by
          linarith
    have hreal : (α : ℝ) * ‖x‖ + min β_out β_in ≤ c := by
      have hαx : (α : ℝ) * ‖x‖ ≤ (α : ℝ) * (‖p‖ + R) :=
        mul_le_mul_of_nonneg_left hx_norm α.2.le
      have hβ : min β_out β_in ≤ β_in := min_le_right _ _
      have hsum :
          (α : ℝ) * ‖x‖ + min β_out β_in ≤ (α : ℝ) * (‖p‖ + R) + β_in :=
        add_le_add hαx hβ
      dsimp [β_in] at hsum
      linarith
    have hcast : (((((α : ℝ) * ‖x‖ + min β_out β_in : ℝ)) : EReal)) ≤ (c : EReal) := by
      exact_mod_cast hreal
    exact le_trans hcast (hc x hx_level)
  · by_cases hxtop : f.asEReal x = ⊤
    · rw [hxtop]
      exact le_top
    · have hx_dom : x ∈ effectiveDomain f := by
        rw [mem_effectiveDomain_iff]
        exact lt_of_le_of_ne le_top hxtop
      have hxp : x ≠ p := by
        intro hxp
        exact hx_level (hxp ▸ hp_level)
      have hfx_top : f.asEReal x ≠ ⊤ := hxtop
      have hfx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
      have hfx_gt : (ξ : EReal) < f.asEReal x := by
        rw [mem_lowerLevelSet_iff] at hx_level
        exact lt_of_not_ge hx_level
      have hfx_real_gt : ξ < (f.asEReal x).toReal := by
        have hcast :
            (ξ : EReal) < (((f.asEReal x).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_gt
        exact_mod_cast hcast
      let t : ℝ := ((f.asEReal x).toReal - m)⁻¹
      have ht_pos : 0 < t := by
        have hden : 0 < (f.asEReal x).toReal - m := by
          dsimp [ξ, m] at hfx_real_gt
          linarith
        dsimp [t]
        exact inv_pos.mpr hden
      have ht_lt_one : t < 1 := by
        dsimp [t, ξ, m] at hfx_real_gt ⊢
        have : 1 < (f.asEReal x).toReal - m := by
          linarith
        simpa [one_div] using inv_lt_one_of_one_lt₀ this
      let z : H := t • x + (1 - t) • p
      have hz_level : z ∈ lowerLevelSet f.asEReal ξ := by
        rw [mem_lowerLevelSet_iff]
        have hconv :=
          hf.2.ineq hx_dom hp ht_pos ht_lt_one
        have hp_top : f.asEReal p ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
        have hp_bot : f.asEReal p ≠ ⊥ := ne_of_gt (f p).2
        have hrhs :
            (t : EReal) * f.asEReal x + (1 - t : EReal) * f.asEReal p =
              (((t * (f x : EReal).toReal + (1 - t) * m : ℝ)) : EReal) := by
          have hx_coe : f.asEReal x = ((((f x : EReal).toReal : ℝ)) : EReal) := by
            symm
            exact EReal.coe_toReal hfx_top hfx_bot
          have hp_coe : f.asEReal p = (m : EReal) := by
            simp [m, EReal.coe_toReal hp_top hp_bot]
          rw [hx_coe, hp_coe]
          rw [show (1 - t : EReal) = ((1 - t : ℝ) : EReal) by norm_num]
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        have hreal_rhs : t * (f x : EReal).toReal + (1 - t) * m = ξ := by
          have hden_ne : (f.asEReal x).toReal - m ≠ 0 := by
            dsimp [ξ, m] at hfx_real_gt
            linarith
          have hone : t * ((f x : EReal).toReal - m) = 1 := by
            dsimp [t]
            field_simp [hden_ne]
          dsimp [ξ, m]
          nlinarith
        calc
          f.asEReal z
              ≤ (t : EReal) * f.asEReal x + (1 - t : EReal) * f.asEReal p := hconv
          _ = (((t * (f x : EReal).toReal + (1 - t) * m : ℝ)) : EReal) := hrhs
          _ = (ξ : EReal) := by rw [hreal_rhs]
      have hz_ball : z ∈ Metric.ball p R := hR hz_level
      have hz_norm : ‖z - p‖ < R := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
      have hz_sub : z - p = t • (x - p) := by
        dsimp [z]
        module
      have ht_bound : t * ‖x - p‖ < R := by
        rw [hz_sub, norm_smul, Real.norm_of_nonneg ht_pos.le] at hz_norm
        exact hz_norm
      have hdist_real :
          (α : ℝ) * ‖x - p‖ + m ≤ (f.asEReal x).toReal := by
        have hdist_div :
            ‖x - p‖ / ((f.asEReal x).toReal - m) < R := by
          simpa [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht_bound
        have hdist_mul :
            ‖x - p‖ < R * ((f.asEReal x).toReal - m) := by
          have hden : 0 < (f.asEReal x).toReal - m := by
            dsimp [ξ, m] at hfx_real_gt
            linarith
          exact (div_lt_iff₀ hden).1 hdist_div
        have hscaled : (α : ℝ) * ‖x - p‖ < (f.asEReal x).toReal - m := by
          have hdiv : ‖x - p‖ / R < (f.asEReal x).toReal - m := by
            exact
              (div_lt_iff₀ hR_pos).2 <| by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hdist_mul
          simpa [α, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
        dsimp [m]
        linarith
      have hnorm_real : (α : ℝ) * ‖x‖ + β_out ≤ (f.asEReal x).toReal := by
        have htriangle : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm] using norm_add_le (x - p) p
        have hstep1 :
            (α : ℝ) * ‖x‖ + β_out ≤ (α : ℝ) * (‖x - p‖ + ‖p‖) + β_out := by
          exact add_le_add (mul_le_mul_of_nonneg_left htriangle α.2.le) le_rfl
        have hstep2 :
            (α : ℝ) * (‖x - p‖ + ‖p‖) + β_out = (α : ℝ) * ‖x - p‖ + m := by
          dsimp [β_out]
          ring
        calc
          (α : ℝ) * ‖x‖ + β_out ≤ (α : ℝ) * (‖x - p‖ + ‖p‖) + β_out := hstep1
          _ = (α : ℝ) * ‖x - p‖ + m := hstep2
          _ ≤ (f.asEReal x).toReal := hdist_real
      have hnorm_cast :
          (((((α : ℝ) * ‖x‖ + β_out : ℝ)) : EReal)) ≤ f.asEReal x := by
        have hcast : (((((α : ℝ) * ‖x‖ + β_out : ℝ)) : EReal)) ≤
            ((((f.asEReal x).toReal : ℝ) : EReal)) := by
          exact_mod_cast hnorm_real
        simpa [EReal.coe_toReal hfx_top hfx_bot] using hcast
      have hβ_min : min β_out β_in ≤ β_out := min_le_left _ _
      have hshift : (((((α : ℝ) * ‖x‖ + min β_out β_in : ℝ)) : EReal)) ≤
          (((((α : ℝ) * ‖x‖ + β_out : ℝ)) : EReal)) := by
        have hreal : (α : ℝ) * ‖x‖ + min β_out β_in ≤ (α : ℝ) * ‖x‖ + β_out := by
          nlinarith
        exact_mod_cast hreal
      exact le_trans hshift hnorm_cast

/-- Helper for Proposition 14 16: if `0` lies in the interior of the domain of the conjugate,
then the conjugate is bounded above on some closed ball around `0`. -/
private theorem exists_conjugate_closedBall_upperBound_of_zero_mem_interior_dom
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hzero : (0 : H) ∈ interior (dom f.asEReal∗)) :
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
      ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
        f.asEReal∗ u ≤ (γ : EReal) := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hzero_eff : (0 : H) ∈ interior (effectiveDomain (f∗[hf])) := by
    simpa [gammaZeroConjugate_apply, effectiveDomain, dom] using hzero
  rw [← continuous_points_eq_interior_effectiveDomain_of_mem_gammaZero (f∗[hf]) hfConj] at hzero_eff
  rcases hzero_eff with ⟨ρ, hρ, hball_dom, hcont⟩
  have hpre :
      (fun y : H ↦ (f∗[hf] y : EReal).toReal) ⁻¹' Metric.ball ((f∗[hf] 0 : EReal).toReal) 1 ∈
        nhds (0 : H) := by
    exact hcont.preimage_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hδball⟩
  let ε : Set.Ioi (0 : ℝ) := ⟨min (ρ / 2) (δ / 2), show 0 < min (ρ / 2) (δ / 2) by
    apply lt_min
    · linarith
    · positivity⟩
  refine ⟨ε, ((f∗[hf] 0 : EReal).toReal + 1), ?_⟩
  intro u hu
  have hu_ball_dom : u ∈ Metric.ball (0 : H) ρ := by
    have hu_norm : ‖u‖ ≤ (ε : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have hu_lt : ‖u‖ < ρ := by
      have hερ : (ε : ℝ) < ρ := by
        dsimp [ε]
        have : min (ρ / 2) (δ / 2) ≤ ρ / 2 := min_le_left _ _
        linarith
      exact lt_of_le_of_lt hu_norm hερ
    simpa [Metric.mem_ball, dist_eq_norm] using hu_lt
  have hu_eff : u ∈ effectiveDomain (f∗[hf]) := hball_dom hu_ball_dom
  have hu_ball_cont : u ∈ Metric.ball (0 : H) δ := by
    have hu_norm : ‖u‖ ≤ (ε : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have hu_lt : ‖u‖ < δ := by
      have hεδ : (ε : ℝ) < δ := by
        dsimp [ε]
        have : min (ρ / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
        have hhalf : δ / 2 < δ := by linarith
        exact lt_of_le_of_lt this hhalf
      exact lt_of_le_of_lt hu_norm hεδ
    simpa [Metric.mem_ball, dist_eq_norm] using hu_lt
  have hu_toReal_lt :
      (f∗[hf] u : EReal).toReal < (f∗[hf] 0 : EReal).toReal + 1 := by
    have hu_mem : u ∈
        (fun y : H ↦ (f∗[hf] y : EReal).toReal) ⁻¹' Metric.ball ((f∗[hf] 0 : EReal).toReal) 1 :=
      hδball hu_ball_cont
    have hu_abs :
        (f∗[hf] u : EReal).toReal < (f∗[hf] 0 : EReal).toReal + 1 := by
      have : -(1 : ℝ) < (f∗[hf] u : EReal).toReal - (f∗[hf] 0 : EReal).toReal ∧
          (f∗[hf] u : EReal).toReal - (f∗[hf] 0 : EReal).toReal < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_lt, sub_eq_add_neg] using hu_mem
      linarith
    exact hu_abs
  have hu_top : (f∗[hf] u : EReal) ≠ ⊤ := by
    exact ne_of_lt ((mem_effectiveDomain_iff).1 hu_eff)
  have hu_bot : (f∗[hf] u : EReal) ≠ ⊥ := by
    exact ne_of_gt (f∗[hf] u).2
  have hu_cast :
      (((f∗[hf] u : EReal).toReal : ℝ) : EReal) ≤
        ((((f∗[hf] 0 : EReal).toReal + 1 : ℝ)) : EReal) := by
    exact le_of_lt (by exact_mod_cast hu_toReal_lt)
  calc
    f.asEReal∗ u = (((f∗[hf] u : EReal).toReal : ℝ) : EReal) := by
      symm
      simpa [gammaZeroConjugate_apply] using EReal.coe_toReal hu_top hu_bot
    _ ≤ ((((f∗[hf] 0 : EReal).toReal + 1 : ℝ)) : EReal) := hu_cast
    _ = (((f∗[hf] 0 : EReal).toReal + 1 : ℝ) : EReal) := rfl

-- Proof sketch: use Proposition 11.12 for `(i) ↔ (ii)`. For `(ii) → (iii)`, argue by
-- contradiction: if the asymptotic quotient has nonpositive liminf, convexity lets one
-- interpolate a bounded lower-level sequence with norms tending to `+∞`. The implication
-- `(iii) → (i)` is immediate. Proposition 14.14 gives `(iii) ↔ (iv)` and the canonical
-- equivalence between affine lower bounds and boundedness of the Fenchel conjugate `f*` on
-- closed balls around `0`, while the standard local boundedness criterion for convex functions
-- identifies boundedness of `f*` on a neighborhood of `0` with `0 ∈ interior (dom f*)`.
/-- Proposition 14 16: for `f ∈ Γ₀(H)`, the following are equivalent: `f` is coercive; every real
lower level set of `f` is bounded; the asymptotic quotient `f(x) / ‖x‖` has strictly positive
liminf at infinity; `f` admits a global affine lower bound of the form `α ‖x‖ + β` with `α > 0`;
the Fenchel conjugate `f*` is bounded above on some closed ball around `0` (equivalently, on some
neighborhood of `0`); and `0` belongs to the interior of its domain. -/
theorem coercive_tfae_lowerLevelSet_asymptoticSlope_affineLowerBound_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    List.TFAE
      [Coercive f.asEReal,
        ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f.asEReal ξ),
        ((0 : ℝ) : EReal) <
          Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop),
        ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
          (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal,
        ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
          ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
            f.asEReal∗ u ≤ (γ : EReal),
        (0 : H) ∈ interior (dom f.asEReal∗)] := by
  let P1 : Prop := Coercive f.asEReal
  let P2 : Prop := ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f.asEReal ξ)
  let P3 : Prop :=
    ((0 : ℝ) : EReal) <
      Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)
  let P4 : Prop :=
    ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
      (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal
  let P5 : Prop :=
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
      ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
        f.asEReal∗ u ≤ (γ : EReal)
  let P6 : Prop := (0 : H) ∈ interior (dom f.asEReal∗)
  tfae_have 1 ↔ 2 := by
    exact coercive_iff_bounded_lowerLevelSet f.asEReal
  tfae_have 2 → 4 := by
    intro h2
    simpa [P2, P4] using exists_affine_lowerBound_of_bounded_lowerLevelSet f hf h2
  tfae_have 4 → 1 := by
    rintro ⟨α, β, hαβ⟩
    refine (coercive_iff_bounded_lowerLevelSet f.asEReal).2 ?_
    intro ξ
    refine (Metric.isBounded_iff_subset_closedBall (0 : H)).2 ?_
    refine ⟨max 0 ((ξ - β) / (α : ℝ)), ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [mem_lowerLevelSet_iff] at hx
    have hboundx :
        (((((α : ℝ) * ‖x‖ + β : ℝ)) : EReal)) ≤ f.asEReal x := by
      simpa [scaledNormKernelOfPos_apply, add_comm, add_left_comm, add_assoc] using hαβ x
    by_cases hξβ : ξ < β
    · have hfalse : False := by
        have hβle : (β : EReal) ≤ (ξ : EReal) := by
          have hβx :
              (β : EReal) ≤ (((((α : ℝ) * ‖x‖ + β : ℝ)) : EReal)) := by
            have hreal : β ≤ (α : ℝ) * ‖x‖ + β := by
              have : 0 ≤ (α : ℝ) * ‖x‖ := mul_nonneg α.2.le (norm_nonneg x)
              linarith
            exact_mod_cast hreal
          exact le_trans hβx (le_trans hboundx hx)
        exact not_lt_of_ge hβle (by exact_mod_cast hξβ)
      exact False.elim hfalse
    · have hξβ' : β ≤ ξ := le_of_not_gt hξβ
      have hreal : (α : ℝ) * ‖x‖ + β ≤ ξ := by
        exact_mod_cast (le_trans hboundx hx)
      have hnorm : ‖x‖ ≤ (ξ - β) / (α : ℝ) := by
        have hmul : (α : ℝ) * ‖x‖ ≤ ξ - β := by
          linarith
        exact (le_div_iff₀ α.2).2 <| by simpa [mul_comm] using hmul
      have hradius : ‖x‖ ≤ max 0 ((ξ - β) / (α : ℝ)) := le_trans hnorm (le_max_right _ _)
      have hdist : ‖x - 0‖ = ‖x‖ := by simp
      rw [hdist]
      exact hradius
  tfae_have 3 ↔ 4 := by
    constructor
    · intro h3
      obtain ⟨α, hα0, hαlt⟩ := EReal.exists_between_coe_real h3
      refine ⟨⟨α, by exact_mod_cast hα0⟩, ?_⟩
      rcases exists_affine_lowerBound_of_positive_liminf f hf α hαlt with ⟨β, hβ⟩
      exact ⟨β, by simpa [scaledNormKernelOfPos_apply, add_comm, add_left_comm, add_assoc] using hβ⟩
    · rintro ⟨α, β, hαβ⟩
      let y : ℝ := (α : ℝ) / 2
      have hy_lt : y < (α : ℝ) := by
        dsimp [y]
        exact half_lt_self α.2
      have hy_pos : 0 < y := by
        dsimp [y]
        exact half_pos α.2
      have hle :
          (y : EReal) ≤
            Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
              (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := by
        exact
          Filter.le_liminf_of_le (by isBoundedDefault)
            ((eventually_lt_div_norm_of_affine_lowerBound f α β hαβ hy_lt).mono fun _ hx ↦ hx.le)
      exact lt_of_lt_of_le (by exact_mod_cast hy_pos) hle
  tfae_have 4 ↔ 5 := by
    constructor
    · rintro ⟨α, β, hαβ⟩
      rcases
          (exists_affine_lowerBound_iff_conjugate_boundedAbove_on_closedBall f α).1
            ⟨β, hαβ⟩ with ⟨γ, hγ⟩
      exact ⟨α, γ, hγ⟩
    · rintro ⟨ε, γ, hγ⟩
      rcases
          (exists_affine_lowerBound_iff_conjugate_boundedAbove_on_closedBall f ε).2
            ⟨γ, hγ⟩ with ⟨β, hβ⟩
      exact ⟨ε, β, hβ⟩
  tfae_have 5 ↔ 6 := by
    constructor
    · rintro ⟨ε, γ, hγ⟩
      rw [mem_interior_iff_mem_nhds]
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) (half_pos ε.2)) ?_
      intro u hu
      rw [mem_dom_iff]
      have hu_closed : u ∈ Metric.closedBall (0 : H) (ε : ℝ) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [Metric.mem_ball, dist_eq_norm] at hu
        have hhalf_le : (ε : ℝ) / 2 ≤ (ε : ℝ) := half_le_self ε.2.le
        exact le_trans hu.le hhalf_le
      exact lt_of_le_of_lt (hγ u hu_closed) (EReal.coe_lt_top γ)
    · intro h6
      simpa [P5, P6] using exists_conjugate_closedBall_upperBound_of_zero_mem_interior_dom f hf h6
  tfae_finish

end Conjugation

end ERealFunction
