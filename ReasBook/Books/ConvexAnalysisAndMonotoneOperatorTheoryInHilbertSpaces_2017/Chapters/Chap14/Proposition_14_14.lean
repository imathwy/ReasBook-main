import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

variable [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2_real
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_normedSpace_l2_real
attribute [local instance] ERealFunction.prod_completeSpace_l2_real
attribute [local instance] ERealFunction.prod_innerProductSpace_l2_real

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 14: a real-height epigraph point has finite base value. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal))) :
    x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

/-- Helper for Proposition 14 14: the epigraph projection inequality yields an affine minorant on
the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain f,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
      hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    have hp_mem :=
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
    rw [← hproj] at hp_mem
    exact hp_mem
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f p : EReal) > ⊥ from (f p).2)
  have hfp_le_pi : (f p : EReal).toReal ≤ π := by
    have hfp_le_pi' : (f p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((f p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hfp_top hfp_bot] using hfp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simp only [real_inner_self_nonneg]
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hfx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar :
      ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤ ((f y : EReal).toReal - π) * (π - ξ) := by
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤ (f y : EReal).toReal - π := by
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (f y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
    linarith
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f y : EReal) > ⊥ from (f y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hfy_top hfy_bot] using hcast

/-- Helper for Proposition 14 14: every `Γ₀(H)` function admits a global affine minorant. -/
private theorem exists_affine_minorant_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    have hp_mem :=
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
    rw [← hproj] at hp_mem
    exact hp_mem
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  refine ⟨p, hp, ((π - ξ)⁻¹) • (x - p), ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · exact affine_minorant_on_effectiveDomain_of_projection hf hx hξ hproj y hy
  · rw [show (f y : EReal) = ⊤ by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))]
    exact le_top

/-- Helper for Proposition 14 14: every `Γ₀(H)` function has Fenchel conjugate with nonempty
domain. -/
private theorem dom_conjugate_nonempty_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (dom f.asEReal∗).Nonempty := by
  rcases exists_affine_minorant_of_mem_gammaZero f hf with ⟨p, hp, u, hminorant⟩
  have hu_minor : HasContinuousAffineMinorantWithSlope f.asEReal u := by
    refine ⟨(f p : EReal).toReal - ⟪p, u⟫_ℝ, ?_⟩
    intro y
    have hrearr :
        ⟪y - p, u⟫_ℝ + (f p : EReal).toReal =
          ⟪y, u⟫_ℝ + ((f p : EReal).toReal - ⟪p, u⟫_ℝ) := by
      rw [inner_sub_left]
      ring
    simpa [HasContinuousAffineMinorantWithSlope, hrearr] using hminorant y
  exact ⟨u, (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f.asEReal u).2 hu_minor⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 14: a strict liminf lower bound along `‖x‖ → +∞` yields a radius
outside which `f x` dominates `α ‖x‖`. -/
private theorem eventually_mul_lower_bound_of_lt_liminf_div_norm
    (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ)
    (hliminf :
      (α : EReal) <
        Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)) :
    ∃ R : ℝ,
      ∀ x : H, R ≤ ‖x‖ → (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
  -- Convert the strict liminf inequality into an eventual quotient bound.
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
  -- Multiply the quotient estimate by the positive norm.
  exact le_of_lt <| (EReal.lt_div_iff hnorm_pos (by simp)).1 hquotx

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 14: an affine lower bound of slope `α` forces the quotient
`f x / ‖x‖` to stay above every smaller real level eventually. -/
private theorem eventually_lt_div_norm_of_affine_norm_lowerBound
    (f : H → Set.Ioi (⊥ : EReal)) (α : NNReal) (β : ℝ)
    (hbound :
      (scaledNormKernel α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal)
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
    simpa [scaledNormKernel_apply, add_comm, add_left_comm, add_assoc] using hbound x
  have hδpos : 0 < (α : ℝ) - y := sub_pos.mpr hy
  have hβlt : |β| < ((α : ℝ) - y) * ‖x‖ := by
    have hxR : |β| / ((α : ℝ) - y) + 1 ≤ ‖x‖ := le_trans (le_max_right _ _) hx
    have hβdivlt : |β| / ((α : ℝ) - y) < ‖x‖ := by
      linarith
    simpa [mul_comm] using (div_lt_iff₀ hδpos).mp hβdivlt
  have hβlower : -((α : ℝ) - y) * ‖x‖ < β := by
    have hnegabs : -|β| ≤ β := by
      exact neg_abs_le β
    nlinarith
  have hylt :
      y * ‖x‖ < (α : ℝ) * ‖x‖ + β := by
    nlinarith
  have hprod :
      (y : EReal) * ‖x‖ < f.asEReal x := by
    exact lt_of_lt_of_le (by exact_mod_cast hylt) hboundx
  -- Divide by the positive norm to recover the quotient lower bound.
  exact (EReal.lt_div_iff hnorm_pos (by simp)).2 hprod

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 14: a real lower bound on a closed ball upgrades to an
affine-norm lower bound there after decreasing the intercept by `|α| R`. -/
private theorem affine_lower_bound_on_closedBall_of_real_lowerBound
    (f : H → Set.Ioi (⊥ : EReal)) (α m R : ℝ)
    (hm : ∀ x ∈ closedBall (0 : H) R, (m : EReal) ≤ f.asEReal x) :
    ∀ x ∈ closedBall (0 : H) R,
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
  have hbeta : min 0 (m - |α| * R) ≤ m - |α| * R := min_le_right _ _
  -- Bound the affine term by the constant lower bound `m` on the ball.
  have hreal : α * ‖x‖ + min 0 (m - |α| * R) ≤ m := by
    nlinarith
  have hereal :
      (((α * ‖x‖ + min 0 (m - |α| * R) : ℝ) : EReal)) ≤ (m : EReal) := by
    exact_mod_cast hreal
  exact le_trans hereal (hm x hx)

-- Proof sketch: the strict liminf inequality at infinity yields a radius beyond which
-- `f x / ‖x‖` stays above `α`, hence `f x ≥ α ‖x‖` outside a large ball. On the complementary
-- closed ball, properness of a `Γ₀(H)` function gives a finite real lower bound, which can be
-- absorbed into a global affine-norm minorant.
/-- Proposition 14 14 (1): if `f ∈ Γ₀(H)` and the liminf of `f(x) / ‖x‖` at infinity is strictly
larger than `α`, then `f` admits a global affine lower bound of slope `α`. -/
theorem exists_affine_norm_lowerBound_of_liminf_div_norm_gt
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (α : ℝ)
    (hliminf :
      (α : EReal) <
        Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)) :
    ∃ β : ℝ,
      (fun x : H ↦ ((α * ‖x‖ + β : ℝ) : EReal)) ≤ f.asEReal := by
  -- Route correction: merge the same-slope outside-ball estimate with a bounded closed-ball
  -- lower bound coming from nonempty conjugate domain, instead of introducing a larger slope.
  rcases eventually_mul_lower_bound_of_lt_liminf_div_norm f α hliminf with ⟨R0, hR0⟩
  let R : ℝ := max R0 0
  have houtside :
      ∀ x : H, R ≤ ‖x‖ → (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
    intro x hx
    exact hR0 x (le_trans (le_max_left _ _) hx)
  have hdom : (dom f.asEReal∗).Nonempty :=
    dom_conjugate_nonempty_of_mem_gammaZero (H := H) f hf
  have hball_bounded : Bornology.IsBounded (closedBall (0 : H) R) :=
    Metric.isBounded_closedBall
  rcases exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
      f.asEReal hdom (closedBall (0 : H) R) hball_bounded with ⟨m, hm⟩
  refine ⟨min 0 (m - |α| * R), ?_⟩
  intro x
  by_cases hxnorm : ‖x‖ ≤ R
  · -- On the exceptional closed ball, absorb the slope term into the constant lower bound.
    have hxball : x ∈ closedBall (0 : H) R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxnorm
    exact affine_lower_bound_on_closedBall_of_real_lowerBound (H := H) f α m R hm x hxball
  · -- Outside the ball, the chosen intercept is nonpositive, so the tail estimate still applies.
    have hRle : R ≤ ‖x‖ := le_of_not_ge hxnorm
    have htail : (((α * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := houtside x hRle
    have hbeta_nonpos : min 0 (m - |α| * R) ≤ 0 := min_le_left _ _
    have hreal : α * ‖x‖ + min 0 (m - |α| * R) ≤ α * ‖x‖ := by
      nlinarith
    have hshift :
        (((α * ‖x‖ + min 0 (m - |α| * R) : ℝ) : EReal)) ≤
          (((α * ‖x‖ : ℝ) : EReal)) := by
      exact_mod_cast hreal
    exact le_trans hshift htail

end

-- Proof sketch: Corollary 13.39 turns the global lower bound
-- `α ‖·‖ + β ≤ f` into the upper bound
-- `f∗ ≤ (fun x : H ↦ ((α * ‖x‖ + β : ℝ) : EReal))∗` by the order-reversing property of
-- Fenchel conjugation. Proposition 13.23 computes the conjugate effect of the additive constant,
-- and Example 13.3(v) identifies the conjugate of `x ↦ α ‖x‖` with the indicator of the closed
-- ball of radius `α`. This is exactly boundedness of `f*` on that ball.
/-- Proposition 14 14 (2): for `0 ≤ α`, a global affine lower bound of slope `α` is equivalent to
the Fenchel conjugate `f*` being bounded above on the closed ball `B(0; α)`. -/
theorem exists_affine_norm_lowerBound_iff_conjugate_boundedAbove_on_closedBall
    (f : H → Set.Ioi (⊥ : EReal)) (α : NNReal) :
    (∃ β : ℝ,
      (scaledNormKernel α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal) ↔
      ∃ γ : ℝ,
        ∀ u ∈ closedBall (0 : H) (α : ℝ), f.asEReal∗ u ≤ (γ : EReal) := by
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
        simpa [scaledNormKernel_apply, add_comm, add_left_comm, add_assoc] using hβ x
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
    · have h0epi : ((0 : H), γ) ∈ epigraph f.asEReal∗ := by
        rw [mem_epigraph_iff]
        simpa using hγ 0 (by simp)
      have h0minor := (mem_epigraph_conjugate_iff f.asEReal (0 : H) γ).1 h0epi (0 : H)
      simpa [hx, scaledNormKernel_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        h0minor
    · let u : H := ((α : ℝ) / ‖x‖) • x
      have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu_mem : u ∈ closedBall (0 : H) (α : ℝ) := by
        have hu_norm : ‖u‖ = (α : ℝ) := by
          calc
            ‖u‖ = ‖((α : ℝ) / ‖x‖)‖ * ‖x‖ := by
              simpa [u] using (norm_smul (((α : ℝ) / ‖x‖)) x)
            _ = (((α : ℝ) / ‖x‖) : ℝ) * ‖x‖ := by
              rw [Real.norm_of_nonneg]
              positivity
            _ = (α : ℝ) := by
              simp [div_eq_mul_inv, hxnorm_pos.ne']
        rw [Metric.mem_closedBall, dist_eq_norm]
        simp [hu_norm]
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
      simpa [scaledNormKernel_apply, hux, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hux_minor

-- Proof sketch: first convert the closed-ball boundedness of `f*` into the affine lower bound of
-- slope `α` by part (2). Dividing that pointwise estimate by `‖x‖` gives
-- `f x / ‖x‖ ≥ α + β / ‖x‖`, and the correction term tends to `0` along `‖x‖ → +∞`, so the
-- liminf is at least `α`.
/-- Proposition 14 14 (3): if `0 ≤ α` and the Fenchel conjugate `f*` is bounded
above on the closed ball `B(0; α)`, then the liminf of `f(x) / ‖x‖` at infinity is at least `α`. -/
theorem le_liminf_div_norm_of_conjugate_boundedAbove_on_closedBall
    (f : H → Set.Ioi (⊥ : EReal)) (α : NNReal)
    (hbounded :
      ∃ γ : ℝ,
        ∀ u ∈ closedBall (0 : H) (α : ℝ), f.asEReal∗ u ≤ (γ : EReal)) :
    ((α : ℝ) : EReal) ≤
      Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := by
  rcases
      (exists_affine_norm_lowerBound_iff_conjugate_boundedAbove_on_closedBall (H := H) f α).2
        hbounded with ⟨β, hβ⟩
  -- Every real level below `α` is eventually below the quotient, so it lies below the liminf.
  let L : EReal :=
    Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)
  have hbelow : ∀ y : ℝ, y < (α : ℝ) → (y : EReal) ≤ L := by
    intro y hy
    exact
      Filter.le_liminf_of_le (by isBoundedDefault)
        ((eventually_lt_div_norm_of_affine_norm_lowerBound (H := H) f α β hβ hy).mono
          fun _ hx ↦ hx.le)
  by_contra hα
  have hlt : L < ((α : ℝ) : EReal) := lt_of_not_ge hα
  rcases exists_between hlt with ⟨z, hLz, hzα⟩
  have hz_top : z ≠ ⊤ := ne_of_lt (lt_trans hzα (EReal.coe_lt_top _))
  have hz_bot : z ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hLz)
  let r : ℝ := z.toReal
  have hzcoe : ((r : ℝ) : EReal) = z := by
    dsimp [r]
    exact EReal.coe_toReal hz_top hz_bot
  have hrα : r < (α : ℝ) := by
    have hrα' : ((r : ℝ) : EReal) < ((α : ℝ) : EReal) := by
      simpa [hzcoe] using hzα
    exact_mod_cast hrα'
  have hrle : (r : EReal) ≤ L := hbelow r hrα
  exact not_le_of_gt hLz (hzcoe ▸ hrle)

end Conjugation

end ERealFunction
