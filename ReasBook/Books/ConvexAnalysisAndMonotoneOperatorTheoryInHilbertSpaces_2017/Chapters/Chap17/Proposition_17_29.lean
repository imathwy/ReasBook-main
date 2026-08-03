import Mathlib
import BauschkeLean.Chap01.Text_1_0_6
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module ℝ H] [ContinuousSMul ℝ H]

/-- Helper for Proposition 17 29: restricting lower semicontinuity to an affine segment gives a
lower-semicontinuous scalar trace on `[0,1]`. -/
private lemma lowerSemicontinuousOn_lineMap_segment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1)) :
    LowerSemicontinuousOn
      (fun t : ℝ ↦ f.asEReal (AffineMap.lineMap x0 x1 t))
      (Set.Icc (0 : ℝ) 1) := by
  -- Compose the segment lower-semicontinuity with the affine parameterization of `[x0,x1]`.
  refine hlsc.comp AffineMap.lineMap_continuous.continuousOn ?_
  intro t ht
  rw [segment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: shifting the scalar parameter on `lineMap` translates into
moving along the segment direction `x1 - x0`. -/
private lemma lineMap_add_eq_lineMap_add_smul
    (x0 x1 : H) (t α : ℝ) :
    AffineMap.lineMap x0 x1 (t + α) =
      AffineMap.lineMap x0 x1 t + α • (x1 - x0) := by
  -- Expand both affine combinations and regroup the common `t` and `α` terms.
  simp [AffineMap.lineMap_apply_module', add_smul, add_assoc, add_comm]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: a directional derivative of `f` along the segment direction
becomes a right derivative of the scalar trace `t ↦ f (lineMap x0 x1 t)`. -/
private lemma hasRightDerivativeAt_lineMap_of_hasDirectionalDerivativeAt
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H} {t : ℝ} {ξ : EReal}
    (hξ : HasDirectionalDerivativeAt f (AffineMap.lineMap x0 x1 t) (x1 - x0) ξ) :
    HasRightDerivativeAt
      (fun s : ℝ ↦ f (AffineMap.lineMap x0 x1 s))
      t ξ := by
  refine ⟨hξ.1, ?_⟩
  -- Rewrite the one-dimensional quotient into the given directional-difference quotient.
  refine Filter.Tendsto.congr' ?_ hξ.2
  apply eventuallyEq_nhdsWithin_of_eqOn
  intro α hα
  simp [lineMap_add_eq_lineMap_add_smul, smul_eq_mul]

/-- Helper for Proposition 17 29: a strict endpoint gap admits a positive linear tilt that still
leaves the right endpoint strictly above the left. -/
private lemma exists_positive_tilt_of_lt_endpoint_values
    {a b : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) (hb_bot : b ≠ ⊥) (hab : a < b) :
    ∃ r : ℝ, 0 < r ∧ a + (r : EReal) < b := by
  by_cases hb_top : b = ⊤
  · refine ⟨1, zero_lt_one, ?_⟩
    have ha_coe : a = (((a.toReal : ℝ)) : EReal) := by
      rw [EReal.coe_toReal ha_top ha_bot]
    rw [ha_coe, hb_top]
    simpa [EReal.coe_add] using EReal.coe_lt_top (a.toReal + 1)
  -- In the finite branch, choose half of the positive real gap between the endpoint values.
  have hab_real :
      a.toReal < b.toReal := by
    have hab_coe : (((a.toReal : ℝ) : EReal)) < (((b.toReal : ℝ) : EReal)) := by
      simpa [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot] using hab
    exact EReal.coe_lt_coe_iff.mp hab_coe
  refine ⟨(b.toReal - a.toReal) / 2, half_pos (sub_pos.mpr hab_real), ?_⟩
  have hsum :
      (((a.toReal + (b.toReal - a.toReal) / 2 : ℝ) : EReal)) <
        (((b.toReal : ℝ) : EReal)) := by
    exact EReal.coe_lt_coe_iff.mpr <| by linarith
  simpa [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot, EReal.coe_add,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hsum

omit [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [Module ℝ H]
  [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: a minimizer of the tilted trace cannot occur at the right
endpoint when the right endpoint value is strictly larger than the left endpoint value. -/
private lemma tilted_minimizer_not_right_endpoint
    {h : ℝ → EReal} {t : ℝ} {a b : EReal}
    (htmin : IsMinOn h (Set.Icc (0 : ℝ) 1) t)
    (h0 : h 0 = a) (h1 : h 1 = b) (hab : ¬ b ≤ a) :
    t ≠ 1 := by
  intro ht1
  have htmin' : ∀ x ∈ Set.Icc (0 : ℝ) 1, h t ≤ h x := isMinOn_iff.mp htmin
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- Compare the minimizing value with the left endpoint of the interval.
  have hmin0 : h t ≤ h 0 := htmin' 0 hzero_mem
  have h1_le_h0 : h 1 ≤ h 0 := by
    simpa [ht1] using hmin0
  rw [h0, h1] at h1_le_h0
  exact hab h1_le_h0

/-- Helper for Proposition 17 29: minimizing the tilted trace gives the additive secant lower
bound after shifting both sides by the same finite affine correction. -/
private lemma secant_additive_lower_bound_of_tilted_minimum
    (g : ℝ → Set.Ioi (⊥ : EReal)) {r t α : ℝ}
    (htmin : IsMinOn
      (fun s : ℝ ↦ g.asEReal s + (((r * (1 - s) : ℝ)) : EReal))
      (Set.Icc (0 : ℝ) 1) t)
    (htα : t + α ∈ Set.Icc (0 : ℝ) 1) :
    g.asEReal t + (((r * α : ℝ)) : EReal) ≤ g.asEReal (t + α) := by
  have htmin' :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        g.asEReal t + (((r * (1 - t) : ℝ)) : EReal) ≤
          g.asEReal x + (((r * (1 - x) : ℝ)) : EReal) := isMinOn_iff.mp htmin
  have hminα :
      g.asEReal t + (((r * (1 - t) : ℝ)) : EReal) ≤
        g.asEReal (t + α) + (((r * (1 - (t + α)) : ℝ)) : EReal) := htmin' _ htα
  have hleft_real :
      r * (1 - t) + (r * t + r * α - r) = r * α := by
    ring
  have hright_real :
      r * (1 - (t + α)) + (r * t + r * α - r) = 0 := by
    ring
  -- Shift the minimizing inequality by the same finite amount and simplify both tilt terms.
  have hshift := add_le_add_left hminα ((((r * t + r * α - r : ℝ)) : EReal))
  have hsum_left :
      ((((r * t + r * α - r : ℝ)) : EReal)) + (((r * (1 - t) : ℝ)) : EReal) =
        (((r * α : ℝ)) : EReal) := by
    simpa [add_comm] using congrArg (fun s : ℝ ↦ (s : EReal)) hleft_real
  have hsum_right :
      ((((r * t + r * α - r : ℝ)) : EReal)) + (((r * (1 - (t + α)) : ℝ)) : EReal) =
        (0 : EReal) := by
    simpa [add_comm] using congrArg (fun s : ℝ ↦ (s : EReal)) hright_real
  have hshift' :
      g.asEReal t + ((((r * t + r * α - r : ℝ)) : EReal) + (((r * (1 - t) : ℝ)) : EReal)) ≤
        g.asEReal (t + α) +
          ((((r * t + r * α - r : ℝ)) : EReal) + (((r * (1 - (t + α)) : ℝ)) : EReal)) := by
    simpa [add_assoc, add_left_comm, add_comm] using hshift
  calc
    g.asEReal t + (((r * α : ℝ)) : EReal)
        = g.asEReal t + ((((r * t + r * α - r : ℝ)) : EReal) + (((r * (1 - t) : ℝ)) : EReal)) := by
            rw [hsum_left]
    _ ≤ g.asEReal (t + α) +
          ((((r * t + r * α - r : ℝ)) : EReal) + (((r * (1 - (t + α)) : ℝ)) : EReal)) := hshift'
    _ = g.asEReal (t + α) := by
          rw [hsum_right]
          simp

/-- Helper for Proposition 17 29: if every directional derivative on a segment is nonpositive,
the right endpoint cannot exceed the left endpoint. -/
private theorem apply_right_le_left_of_nonpos_directionalDerivativeOn_segment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0) :
    f.asEReal x1 ≤ f.asEReal x0 := by
  let g : ℝ → Set.Ioi (⊥ : EReal) := fun t ↦ f (AffineMap.lineMap x0 x1 t)
  have hg_lsc : LowerSemicontinuousOn g.asEReal (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the segment lower-semicontinuity to the scalar parameter interval.
    simpa [g] using lowerSemicontinuousOn_lineMap_segment f hlsc
  have hx0_seg : x0 ∈ closedOpenSegment x0 x1 := by
    -- The left endpoint corresponds to the parameter value `0`.
    refine mem_closedOpenSegment_iff.mpr ?_
    have hzero_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simp
    refine ⟨0, hzero_mem, ?_⟩
    simp
  obtain ⟨ξ0, hξ0, -⟩ := hderiv x0 hx0_seg
  have hx0_dom : x0 ∈ effectiveDomain f := hξ0.1
  have hfx0_top : f.asEReal x0 ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom)
  have hfx0_bot : f.asEReal x0 ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < f.asEReal x0 from (f x0).2)
  have hfx1_bot : f.asEReal x1 ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < f.asEReal x1 from (f x1).2)
  by_contra hle
  have hlt : f.asEReal x0 < f.asEReal x1 := lt_of_not_ge hle
  obtain ⟨r, hr_pos, hgap⟩ :=
    exists_positive_tilt_of_lt_endpoint_values hfx0_top hfx0_bot hfx1_bot hlt
  let h : ℝ → EReal := fun t ↦ g.asEReal t + (((r * (1 - t) : ℝ)) : EReal)
  have hlin_cont : Continuous (fun t : ℝ ↦ (((r * (1 - t) : ℝ)) : EReal)) := by
    -- The tilt is an ordinary real affine function, then coerced into `EReal`.
    have hreal_cont : Continuous (fun t : ℝ ↦ r * (1 - t)) := by
      continuity
    exact continuous_coe_real_ereal.comp hreal_cont
  have hh_lsc : LowerSemicontinuousOn h (Set.Icc (0 : ℝ) 1) := by
    -- Addition is continuous here because the tilt is always finite.
    refine hg_lsc.add' (hlin_cont.continuousOn.lowerSemicontinuousOn) ?_
    intro t ht
    have htilt_ne_bot : (((r * (1 - t) : ℝ)) : EReal) ≠ ⊥ := by
      simpa [EReal.coe_mul, EReal.coe_sub] using EReal.coe_ne_bot (r * (1 - t))
    have htilt_ne_top : (((r * (1 - t) : ℝ)) : EReal) ≠ ⊤ := by
      simpa [EReal.coe_mul, EReal.coe_sub] using EReal.coe_ne_top (r * (1 - t))
    exact EReal.continuousAt_add
      (Or.inr htilt_ne_bot)
      (Or.inr htilt_ne_top)
  obtain ⟨t, ht, htmin⟩ :=
    hh_lsc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) isCompact_Icc
  have h0 : h 0 = f.asEReal x0 + (r : EReal) := by
    -- Evaluate the tilted trace at the left endpoint.
    simp [h, g, AffineMap.lineMap_apply_zero]
  have h1 : h 1 = f.asEReal x1 := by
    -- The tilt vanishes at the right endpoint.
    have hmul_zero : ((r : EReal) * (1 - (1 : EReal))) = 0 := by
      have hzero : (1 - (1 : EReal)) = 0 := by
        exact EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      rw [hzero]
      simp
    simp [h, g, AffineMap.lineMap_apply_one, EReal.coe_mul, hmul_zero]
  have h_not_one : t ≠ 1 := by
    -- The positive tilt makes the right endpoint too large to be the minimizer.
    exact tilted_minimizer_not_right_endpoint htmin h0 h1 hgap.not_ge
  have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 h_not_one
  have ht_seg : AffineMap.lineMap x0 x1 t ∈ closedOpenSegment x0 x1 := by
    -- Parameters in `Ico 0 1` correspond exactly to the half-open segment.
    refine mem_closedOpenSegment_iff.mpr ?_
    exact ⟨t, ⟨ht.1, ht_lt_one⟩, rfl⟩
  obtain ⟨ξ, hξ, hξ_nonpos⟩ := hderiv _ ht_seg
  have hright : HasRightDerivativeAt g t ξ := by
    -- Transport the segment directional derivative to the scalar trace.
    simpa [g] using hasRightDerivativeAt_lineMap_of_hasDirectionalDerivativeAt f hξ
  let q : ℝ → EReal := fun α ↦ ((g (t + α) : EReal) - (g t : EReal)) / α
  have hq_tendsto : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ξ) := by
    -- Unfold the right derivative and rewrite `α • 1` as `α`.
    simpa [q, HasDirectionalDerivativeAt, one_smul] using hright.2
  have hq_lower :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((r : ℝ) : EReal) ≤ q α := by
    have hzero_lt_sub : (0 : ℝ) < 1 - t := by
      linarith
    have hα_small : Set.Iio (1 - t) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      exact mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hzero_lt_sub)
    have htmin_tilt : IsMinOn
        (fun s : ℝ ↦ g.asEReal s + (((r * (1 - s) : ℝ)) : EReal))
        (Set.Icc (0 : ℝ) 1) t := by
      simpa [h] using htmin
    filter_upwards [self_mem_nhdsWithin, hα_small] with α hα_pos hα_lt
    have hα0 : 0 < α := hα_pos
    have hα1 : α < 1 - t := hα_lt
    have htα : t + α ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2, hα0, hα1]
    have hstep :
        g.asEReal t + (((r * α : ℝ)) : EReal) ≤ g.asEReal (t + α) := by
      -- Use the standalone additive consequence of tilted minimality before dividing by `α`.
      exact secant_additive_lower_bound_of_tilted_minimum g htmin_tilt htα
    have hsub :
        (((r * α : ℝ)) : EReal) ≤ g.asEReal (t + α) - g.asEReal t := by
      -- Repackage the reordered inequality as a subtraction estimate.
      have hgt_bot : (⊥ : EReal) < g.asEReal t := (g t).2
      have hgt_ne_bot : g.asEReal t ≠ ⊥ := ne_of_gt hgt_bot
      have hgt_ne_top : g.asEReal t ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hright.1)
      have hstep_add :
          (((r * α : ℝ)) : EReal) + g.asEReal t ≤ g.asEReal (t + α) := by
        simpa [add_comm] using hstep
      exact (EReal.le_sub_iff_add_le
        (Or.inl hgt_ne_bot)
        (Or.inl hgt_ne_top)).2 hstep_add
    have hdiv :
        ((((r * α : ℝ)) : EReal) / α) ≤ q α := by
      have hα0_ereal : (0 : EReal) < α := by
        exact_mod_cast hα0
      exact (EReal.strictMono_div_right_of_pos hα0_ereal (EReal.coe_ne_top α)).monotone hsub
    have hcancel :
        (((r : EReal) * α) / α) = (r : EReal) := by
      have hα_ne_zero_ereal : (((α : ℝ) : EReal)) ≠ 0 := by
        exact_mod_cast hα0.ne'
      rw [EReal.div_eq_iff (EReal.coe_ne_bot α) (EReal.coe_ne_top α) hα_ne_zero_ereal]
    simpa [q, EReal.coe_mul, hcancel] using hdiv
  have hr_le_ξ : ((r : ℝ) : EReal) ≤ ξ := by
    -- Closedness of `Ici r` passes the eventual secant lower bound to the derivative limit.
    exact isClosed_Ici.mem_of_tendsto hq_tendsto hq_lower
  have hr_contra : ¬ ((r : ℝ) : EReal) ≤ ξ := by
    intro hr_le
    have hr_le_zero : ((r : ℝ) : EReal) ≤ (0 : EReal) := le_trans hr_le hξ_nonpos
    have hr_pos_ereal : (0 : EReal) < (r : EReal) := by
      exact_mod_cast hr_pos
    exact (not_le_of_gt hr_pos_ereal) hr_le_zero
  exact hr_contra hr_le_ξ

/-- Helper for Proposition 17 29: if a scalar trace strictly increases on a segment, some point
of the corresponding half-open segment has strictly positive directional derivative. -/
private theorem exists_positive_directional_derivative_on_half_open_segment
    (f : H → Set.Ioi (⊥ : EReal)) (x0 x1 : H)
    (hvalue : f.asEReal x0 < f.asEReal x1)
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ) :
    ∃ x ∈ closedOpenSegment x0 x1, ∃ ξ : EReal,
      HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ 0 < ξ := by
  by_contra hpositive
  have hnonpos :
      ∀ x ∈ closedOpenSegment x0 x1,
        ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0 := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := hderiv x hx
    refine ⟨ξ, hξ, ?_⟩
    by_contra hξ_pos
    exact hpositive ⟨x, hx, ξ, hξ, lt_of_not_ge hξ_pos⟩
  exact hvalue.not_ge <|
    apply_right_le_left_of_nonpos_directionalDerivativeOn_segment f hlsc hnonpos

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: convexity of the effective domain keeps the whole affine
parameter segment between two effective-domain points inside the effective domain. -/
private lemma lineMap_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom_convex : Convex ℝ (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ effectiveDomain f := by
  -- The source proof only needs the convexity of the effective domain along the chosen secant.
  exact hdom_convex.lineMap_mem hx hy ht

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: directional derivatives scale by a positive real factor in the
direction and in the derivative value. -/
private lemma has_directional_derivative_at_smul_pos
    {f : H → Set.Ioi (⊥ : EReal)} {x d : H} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x d ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c • d) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • d) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    -- Reparameterize the difference quotient by the positive scaling `α ↦ α * c`.
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hcoe_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top c
  have hcoe_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hmul :
      Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ξ * c)) := by
    -- Multiplying the reparameterized quotient by the same positive constant gives the new limit.
    exact EReal.Tendsto.mul_const hcomp (Or.inr hcoe_bot) (Or.inr hcoe_top)
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • (c • d)) : EReal) - (f x : EReal)) / α)
      (fun α ↦ q (α * c) * c) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hc0 : c ≠ 0 := hc.ne'
    have hcoeff : ((((α * c : ℝ) : EReal)⁻¹) * c) = ((α : EReal)⁻¹) := by
      rw [← EReal.coe_inv (α * c), ← EReal.coe_mul, ← EReal.coe_inv α]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        calc
          (α * c)⁻¹ * c = c / (α * c) := by rw [div_eq_mul_inv, mul_comm]
          _ = α⁻¹ := by simpa [mul_comm] using (div_mul_cancel_left₀ hc0 α)
    -- Rewrite the scaled direction quotient into the reparameterized original quotient.
    calc
      ((f (x + α • (c • d)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) • d) : EReal) - (f x : EReal)) / α) := by
              simp [smul_smul, mul_comm]
      _ = ((f (x + (α * c) • d) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) • d) : EReal) - (f x : EReal)) *
            ((((α * c : ℝ) : EReal)⁻¹) * c) := by
              rw [hcoeff]
      _ = ((((f (x + (α * c) • d) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
            rw [div_eq_mul_inv]
            exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by
            simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: a directional derivative value is unique once the basepoint and
direction are fixed. -/
private lemma directional_derivative_value_unique
    {f : H → Set.Ioi (⊥ : EReal)} {x d : H} {ξ η : EReal}
    (hξ : HasDirectionalDerivativeAt f x d ξ)
    (hη : HasDirectionalDerivativeAt f x d η) :
    ξ = η := by
  -- Both derivative values are limits of the same difference-quotient map, so the limit is unique.
  exact tendsto_nhds_unique hξ.2 hη.2

/-- Helper for Proposition 17 29: the source-faithful secant parameterization with
`secantLine x y 0 = y` and `secantLine x y 1 = x`. -/
private def secantLine (x y : H) : ℝ → H :=
  AffineMap.lineMap y x

/-- Helper for Proposition 17 29: the secant gap between `f` and the affine chord joining the
endpoint values `f y` and `f x` along `secantLine x y`. -/
private noncomputable def secantGap
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) : ℝ → EReal :=
  fun t ↦
    (f (secantLine x y t) : EReal) -
      (((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal : ℝ) : EReal)

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: subtracting two points on the same secant line factors through
the common chord direction. -/
private lemma lineMap_sub_lineMap_eq_smul_sub
    (x y : H) (s t : ℝ) :
    secantLine x y s - secantLine x y t = (s - t) • (x - y) := by
  -- Expand both affine-segment points around the same base point and collect the coefficients.
  rw [secantLine, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  have hmain : s • (x - y) + y - (t • (x - y) + y) = (s - t) • (x - y) := by
    calc
      s • (x - y) + y - (t • (x - y) + y) = s • (x - y) - t • (x - y) := by
        abel_nf
      _ = (s - t) • (x - y) := by
        simpa [sub_eq_add_neg] using (sub_smul s t (x - y)).symm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: shifting the secant parameter by `α * c` is the same as moving
from the current secant point along the chord direction by `α • (c • (x - y))`. -/
private lemma secantLine_add_mul_eq_add_smul
    (x y : H) (t α c : ℝ) :
    secantLine x y (t + α * c) = secantLine x y t + α • (c • (x - y)) := by
  -- Expand the affine parametrization at the two scalar parameters and regroup the coefficients.
  rw [secantLine, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  rw [add_smul, smul_smul]
  abel_nf

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: convexity of the effective domain keeps every scalar point of
the source secant inside the effective domain. -/
private lemma secantLine_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom_convex : Convex ℝ (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    secantLine x y t ∈ effectiveDomain f := by
  -- Reuse convexity on the affine parameter interval after matching the chosen orientation.
  simpa [secantLine] using lineMap_mem_effectiveDomain hdom_convex hy hx ht

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: the secant gap vanishes at the left endpoint of the source
segment because the affine correction equals `f y` there. -/
private lemma secant_gap_apply_zero
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hy : y ∈ effectiveDomain f) :
    secantGap f x y 0 = 0 := by
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  -- Rewrite the affine correction at `0` to the finite endpoint value `f y`.
  rw [secantGap, secantLine, AffineMap.lineMap_apply_zero]
  rw [show ((((1 - (0 : ℝ)) * (f y : EReal).toReal + (0 : ℝ) * (f x : EReal).toReal : ℝ) :
      EReal)) = (f y : EReal) by
      simp [EReal.coe_toReal hy_top hy_bot]]
  exact EReal.sub_self hy_top hy_bot

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: the secant gap vanishes at the right endpoint of the source
segment because the affine correction equals `f x` there. -/
private lemma secant_gap_apply_one
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) :
    secantGap f x y 1 = 0 := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  -- Rewrite the affine correction at `1` to the finite endpoint value `f x`.
  rw [secantGap, secantLine, AffineMap.lineMap_apply_one]
  rw [show ((((1 - (1 : ℝ)) * (f y : EReal).toReal + (1 : ℝ) * (f x : EReal).toReal : ℝ) :
      EReal)) = (f x : EReal) by
      simp [EReal.coe_toReal hx_top hx_bot]]
  exact EReal.sub_self hx_top hx_bot

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: a strict Jensen violation becomes a positive interior value of
the secant gap on the source scalar segment. -/
private lemma secant_gap_pos_of_strict_jensen
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ}
    (hstrict :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) <
        (f (α • x + (1 - α) • y) : EReal)) :
    0 < secantGap f x y α := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hchord :
      ((((1 - α) * (f y : EReal).toReal + α * (f x : EReal).toReal : ℝ) : EReal)) =
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
    have hy_coe : (((f y : EReal).toReal : ℝ) : EReal) = (f y : EReal) := by
      rw [EReal.coe_toReal hy_top hy_bot]
    have hx_coe : (((f x : EReal).toReal : ℝ) : EReal) = (f x : EReal) := by
      rw [EReal.coe_toReal hx_top hx_bot]
    -- Convert the affine real interpolation back to `EReal` using finiteness of the endpoints.
    calc
      ((((1 - α) * (f y : EReal).toReal + α * (f x : EReal).toReal : ℝ) : EReal))
          = ((((1 - α) * (f y : EReal).toReal : ℝ) : EReal)) +
              (((α * (f x : EReal).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_add]
      _ = (((1 - α : ℝ) : EReal) * (f y : EReal)) + (α : EReal) * (f x : EReal) := by
            simp [hy_coe, hx_coe, EReal.coe_mul]
      _ = (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := by
            rw [add_comm]
      _ = (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
            rw [show (((1 - α : ℝ) : EReal)) = (1 - α : EReal) by
              rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]]
  -- The secant gap is positive exactly when the affine chord lies strictly below the function.
  rw [secantGap]
  refine EReal.sub_pos.mpr ?_
  calc
    ((((1 - α) * (f y : EReal).toReal + α * (f x : EReal).toReal : ℝ) : EReal))
        = (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := hchord
    _ < (f (α • x + (1 - α) • y) : EReal) := hstrict
    _ = (f (secantLine x y α) : EReal) := by
          simp [secantLine, AffineMap.lineMap_apply_module, add_comm]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: the secant gap is proper as an `EReal`-valued function, so it
can be repackaged by `properIoi` for the one-dimensional contradiction argument. -/
private lemma secant_gap_is_proper
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (_hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    IsProper (secantGap f x y) := by
  refine ⟨?_, ?_⟩
  · intro t
    -- Subtracting a finite affine correction cannot create the forbidden value `⊥`.
    rw [secantGap, sub_eq_add_neg, EReal.add_ne_bot_iff]
    constructor
    · exact ne_of_gt (show (⊥ : EReal) < (f (secantLine x y t) : EReal) from (f _).2)
    · intro htop
      have hfinite :
          ((((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal : ℝ)) : EReal) ≠ ⊤ :=
        EReal.coe_ne_top _
      apply hfinite
      simpa [EReal.coe_add, EReal.coe_mul] using htop
  · -- The left endpoint gives an explicit finite point in the domain of the secant gap.
    refine ⟨0, ?_⟩
    simp [dom, secant_gap_apply_zero hy]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: whenever both endpoint values of a directional quotient are
finite, the quotient is the coercion of the corresponding real quotient. -/
private lemma directional_quotient_eq_coe_toReal
    {f : H → Set.Ioi (⊥ : EReal)} {x d : H} {α : ℝ}
    (hx : x ∈ effectiveDomain f) (_hα : 0 < α) (hαdom : x + α • d ∈ effectiveDomain f) :
    ((f (x + α • d) : EReal) - (f x : EReal)) / α =
      ((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  -- Rewrite both finite `EReal` values through `toReal`, then the quotient is purely real.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • d) : EReal) from (f (x + α • d)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: on the scalar interval `[0,1]`, the secant gap is just the
coercion of the real-valued gap between the finite trace and the affine chord. -/
private lemma secantGap_eq_coe_toReal_sub_chord
    {f : H → Set.Ioi (⊥ : EReal)} (hdom_convex : Convex ℝ (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    secantGap f x y t =
      ((((f (secantLine x y t) : EReal).toReal -
          ((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal)) : ℝ) : EReal) := by
  -- On the secant segment all involved values are finite, so the gap is a real subtraction.
  have hsecant : secantLine x y t ∈ effectiveDomain f :=
    secantLine_mem_effectiveDomain hdom_convex hx hy ht
  have hsecant_top : (f (secantLine x y t) : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hsecant)
  have hsecant_bot : (f (secantLine x y t) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (secantLine x y t) : EReal) from (f _).2)
  rw [secantGap, ← EReal.coe_toReal hsecant_top hsecant_bot, ← EReal.coe_sub]
  simp

/-- Helper for Proposition 17 29: restricting `hlsc` along the source secant gives a lower
semicontinuous scalar trace on `[0,1]`. -/
private lemma lower_semicontinuous_on_secantLine_trace
    (f : H → Set.Ioi (⊥ : EReal)) (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    LowerSemicontinuousOn
      (fun t : ℝ ↦ f.asEReal (secantLine x y t))
      (Set.Icc (0 : ℝ) 1) := by
  -- Compose the ambient lower-semicontinuity with the affine secant parametrization.
  refine hlsc.comp AffineMap.lineMap_continuous.continuousOn ?_
  intro t ht
  rw [secantLine]
  exact lineMap_mem_effectiveDomain hdom_convex hy hx ht

/-- Helper for Proposition 17 29: the packaged secant gap is lower semicontinuous on `[0,1]`. -/
private lemma lower_semicontinuous_on_secant_gap_segment
    (f : H → Set.Ioi (⊥ : EReal)) (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    LowerSemicontinuousOn (secantGap f x y) (Set.Icc (0 : ℝ) 1) := by
  have htrace :
      LowerSemicontinuousOn
        (fun t : ℝ ↦ f.asEReal (secantLine x y t))
        (Set.Icc (0 : ℝ) 1) :=
    lower_semicontinuous_on_secantLine_trace f hdom_convex hlsc hx hy
  have hcorr_cont :
      Continuous (fun t : ℝ ↦
        -((((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal : ℝ) : EReal))) := by
    -- The affine chord term is an ordinary real affine map, then coerced into `EReal`.
    exact (continuous_coe_real_ereal.comp (by continuity)).neg
  -- Add the finite affine correction pointwise to the secant trace.
  refine htrace.add' (hcorr_cont.continuousOn.lowerSemicontinuousOn) ?_
  intro t ht
  have hsecant : secantLine x y t ∈ effectiveDomain f :=
    secantLine_mem_effectiveDomain hdom_convex hx hy ht
  have hsecant_top : (f (secantLine x y t) : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hsecant)
  have hsecant_bot : (f (secantLine x y t) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (secantLine x y t) : EReal) from (f _).2)
  exact EReal.continuousAt_add (Or.inl hsecant_top) (Or.inl hsecant_bot)

/-- Helper for Proposition 17 29: a point of `[0,α[` is exactly a scalar `s` with `0 ≤ s < α`. -/
private lemma mem_closedOpenSegment_zero_alpha
    {α s : ℝ} (hα0 : 0 < α) (hs : s ∈ closedOpenSegment (0 : ℝ) α) :
    s ∈ Set.Ico (0 : ℝ) α := by
  rcases mem_closedOpenSegment_iff.mp hs with ⟨u, hu, rfl⟩
  constructor
  · have : 0 ≤ u * α := mul_nonneg hu.1 hα0.le
    simpa [AffineMap.lineMap_apply_module, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      this
  · have : u * α < α := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hu.2 hα0
    simpa [AffineMap.lineMap_apply_module, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      this

/-- Helper for Proposition 17 29: a point of `[1,α[` with `α < 1` lies strictly above `α` and at
most `1`. -/
private lemma mem_closedOpenSegment_one_alpha
    {α t : ℝ} (hα1 : α < 1) (ht : t ∈ closedOpenSegment (1 : ℝ) α) :
    t ∈ Set.Ioc α 1 := by
  rcases mem_closedOpenSegment_iff.mp ht with ⟨u, hu, rfl⟩
  constructor
  · -- Expand the affine parameterization and measure the gap above `α`.
    have hgap : 0 < (1 - u) * (1 - α) := by
      exact mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr hα1)
    have hrepr :
        AffineMap.lineMap (1 : ℝ) α u - α = (1 - u) * (1 - α) := by
      simp [AffineMap.lineMap_apply_module, smul_eq_mul]
      ring
    linarith
  · -- The same expansion shows that the point never exceeds the right endpoint `1`.
    have hnonpos : u * (α - 1) ≤ 0 := by
      nlinarith [hu.1, hα1.le]
    have hrepr :
        AffineMap.lineMap (1 : ℝ) α u - 1 = u * (α - 1) := by
      simp [AffineMap.lineMap_apply_module, smul_eq_mul]
      ring
    linarith

/-- Helper for Proposition 17 29: positive rescaling inside the interval keeps the scalar path of
the left half-open secant segment inside `[0,1]`. -/
private lemma eventually_mem_Icc_of_closedOpenSegment_zero_alpha
    {α s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hs : s ∈ closedOpenSegment (0 : ℝ) α) :
    ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0), s + β * α ∈ Set.Icc (0 : ℝ) 1 := by
  have hsIco : s ∈ Set.Ico (0 : ℝ) α := mem_closedOpenSegment_zero_alpha hα0 hs
  have hbound_pos : 0 < (1 - s) / α := by
    have hs_lt_one : s < 1 := lt_trans hsIco.2 hα1
    exact div_pos (sub_pos.mpr hs_lt_one) hα0
  have hβ_small :
      Set.Iio ((1 - s) / α) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbound_pos)
  filter_upwards [self_mem_nhdsWithin, hβ_small] with β hβ0 hβlt
  constructor
  · -- Positivity of `β` and `α` keeps the perturbed point to the right of `s ≥ 0`.
    nlinarith [hsIco.1, hα0, show 0 < β from hβ0]
  · -- The neighborhood cutoff `β < (1 - s) / α` is chosen exactly so that the perturbed point
    -- stays below `1`.
    have hupper : β * α < 1 - s := (lt_div_iff₀ hα0).mp hβlt
    linarith

/-- Helper for Proposition 17 29: positive rescaling inside the interval keeps the scalar path of
the right half-open secant segment inside `[0,1]`. -/
private lemma eventually_mem_Icc_of_closedOpenSegment_one_alpha
    {α t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ closedOpenSegment (1 : ℝ) α) :
    ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0), t + β * (α - 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have htIoc : t ∈ Set.Ioc α 1 := mem_closedOpenSegment_one_alpha hα1 ht
  have ht_pos : 0 < t := lt_trans hα0 htIoc.1
  have hbound_pos : 0 < t / (1 - α) := by
    exact div_pos ht_pos (sub_pos.mpr hα1)
  have hβ_small :
      Set.Iio (t / (1 - α)) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbound_pos)
  filter_upwards [self_mem_nhdsWithin, hβ_small] with β hβ0 hβlt
  constructor
  · -- The cutoff `β < t / (1 - α)` is chosen so that the negative drift cannot cross `0`.
    have hlower : β * (1 - α) < t := (lt_div_iff₀ (sub_pos.mpr hα1)).mp hβlt
    linarith
  · -- Since `α - 1 ≤ 0`, positive `β` can only move the parameter leftward from `t ≤ 1`.
    nlinarith [htIoc.2, show 0 < β from hβ0, hα1.le]

/-- Helper for Proposition 17 29: moving from one scalar point of `[0,1]` toward another with a
small positive step stays inside `[0,1]`. -/
private lemma eventually_mem_Icc_of_segment_direction
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0), s + β * (t - s) ∈ Set.Icc (0 : ℝ) 1 := by
  have hβ_small : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hβ_small] with β hβ0 hβlt
  have hβ_mem : β ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hβ0, hβlt.le⟩
  have hrepr : s + β * (t - s) = (1 - β) * s + β * t := by
    ring
  constructor
  · -- The perturbed scalar point is a convex combination of two nonnegative endpoints.
    rw [hrepr]
    nlinarith [hs.1, ht.1, hβ_mem.1, hβ_mem.2]
  · -- The same convex-combination form keeps the point below the upper endpoint `1`.
    rw [hrepr]
    nlinarith [hs.2, ht.2, hβ_mem.1, hβ_mem.2]

/-- Helper for Proposition 17 29: eventual membership of the shifted scalar parameters in `[0,1]`
forces the basepoint parameter itself to lie in `[0,1]`. -/
private lemma mem_Icc_of_eventually_add_mul_mem_Icc
    {t c : ℝ}
    (hevent : ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0), t + β * c ∈ Set.Icc (0 : ℝ) 1) :
    t ∈ Set.Icc (0 : ℝ) 1 := by
  have htendsto :
      Filter.Tendsto (fun β : ℝ ↦ t + β * c) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds t) := by
    -- The affine scalar path converges back to its basepoint as `β ↓ 0`.
    have hcont : Continuous (fun β : ℝ ↦ t + β * c) := by
      fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Closedness of `[0,1]` upgrades the eventual interval control to the basepoint itself.
  exact isClosed_Icc.mem_of_tendsto htendsto hevent

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: on a fixed positive scalar step, the secant-gap quotient is the
ambient directional quotient minus the constant chord slope. -/
private lemma secantGap_difference_quotient_eq_ambient_sub_chord_slope
    (f : H → Set.Ioi (⊥ : EReal)) (hdom_convex : Convex ℝ (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {t c β : ℝ} (hβ : 0 < β)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htβ : t + β * c ∈ Set.Icc (0 : ℝ) 1) :
    ((secantGap f x y (t + β * c) - secantGap f x y t) / β) =
      (((f (secantLine x y t + β • (c • (x - y))) : EReal) -
          (f (secantLine x y t) : EReal)) / β) -
        ((((c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
  have hsecant : secantLine x y t ∈ effectiveDomain f :=
    secantLine_mem_effectiveDomain hdom_convex hx hy ht
  have hstep_dom : secantLine x y t + β • (c • (x - y)) ∈ effectiveDomain f := by
    -- The transported ambient basepoint stays in the effective domain because it is the same
    -- secant point evaluated at the shifted scalar parameter.
    simpa [secantLine_add_mul_eq_add_smul, smul_smul, smul_eq_mul] using
      secantLine_mem_effectiveDomain hdom_convex hx hy htβ
  have hgap_t :
      secantGap f x y t =
        ((((f (secantLine x y t) : EReal).toReal -
            ((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal)) : ℝ) : EReal) :=
    secantGap_eq_coe_toReal_sub_chord hdom_convex hx hy ht
  have hgap_tβ :
      secantGap f x y (t + β * c) =
        ((((f (secantLine x y (t + β * c)) : EReal).toReal -
            ((1 - (t + β * c)) * (f y : EReal).toReal +
              (t + β * c) * (f x : EReal).toReal)) : ℝ) : EReal) :=
    secantGap_eq_coe_toReal_sub_chord hdom_convex hx hy htβ
  have hquot :
      (((f (secantLine x y t + β • (c • (x - y))) : EReal) -
            (f (secantLine x y t) : EReal)) / β) =
        ((((f (secantLine x y t + β • (c • (x - y))) : EReal).toReal -
            (f (secantLine x y t) : EReal).toReal) / β : ℝ) : EReal) :=
    directional_quotient_eq_coe_toReal (f := f) (x := secantLine x y t) (d := c • (x - y))
      hsecant hβ hstep_dom
  have hreal :
      (((f (secantLine x y (t + β * c)) : EReal).toReal -
            ((1 - (t + β * c)) * (f y : EReal).toReal +
              (t + β * c) * (f x : EReal).toReal)) -
          ((f (secantLine x y t) : EReal).toReal -
            ((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal))) / β =
        ((f (secantLine x y (t + β * c)) : EReal).toReal -
            (f (secantLine x y t) : EReal).toReal) / β -
          c * ((f x : EReal).toReal - (f y : EReal).toReal) := by
    -- Once all terms are in `ℝ`, the secant-gap quotient reduces to a one-line affine identity.
    field_simp [hβ.ne']
    ring
  calc
    ((secantGap f x y (t + β * c) - secantGap f x y t) / β)
        =
          (((((f (secantLine x y (t + β * c)) : EReal).toReal -
                ((1 - (t + β * c)) * (f y : EReal).toReal +
                  (t + β * c) * (f x : EReal).toReal)) -
              ((f (secantLine x y t) : EReal).toReal -
                ((1 - t) * (f y : EReal).toReal + t * (f x : EReal).toReal))) /
            β : ℝ) : EReal) := by
          -- Rewrite both secant-gap values as finite real expressions before dividing by `β`.
          rw [hgap_tβ, hgap_t, ← EReal.coe_sub, ← EReal.coe_div]
    _ =
          ((((f (secantLine x y (t + β * c)) : EReal).toReal -
                (f (secantLine x y t) : EReal).toReal) / β -
            c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ) : EReal) := by
          -- The real quotient identity isolates the ambient difference quotient and the chord
          -- slope correction.
          exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
    _ =
          ((((f (secantLine x y t + β • (c • (x - y))) : EReal).toReal -
                (f (secantLine x y t) : EReal).toReal) / β -
            c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ) : EReal) := by
          -- Move back from the shifted scalar parameter to the ambient secant point plus the
          -- chord-direction displacement.
          rw [secantLine_add_mul_eq_add_smul]
    _ =
          (((f (secantLine x y t + β • (c • (x - y))) : EReal) -
              (f (secantLine x y t) : EReal)) / β) -
            ((((c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
          -- Repackage the ambient quotient as an `EReal` directional quotient and subtract the
          -- same finite slope term outside the coercion.
          rw [hquot, ← EReal.coe_sub]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: an ambient directional derivative along the chord direction
transfers to the packaged scalar secant gap once the shifted parameters remain in `[0,1]`. -/
private lemma has_directional_derivative_at_secant_gap_of_eventually_mem
    (f : H → Set.Ioi (⊥ : EReal)) (hdom_convex : Convex ℝ (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {t c : ℝ} {ξ : EReal}
    (hξ : HasDirectionalDerivativeAt f (secantLine x y t) (c • (x - y)) ξ)
    (hevent : ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0), t + β * c ∈ Set.Icc (0 : ℝ) 1) :
    HasDirectionalDerivativeAt
      (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
      t c
      (ξ - (((c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_eventually_add_mul_mem_Icc hevent
  have ht_dom :
      t ∈ effectiveDomain (properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) := by
    -- The recovered basepoint lies on the finite secant trace, so the packaged gap is evaluable
    -- there.
    rw [mem_effectiveDomain_iff, properIoi_apply]
    rw [secantGap_eq_coe_toReal_sub_chord hdom_convex hx hy ht]
    exact EReal.coe_lt_top _
  refine ⟨ht_dom, ?_⟩
  let slope : EReal :=
    ((((c * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal))
  have hslope_ne_top : slope ≠ ⊤ := by
    exact EReal.coe_ne_top _
  have hslope_ne_bot : slope ≠ ⊥ := by
    exact EReal.coe_ne_bot _
  have hslope_neg_bot : -slope ≠ ⊥ := by
    -- The chord slope is finite, so its negation is also finite.
    simpa using hslope_ne_top
  have hslope_neg_top : -slope ≠ ⊤ := by
    -- The same finiteness statement keeps the negated slope away from `⊤`.
    simpa using hslope_ne_bot
  have hEq :
      Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun β : ℝ ↦
          (((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) (t + β • c) : EReal) -
              ((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) t : EReal)) / β)
        (fun β : ℝ ↦
          (((f (secantLine x y t + β • (c • (x - y))) : EReal) -
              (f (secantLine x y t) : EReal)) / β) - slope) := by
    filter_upwards [self_mem_nhdsWithin, hevent] with β hβ0 hβmem
    -- On the neighborhood where the shifted parameter stays in `[0,1]`, the packaged quotient
    -- matches the ambient quotient minus the constant chord slope.
    simpa [slope, properIoi_apply, smul_eq_mul] using
      secantGap_difference_quotient_eq_ambient_sub_chord_slope
        (f := f) hdom_convex hx hy hβ0 ht hβmem
  have hsub :
      Filter.Tendsto
        (fun β : ℝ ↦
          (((f (secantLine x y t + β • (c • (x - y))) : EReal) -
              (f (secantLine x y t) : EReal)) / β) - slope)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (ξ - slope)) := by
    have hpair :
        Filter.Tendsto
          (fun β : ℝ ↦
            ((((f (secantLine x y t + β • (c • (x - y))) : EReal) -
                (f (secantLine x y t) : EReal)) / β), -slope))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (ξ, -slope)) := by
      -- Pair the ambient quotient limit with the constant finite chord-slope correction.
      exact Filter.Tendsto.prodMk_nhds hξ.2 tendsto_const_nhds
    have hadd :
        Filter.Tendsto
          (fun p : EReal × EReal ↦ p.1 + p.2)
          (nhds (ξ, -slope))
          (nhds (ξ + -slope)) := by
      -- Addition is continuous here because the second coordinate is finite.
      exact (EReal.continuousAt_add (Or.inr hslope_neg_bot) (Or.inr hslope_neg_top)).tendsto
    -- Reinterpret subtraction as addition of the negated finite slope term.
    simpa [sub_eq_add_neg] using hadd.comp hpair
  exact Filter.Tendsto.congr' hEq.symm hsub

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: an ambient antisymmetry witness between two secant points
transfers to antisymmetric directional derivatives of the packaged secant gap on the same scalar
subsegment. -/
private lemma secant_gap_directional_antisymmetry_on_subsegment
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ζ θ : EReal,
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        s (t - s) ζ ∧
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        t (s - t) θ ∧
      ζ ≤ -θ := by
  let u := secantLine x y s
  let v := secantLine x y t
  have hu : u ∈ effectiveDomain f := by
    -- Convexity keeps the left secant parameter inside the effective domain.
    simpa [u] using secantLine_mem_effectiveDomain hdom_convex hx hy hs
  have hv : v ∈ effectiveDomain f := by
    -- The same convexity argument applies to the right secant parameter.
    simpa [v] using secantLine_mem_effectiveDomain hdom_convex hx hy ht
  obtain ⟨ξ, η, hξ, hη, hanti⟩ := hderiv hu hv
  have huv :
      v - u = (t - s) • (x - y) := by
    -- Two secant points differ by the scalar gap times the common chord direction.
    simpa [u, v] using lineMap_sub_lineMap_eq_smul_sub x y t s
  have hvu :
      u - v = (s - t) • (x - y) := by
    -- Reversing the secant endpoints flips the scalar direction.
    simpa [u, v] using lineMap_sub_lineMap_eq_smul_sub x y s t
  have hξ_gap :
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        s (t - s)
        (ξ - ((((t - s) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
    -- Transport the ambient derivative at `u` to the secant-gap derivative at parameter `s`.
    have hξ' : HasDirectionalDerivativeAt f u ((t - s) • (x - y)) ξ := by
      simpa [huv] using hξ
    simpa [u, v] using
      has_directional_derivative_at_secant_gap_of_eventually_mem
        (f := f) hdom_convex hx hy hξ'
        (eventually_mem_Icc_of_segment_direction hs ht)
  have hη_gap :
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        t (s - t)
        (η - ((((s - t) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
    -- Transport the ambient derivative at `v` to the secant-gap derivative at parameter `t`.
    have hη' : HasDirectionalDerivativeAt f v ((s - t) • (x - y)) η := by
      simpa [hvu] using hη
    simpa [u, v] using
      has_directional_derivative_at_secant_gap_of_eventually_mem
        (f := f) hdom_convex hx hy hη'
        (eventually_mem_Icc_of_segment_direction ht hs)
  let m : EReal :=
    ((((t - s) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)
  have hm_ne_top : m ≠ ⊤ := by
    dsimp [m]
    exact EReal.coe_ne_top _
  have hm_ne_bot : m ≠ ⊥ := by
    dsimp [m]
    exact EReal.coe_ne_bot _
  have hm_flip :
      ((((s - t) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal) = -m := by
    -- The chord-slope correction changes sign when the secant direction is reversed.
    rw [← EReal.coe_neg]
    congr 1
    dsimp [m]
    ring
  have hanti_gap :
      (ξ - m) ≤
        -(
          η - ((((s - t) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
    -- Adding the finite slope correction to the ambient antisymmetry inequality keeps the order.
    have hadd : ξ + (-m) ≤ -η + (-m) := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hanti (-m)
    calc
      ξ - m = ξ + (-m) := by simp [sub_eq_add_neg]
      _ ≤ -η + (-m) := hadd
      _ = -m + -η := by rw [add_comm]
      _ = -(m + η) := by
            simpa using
              (EReal.neg_add (x := m) (y := η) (Or.inl hm_ne_bot) (Or.inl hm_ne_top)).symm
      _ = -(η + m) := by rw [add_comm]
      _ = -(η - ((((s - t) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
            rw [hm_flip]
            simp [sub_eq_add_neg]
  exact ⟨ξ - m,
    η - ((((s - t) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal),
    hξ_gap, hη_gap, hanti_gap⟩

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: the left half of the secant gap satisfies the hypotheses of
Corollary 17.28 and therefore contains a point with strictly positive secant-gap derivative in
direction `α`. -/
private lemma exists_positive_secant_gap_derivative_on_left_half_segment
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hg0 :
      ((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) 0 : EReal) = 0)
    (hg_peak :
      0 < ((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) α : EReal))
    (hg_lsc :
      LowerSemicontinuousOn
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy)).asEReal
        (Set.Icc (0 : ℝ) 1)) :
    ∃ s ∈ closedOpenSegment (0 : ℝ) α, ∃ ξ : EReal,
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        s α ξ ∧
      0 < ξ := by
  let g : ℝ → Set.Ioi (⊥ : EReal) := properIoi (secantGap f x y) (secant_gap_is_proper hx hy)
  have hsubset :
      segment ℝ (0 : ℝ) α ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    rw [segment_eq_Icc hα0.le] at ht
    exact ⟨ht.1, ht.2.trans hα1.le⟩
  have hg_lsc_left : LowerSemicontinuousOn g.asEReal (segment ℝ (0 : ℝ) α) := by
    -- Restrict the global secant-gap lower semicontinuity to the left scalar segment.
    exact hg_lsc.mono hsubset
  have hvalue : g.asEReal 0 < g.asEReal α := by
    -- The left endpoint is zero while the interior secant-gap value is strictly positive.
    have hg0' : g.asEReal 0 = 0 := by
      simpa [Function.asEReal_apply, g, properIoi_apply] using hg0
    rw [hg0']
    simpa [Function.asEReal_apply, g, properIoi_apply] using hg_peak
  have hleft_deriv :
      ∀ s ∈ closedOpenSegment (0 : ℝ) α, ∃ ξ : EReal,
        HasDirectionalDerivativeAt g s α ξ := by
    intro s hs
    have hsIco : s ∈ Set.Ico (0 : ℝ) α := mem_closedOpenSegment_zero_alpha hα0 hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hsIco.1, hsIco.2.le.trans hα1.le⟩
    have hu : secantLine x y s ∈ effectiveDomain f :=
      secantLine_mem_effectiveDomain hdom_convex hx hy hsIcc
    obtain ⟨ξ, η, hξ, hη, hanti⟩ := hderiv hu hx
    have hdir :
        x - secantLine x y s = (1 - s) • (x - y) := by
      -- Moving from the secant point at `s` to the right endpoint follows the chord direction.
      simpa [secantLine] using lineMap_sub_lineMap_eq_smul_sub x y 1 s
    have hs_lt_one : s < 1 := lt_trans hsIco.2 hα1
    have hscale_pos : 0 < α / (1 - s) := by
      exact div_pos hα0 (sub_pos.mpr hs_lt_one)
    have hcoeff :
        (α / (1 - s)) * (1 - s) = α := by
      calc
        (α / (1 - s)) * (1 - s) = α * ((1 - s)⁻¹ * (1 - s)) := by
          rw [div_eq_mul_inv]
          ring
        _ = α := by
          have hcancel : (1 - s)⁻¹ * (1 - s) = (1 : ℝ) :=
            inv_mul_cancel₀ (sub_ne_zero.mpr hs_lt_one.ne.symm)
          rw [hcancel, mul_one]
    have hξ_scaled :
        HasDirectionalDerivativeAt f (secantLine x y s) (α • (x - y)) (ξ * (α / (1 - s))) := by
      -- Rescale the ambient derivative from direction `x - secantLine x y s` to `α • (x - y)`.
      have hξ' :
          HasDirectionalDerivativeAt f (secantLine x y s) ((1 - s) • (x - y)) ξ := by
        simpa [hdir] using hξ
      simpa [smul_smul, hcoeff] using
        has_directional_derivative_at_smul_pos (f := f) (x := secantLine x y s)
          (d := (1 - s) • (x - y)) (ξ := ξ) (c := α / (1 - s)) hξ' hscale_pos
    have hξ_gap :
        HasDirectionalDerivativeAt g s α
          (ξ * (α / (1 - s)) -
            ((((α * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal))) := by
      -- Transfer the rescaled ambient derivative to the scalar secant-gap derivative.
      simpa [g, smul_eq_mul] using
        has_directional_derivative_at_secant_gap_of_eventually_mem
          (f := f) hdom_convex hx hy hξ_scaled
          (eventually_mem_Icc_of_closedOpenSegment_zero_alpha hα0 hα1 hs)
    exact ⟨_, hξ_gap⟩
  have hleft_deriv' :
      ∀ s ∈ closedOpenSegment (0 : ℝ) α, ∃ ξ : EReal,
        HasDirectionalDerivativeAt g s (α - 0) ξ := by
    intro s hs
    obtain ⟨ξ, hξ⟩ := hleft_deriv s hs
    exact ⟨ξ, by simpa using hξ⟩
  simpa [g] using
    exists_positive_directional_derivative_on_half_open_segment
      g 0 α hvalue hg_lsc_left hleft_deriv'

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17 29: the right half of the secant gap satisfies the hypotheses of
Corollary 17.28 and therefore contains a point with strictly positive secant-gap derivative in
direction `α - 1`. -/
private lemma exists_positive_secant_gap_derivative_on_right_half_segment
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hg1 :
      ((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) 1 : EReal) = 0)
    (hg_peak :
      0 < ((properIoi (secantGap f x y) (secant_gap_is_proper hx hy)) α : EReal))
    (hg_lsc :
      LowerSemicontinuousOn
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy)).asEReal
        (Set.Icc (0 : ℝ) 1)) :
    ∃ t ∈ closedOpenSegment (1 : ℝ) α, ∃ ξ : EReal,
      HasDirectionalDerivativeAt
        (properIoi (secantGap f x y) (secant_gap_is_proper hx hy))
        t (α - 1) ξ ∧
      0 < ξ := by
  let g : ℝ → Set.Ioi (⊥ : EReal) := properIoi (secantGap f x y) (secant_gap_is_proper hx hy)
  have hsubset :
      segment ℝ (1 : ℝ) α ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    have htIcc : t ∈ Set.Icc α 1 := by
      simpa [min_eq_right hα1.le, max_eq_left hα1.le] using
        (show t ∈ Set.Icc (min (1 : ℝ) α) (max (1 : ℝ) α) by
          simpa [segment_eq_Icc' (1 : ℝ) α] using ht)
    exact ⟨hα0.le.trans htIcc.1, htIcc.2⟩
  have hg_lsc_right : LowerSemicontinuousOn g.asEReal (segment ℝ (1 : ℝ) α) := by
    -- Restrict the global secant-gap lower semicontinuity to the right scalar segment.
    exact hg_lsc.mono hsubset
  have hvalue : g.asEReal 1 < g.asEReal α := by
    -- The right endpoint is zero while the same interior secant-gap value stays positive.
    have hg1' : g.asEReal 1 = 0 := by
      simpa [Function.asEReal_apply, g, properIoi_apply] using hg1
    rw [hg1']
    simpa [Function.asEReal_apply, g, properIoi_apply] using hg_peak
  have hright_deriv :
      ∀ t ∈ closedOpenSegment (1 : ℝ) α, ∃ ξ : EReal,
        HasDirectionalDerivativeAt g t (α - 1) ξ := by
    intro t ht
    have htIoc : t ∈ Set.Ioc α 1 := mem_closedOpenSegment_one_alpha hα1 ht
    have ht_pos : 0 < t := lt_trans hα0 htIoc.1
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, htIoc.2⟩
    have hu : secantLine x y t ∈ effectiveDomain f :=
      secantLine_mem_effectiveDomain hdom_convex hx hy htIcc
    obtain ⟨ξ, η, hξ, hη, hanti⟩ := hderiv hu hy
    have hdir :
        y - secantLine x y t = (-t) • (x - y) := by
      -- Moving from the secant point at `t` back to the left endpoint reverses the chord
      -- direction.
      simpa [secantLine] using lineMap_sub_lineMap_eq_smul_sub x y 0 t
    have hscale_pos : 0 < (1 - α) / t := by
      exact div_pos (sub_pos.mpr hα1) ht_pos
    have hcoeff :
        ((1 - α) / t) * (-t) = α - 1 := by
      calc
        ((1 - α) / t) * (-t) = (1 - α) * (t⁻¹ * (-t)) := by
          rw [div_eq_mul_inv]
          ring
        _ = (1 - α) * (-1) := by
          simp [ht_pos.ne']
        _ = α - 1 := by ring
    have hξ_scaled :
        HasDirectionalDerivativeAt f (secantLine x y t) ((α - 1) • (x - y))
          (ξ * ((1 - α) / t)) := by
      -- Rescale the ambient derivative from direction `y - secantLine x y t` to
      -- `(α - 1) • (x - y)`.
      have hξ' :
          HasDirectionalDerivativeAt f (secantLine x y t) ((-t) • (x - y)) ξ := by
        simpa [hdir] using hξ
      have hdir_eq :
          ((1 - α) / t) • ((-t) • (x - y)) = (α - 1) • (x - y) := by
        calc
          ((1 - α) / t) • ((-t) • (x - y)) = (((1 - α) / t) * (-t)) • (x - y) := by
            rw [smul_smul]
          _ = (α - 1) • (x - y) := by rw [hcoeff]
      have hscaled :
          HasDirectionalDerivativeAt f (secantLine x y t)
            (((1 - α) / t) • ((-t) • (x - y))) (ξ * ((1 - α) / t)) := by
        exact
          has_directional_derivative_at_smul_pos (f := f) (x := secantLine x y t)
            (d := (-t) • (x - y)) (ξ := ξ) (c := (1 - α) / t) hξ' hscale_pos
      rw [hdir_eq] at hscaled
      exact hscaled
    have hξ_gap :
        HasDirectionalDerivativeAt g t (α - 1)
          (ξ * ((1 - α) / t) -
            ((((α - 1) * ((f x : EReal).toReal - (f y : EReal).toReal) : ℝ)) : EReal)) := by
      -- Transfer the rescaled ambient derivative to the scalar secant-gap derivative.
      simpa [g, smul_eq_mul] using
        has_directional_derivative_at_secant_gap_of_eventually_mem
          (f := f) hdom_convex hx hy hξ_scaled
          (eventually_mem_Icc_of_closedOpenSegment_one_alpha hα0 hα1 ht)
    exact ⟨_, hξ_gap⟩
  simpa [g] using
    exists_positive_directional_derivative_on_half_open_segment
      g 1 α hvalue hg_lsc_right hright_deriv

/-- Helper for Proposition 17 29: once a strict Jensen violation is restricted to the offending
line, Corollary 17.28 should produce two opposite positive directional derivatives, contradicting
the assumed antisymmetry. -/
private lemma strict_jensen_violation_false_of_directional_derivative_antisymmetry
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hstrict :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) <
        (f (α • x + (1 - α) • y) : EReal)) :
    False := by
  let gap : ℝ → EReal := secantGap f x y
  let g : ℝ → Set.Ioi (⊥ : EReal) := properIoi gap (secant_gap_is_proper hx hy)
  have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hα0, hα1.le⟩
  have hgap0 : gap 0 = 0 := by
    -- The left secant endpoint lies on the affine chord.
    simpa [gap] using secant_gap_apply_zero (f := f) (x := x) hy
  have hgap1 : gap 1 = 0 := by
    -- The right secant endpoint lies on the same affine chord.
    simpa [gap] using secant_gap_apply_one (f := f) (x := x) hx
  have hgap_peak : 0 < gap α := by
    -- The strict Jensen violation is exactly the positive interior peak of the secant gap.
    simpa [gap] using secant_gap_pos_of_strict_jensen (f := f) hx hy hstrict
  have hg0 : (g 0 : EReal) = 0 := by
    -- Repackaging by `properIoi` preserves the already-established endpoint value.
    simpa [g, gap] using hgap0
  have hg1 : (g 1 : EReal) = 0 := by
    -- The same preservation holds at the right endpoint.
    simpa [g, gap] using hgap1
  have hg_peak : 0 < (g α : EReal) := by
    -- The positive secant-gap peak survives the `properIoi` wrapper unchanged.
    simpa [g, gap] using hgap_peak
  have hg_lsc :
      LowerSemicontinuousOn g.asEReal (Set.Icc (0 : ℝ) 1) := by
    -- The secant-gap package is now lower semicontinuous on the whole scalar interval `[0,1]`.
    simpa [g, gap] using
      lower_semicontinuous_on_secant_gap_segment f hdom_convex hlsc hx hy
  obtain ⟨s, hs, ξs, hξs, hξs_pos⟩ :=
    exists_positive_secant_gap_derivative_on_left_half_segment
      f hdom_convex hderiv hx hy hα0 hα1 hg0 hg_peak hg_lsc
  obtain ⟨t, ht, ξt, hξt, hξt_pos⟩ :=
    exists_positive_secant_gap_derivative_on_right_half_segment
      f hdom_convex hderiv hx hy hα0 hα1 hg1 hg_peak hg_lsc
  have hsIco : s ∈ Set.Ico (0 : ℝ) α := mem_closedOpenSegment_zero_alpha hα0 hs
  have htIoc : t ∈ Set.Ioc α 1 := mem_closedOpenSegment_one_alpha hα1 ht
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hsIco.1, hsIco.2.le.trans hα1.le⟩
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨(lt_trans hα0 htIoc.1).le, htIoc.2⟩
  have hst : s < t := lt_trans hsIco.2 htIoc.1
  let κs : ℝ := (t - s) / α
  let κt : ℝ := (t - s) / (1 - α)
  have hκs_pos : 0 < κs := by
    -- The two corollary points lie on opposite sides of `α`, so the left rescaling factor is
    -- positive.
    dsimp [κs]
    exact div_pos (sub_pos.mpr hst) hα0
  have hκt_pos : 0 < κt := by
    -- The right rescaling factor is positive for the same reason.
    dsimp [κt]
    exact div_pos (sub_pos.mpr hst) (sub_pos.mpr hα1)
  have hκs_mul : κs * α = t - s := by
    -- The left factor rescales direction `α` to the common gap direction `t - s`.
    dsimp [κs]
    calc
      ((t - s) / α) * α = (t - s) * (α⁻¹ * α) := by
        rw [div_eq_mul_inv]
        ring
      _ = t - s := by
        simp [hα0.ne']
  have hκt_mul : κt * (α - 1) = s - t := by
    -- The right factor rescales direction `α - 1` to the reversed common gap direction.
    dsimp [κt]
    have hcoeff : (1 - α)⁻¹ * (α - 1) = (-1 : ℝ) := by
      have hcancel : (1 - α)⁻¹ * (1 - α) = (1 : ℝ) :=
        inv_mul_cancel₀ (sub_ne_zero.mpr hα1.ne.symm)
      calc
        (1 - α)⁻¹ * (α - 1) = (1 - α)⁻¹ * (-(1 - α)) := by
          rw [show α - 1 = -(1 - α) by ring]
        _ = -((1 - α)⁻¹ * (1 - α)) := by ring
        _ = (-1 : ℝ) := by rw [hcancel]
    calc
      ((t - s) / (1 - α)) * (α - 1) = (t - s) * ((1 - α)⁻¹ * (α - 1)) := by
        rw [div_eq_mul_inv]
        ring
      _ = (t - s) * (-1) := by rw [hcoeff]
      _ = s - t := by ring
  have hξs_rescaled :
      HasDirectionalDerivativeAt g s (t - s) (ξs * κs) := by
    -- Rescale the left corollary derivative onto the common secant-subsegment direction.
    simpa [g, κs, smul_eq_mul, hκs_mul] using
      has_directional_derivative_at_smul_pos (f := g) (x := s) (d := α) (ξ := ξs)
        (c := κs) hξs hκs_pos
  have hξt_rescaled :
      HasDirectionalDerivativeAt g t (s - t) (ξt * κt) := by
    -- Rescale the right corollary derivative onto the opposite common secant-subsegment
    -- direction.
    simpa [g, κt, smul_eq_mul, hκt_mul] using
      has_directional_derivative_at_smul_pos (f := g) (x := t) (d := α - 1) (ξ := ξt)
        (c := κt) hξt hκt_pos
  obtain ⟨ζ, θ, hζ, hθ, hanti_gap⟩ :=
    secant_gap_directional_antisymmetry_on_subsegment
      f hdom_convex hderiv hx hy hsIcc htIcc
  have hζ_eq : ζ = ξs * κs := directional_derivative_value_unique hζ hξs_rescaled
  have hθ_eq : θ = ξt * κt := directional_derivative_value_unique hθ hξt_rescaled
  have hζ_pos : 0 < ζ := by
    -- Uniqueness identifies the antisymmetric left derivative with the positive rescaled
    -- corollary derivative.
    rw [hζ_eq]
    exact EReal.mul_pos hξs_pos (by exact_mod_cast hκs_pos)
  have hθ_pos : 0 < θ := by
    -- The same identification holds on the right-hand side.
    rw [hθ_eq]
    exact EReal.mul_pos hξt_pos (by exact_mod_cast hκt_pos)
  have hnegθ_lt_zero : -θ < 0 := by
    -- A positive right derivative forces its negation to be strictly negative.
    simpa using (EReal.neg_lt_zero.mpr hθ_pos)
  have hζ_lt_zero : ζ < 0 := lt_of_le_of_lt hanti_gap hnegθ_lt_zero
  -- The left derivative cannot be both strictly positive and strictly negative.
  exact not_lt_of_ge hζ_pos.le hζ_lt_zero

-- Proof sketch: argue by contradiction. If `f` fails to be convex on its effective domain, choose
-- a segment with a strict Jensen violation and restrict `f` to that line. Corollary 17.28 then
-- yields two points on the segment with strictly positive opposite directional derivatives, which
-- contradicts the assumed inequality `f'(x; y - x) ≤ -f'(y; x - y)`. Since the codomain already
-- excludes `-∞`, the only primitive data needed from source-level properness is that the effective
-- domain is nonempty.
/-- Proposition 17 29: an `]-∞,+∞]`-valued function is convex on its effective domain if that
domain is nonempty and convex, if the finite-valued restriction is lower semicontinuous on the
effective domain, and if every pair of effective-domain points admits directional derivatives along
the connecting segment that satisfy `f'(x; y - x) ≤ -f'(y; x - y)`. -/
theorem convexOn_effectiveDomain_of_directionalDerivative_antisymmetry
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η) :
    ConvexOn f (effectiveDomain f) := by
  refine ⟨hdom, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  -- Jensen's inequality follows once the source proof's strict-violation alternative is excluded.
  exact not_lt.mp <|
    fun hstrict ↦
      strict_jensen_violation_false_of_directional_derivative_antisymmetry
        f hdom_convex hlsc hderiv hx hy hα0 hα1 hstrict

end ERealFunction
