import Mathlib
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap09.Proposition_9_27
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

open scoped InnerProductSpace

variable (f : ℝ → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

/-- Helper for Proposition 17 16: on `ℝ`, the directional derivative is the infimum of the
positive directional difference quotients. -/
private noncomputable def scalar_directionalDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x y : ℝ) : EReal :=
  sInf (Set.range (directionalDifferenceQuotient f x y))

local notation:arg f "′(" x "; " y ")" => scalar_directionalDerivative f x y

/-- Helper for Proposition 17 16: on `ℝ`, the right derivative is the directional derivative in
the direction `1`. -/
private noncomputable abbrev scalar_rightDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  f′(x; 1)

local notation:arg f "′₊(" x ")" => scalar_rightDerivative f x

/-- Helper for Proposition 17 16: on `ℝ`, the left derivative is the negative directional
derivative in the direction `-1`. -/
private noncomputable abbrev scalar_leftDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  -f′(x; -1)

local notation:arg f "′₋(" x ")" => scalar_leftDerivative f x

/-- Helper for Proposition 17 16: positive rescaling of the direction rescales a directional
derivative limit by the same factor. -/
private theorem has_directional_derivative_at_smul_pos
    {x y : ℝ} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x y ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c * y) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α * y) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    -- Reparameterize the directional quotient by the positive scaling `α ↦ α * c`.
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hcoe_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top c
  have hcoe_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hmul :
      Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ξ * c)) := by
    -- Multiply the reparameterized quotient by the same positive factor to transport the limit.
    exact EReal.Tendsto.mul_const hcomp (Or.inr hcoe_bot) (Or.inr hcoe_top)
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α * (c * y)) : EReal) - (f x : EReal)) / α)
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
    -- Rewrite the scaled-direction quotient into the original quotient evaluated at `α * c`.
    calc
      ((f (x + α * (c * y)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) * y) : EReal) - (f x : EReal)) / α) := by ring_nf
      _ = ((f (x + (α * c) * y) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) * y) : EReal) - (f x : EReal)) *
            ((((α * c : ℝ) : EReal)⁻¹) * c) := by
              rw [hcoeff]
      _ = ((((f (x + (α * c) * y) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
            rw [div_eq_mul_inv]
            exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by
            simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

/-- Helper for Proposition 17 16: the canonical scalar directional derivative is the limit of the
positive directional difference quotients. -/
private theorem hasDirectionalDerivativeAt_scalar_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : ℝ} (hx : x ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) := by
  refine ⟨hx, ?_⟩
  let g : ℝ → EReal := fun α ↦
    if hα : 0 < α then directionalDifferenceQuotient f x y ⟨α, hα⟩ else ⊥
  have hmono : Monotone g := by
    intro α β hαβ
    by_cases hβ : 0 < β
    · by_cases hα : 0 < α
      · have hsub : (⟨α, hα⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨β, hβ⟩ := hαβ
        simpa [g, hα, hβ] using
          directionalDifferenceQuotient_monotone f hconv hx y hsub
      · -- Crossing from the nonpositive region to the positive ray starts at the bottom element.
        simp [g, hα, hβ]
    · have hβ_nonpos : β ≤ 0 := le_of_not_gt hβ
      have hα_nonpos : α ≤ 0 := le_trans hαβ hβ_nonpos
      have hα : ¬ 0 < α := not_lt.mpr hα_nonpos
      -- Both nonpositive arguments land in the constant `⊥` branch.
      simp [g, hα, hβ]
  have htendsto : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (f′(x; y))) := by
    have himage : g '' Set.Ioi (0 : ℝ) = Set.range (directionalDifferenceQuotient f x y) := by
      ext ξ
      constructor
      · intro hξ
        rcases hξ with ⟨α, hα, rfl⟩
        have hα_pos : 0 < α := hα
        refine ⟨⟨α, hα⟩, ?_⟩
        simp [g, hα_pos]
      · intro hξ
        rcases hξ with ⟨α, rfl⟩
        rcases α with ⟨a, ha⟩
        refine ⟨a, ha, ?_⟩
        have ha_pos : 0 < a := ha
        change
          (if hα : 0 < a then directionalDifferenceQuotient f x y ⟨a, hα⟩ else ⊥) =
            directionalDifferenceQuotient f x y ⟨a, ha⟩
        rw [dif_pos ha_pos]
    simpa [scalar_directionalDerivative, himage] using hmono.tendsto_nhdsGT (0 : ℝ)
  have hEq : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α * y) : EReal) - (f x : EReal)) / α)
      g := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hα_pos : 0 < α := hα
    simp [g, directionalDifferenceQuotient, hα_pos]
  exact Filter.Tendsto.congr' hEq.symm htendsto

/-- Helper for Proposition 17 16: any scalar directional derivative limit agrees with the
canonical infimum-valued directional derivative. -/
private theorem scalar_directionalDerivative_eq_of_hasDirectionalDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : ℝ} {ξ : EReal} (hξ : HasDirectionalDerivativeAt f x y ξ) :
    f′(x; y) = ξ := by
  have hdir :=
    hasDirectionalDerivativeAt_scalar_directionalDerivative (f := f) hconv hξ.1 (y := y)
  -- The same difference-quotient filter cannot converge to two different limits.
  exact tendsto_nhds_unique hdir.2 hξ.2

/-- Helper for Proposition 17 16: testing the defining infimum at step `1` bounds the secant
increment from above. -/
private theorem scalar_directionalDerivative_add_value_le
    {x : ℝ} (hx : x ∈ effectiveDomain f) (y : ℝ) :
    f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) := by
  by_cases hy : y ∈ effectiveDomain f
  · have htest :
        f′(x; y - x) ≤ directionalDifferenceQuotient f x (y - x) ⟨1, by norm_num⟩ := by
      -- Test the defining infimum at the unit step, which lands exactly at `y`.
      rw [scalar_directionalDerivative]
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hquot :
        directionalDifferenceQuotient f x (y - x) ⟨1, by norm_num⟩ =
          (f y : EReal) - (f x : EReal) := by
      -- Evaluate the quotient at `α = 1`, where the ray point is exactly `y`.
      simp [directionalDifferenceQuotient, sub_eq_add_neg]
    have hle : f′(x; y - x) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hquot] using htest
    exact (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).1 hle
  · have hfy_top : (f y : EReal) = ⊤ := by
      exact top_unique (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
    -- Outside the effective domain, the target value is `⊤`, so the inequality is immediate.
    simp [hfy_top]

/-- Helper for Proposition 17 16: secant estimates at both endpoints give the standard swap
inequality between opposite scalar directional derivatives. -/
private theorem scalar_directionalDerivative_le_neg_swap
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    f′(x; y - x) ≤ -f′(y; x - y) := by
  have hxy : f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) :=
    scalar_directionalDerivative_add_value_le (f := f) hx y
  have hyx : f′(y; x - y) + (f y : EReal) ≤ (f x : EReal) :=
    scalar_directionalDerivative_add_value_le (f := f) hy x
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hsecant_upper : f′(x; y - x) ≤ (f y : EReal) - (f x : EReal) := by
    -- Rewrite the first secant estimate into subtraction form.
    exact (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).2 hxy
  have hsecant_lower_value : (f y : EReal) ≤ (f x : EReal) - f′(y; x - y) := by
    -- Rewrite the second secant estimate so that the same secant gap appears on the left.
    exact (EReal.le_sub_iff_add_le (.inr hfx_bot) (.inr hfx_top)).2
      (by simpa [add_comm] using hyx)
  have hsecant_lower : (f y : EReal) - (f x : EReal) ≤ -f′(y; x - y) := by
    exact (EReal.sub_le_iff_le_add (.inl hfx_bot) (.inl hfx_top)).2
      (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsecant_lower_value)
  exact le_trans hsecant_upper hsecant_lower

/-- Helper for Proposition 17 16: the scalar directional derivative in the zero direction is
zero at an effective-domain point. -/
private theorem scalar_directionalDerivative_zero
    {x : ℝ} (hx : x ∈ effectiveDomain f) :
    f′(x; 0) = 0 := by
  rw [scalar_directionalDerivative]
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hquot : directionalDifferenceQuotient f x 0 = fun _ ↦ (0 : EReal) := by
    funext α
    simp [directionalDifferenceQuotient, EReal.sub_self hfx_top hfx_bot]
  simp [hquot]

/-- Helper for Proposition 17 16: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  -- Collapse the one-dimensional inner product to the scalar formula on `ℝ`.
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Proposition 17 16: if the ray endpoint leaves the effective domain, then the
corresponding directional difference quotient is `⊤`. -/
private theorem directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) * y ∉ effectiveDomain f) :
    directionalDifferenceQuotient f x y a = ⊤ := by
  -- Once the endpoint value is `⊤`, the positive denominator preserves `⊤`.
  have hxa_top : (f (x + (a : ℝ) * y) : EReal) = ⊤ := by
    exact top_unique (not_lt.mp (by simpa [mem_effectiveDomain_iff] using ha))
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have ha_pos : (0 : EReal) < (a : ℝ) := by
    exact_mod_cast a.2
  have ha_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  change ((f (x + (a : ℝ) * y) : EReal) - (f x : EReal)) / (a : ℝ) = ⊤
  rw [hxa_top, EReal.top_sub hx_top,
    EReal.top_div_of_pos_ne_top ha_pos ha_top]

/-- Helper for Proposition 17 16: if the ray endpoint stays in the effective domain, then the
directional difference quotient is the cast of the corresponding real quotient. -/
private theorem directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) * y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y a =
      ((((f (x + (a : ℝ) * y) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) : EReal) := by
  -- Finite endpoint values let the quotient collapse to an ordinary real expression.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) * y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp ha)
  have hxa_bot : (f (x + (a : ℝ) * y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) * y) : EReal) from
      (f (x + (a : ℝ) * y)).2)
  change ((f (x + (a : ℝ) * y) : EReal) - (f x : EReal)) / (a : ℝ) =
    ((((f (x + (a : ℝ) * y) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) : EReal)
  rw [← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 17 16: the convex upper bound at the midpoint between `x + α` and
`x - β` rearranges to the usual inequality between the corresponding real secant quotients. -/
private theorem real_difference_quotient_le_of_convex_bound
    {u v w α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (h : w ≤ (β / (α + β)) * u + (1 - β / (α + β)) * v) :
    (w - v) / β ≤ (u - w) / α := by
  -- Multiply through by the positive denominator `α + β`, then isolate the two quotients.
  have hsum_pos : 0 < α + β := add_pos hα hβ
  have hmul : (α + β) * w ≤ β * u + α * v := by
    calc
      (α + β) * w ≤ (α + β) * ((β / (α + β)) * u + (1 - β / (α + β)) * v) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt hsum_pos)
      _ = β * u + α * v := by
        field_simp [hsum_pos.ne']
        ring
  have hquot : α * (w - v) ≤ β * (u - w) := by
    nlinarith
  have hgoal : (w - v) / β ≤ (u - w) / α := by
    field_simp [hα.ne', hβ.ne'] at hquot ⊢
    linarith
  exact hgoal

/-- Helper for Proposition 17 16: the directional derivative is positively homogeneous with
respect to positive real scalars in the direction variable. -/
private theorem directionalDerivative_mul_of_pos
    (hconv : ConvexOn f (effectiveDomain f))
    {x y c : ℝ} (hx : x ∈ effectiveDomain f) (hc : 0 < c) :
    f′(x; c * y) = f′(x; y) * c := by
  have hdir : HasDirectionalDerivativeAt f x y (f′(x; y)) :=
    hasDirectionalDerivativeAt_scalar_directionalDerivative
      (f := f) hconv (x := x) hx (y := y)
  have hscaled : HasDirectionalDerivativeAt f x (c * y) (f′(x; y) * c) := by
    simpa [smul_eq_mul] using
      has_directional_derivative_at_smul_pos
        (f := f) (x := x) (y := y) (ξ := f′(x; y)) hdir hc
  exact scalar_directionalDerivative_eq_of_hasDirectionalDerivativeAt
    (f := f) hconv hscaled

/-- Helper for Proposition 17 16: multiplying by a positive real preserves order on `EReal`. -/
private theorem mul_le_mul_of_pos_right
    {a b : EReal} {c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a * c ≤ b * c := by
  -- Divide by the positive scalar and use strict monotonicity of right-division.
  have hmono := (EReal.strictMono_div_right_of_pos
    (show (0 : EReal) < ((c : EReal)⁻¹) by
      rw [← EReal.coe_inv c]
      exact_mod_cast inv_pos.mpr hc)
    (by
      rw [← EReal.coe_inv c]
      exact EReal.coe_ne_top _)).monotone
  have hcinv : (((c : EReal)⁻¹)⁻¹) = (c : EReal) := by
    rw [EReal.inv_inv] <;> simp
  simpa [div_eq_mul_inv, hcinv] using hmono h

/-- Helper for Proposition 17 16: a positive common factor can be canceled from an `EReal`
inequality. -/
private theorem le_of_mul_le_mul_of_pos_right
    {a b : EReal} {c : ℝ} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  -- Divide the inequality by the positive factor and simplify both sides.
  have hdiv :
      (a * c) / (c : EReal) ≤ (b * c) / (c : EReal) := by
    exact EReal.div_le_div_right_of_nonneg
      (show (0 : EReal) ≤ (c : EReal) by exact_mod_cast hc.le) h
  have hc_bot : ((c : ℝ) : EReal) ≠ ⊥ := by
    exact EReal.coe_ne_bot _
  have hc_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hc_zero : ((c : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hcancel_a : (a * c) / (c : EReal) = a := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  have hcancel_b : (b * c) / (c : EReal) = b := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  simpa [hcancel_a, hcancel_b] using hdiv

include hconv

-- Proof sketch: apply convexity to the midpoint identity
-- `x = ((x - α) + (x + α)) / 2`, rearrange the resulting inequality of secant quotients, and pass
-- to the infimum definitions of the one-sided directional derivatives.
/-- Proposition 17 16 (1): at an effective-domain point of a convex function on `ℝ`, the left
derivative is bounded above by the right derivative. -/
theorem leftDerivative_le_rightDerivative
    {x : ℝ} (hx : x ∈ effectiveDomain f) :
    f′₋(x) ≤ f′₊(x) := by
  -- Compare every left secant quotient with every right secant quotient across `x`.
  rw [scalar_leftDerivative, scalar_rightDerivative,
    scalar_directionalDerivative, scalar_directionalDerivative]
  apply le_sInf
  intro z hz
  rcases hz with ⟨α, rfl⟩
  have hlower :
      -(directionalDifferenceQuotient f x 1 α) ≤
        sInf (Set.range (directionalDifferenceQuotient f x (-1))) := by
    apply le_sInf
    intro w hw
    rcases hw with ⟨β, rfl⟩
    by_cases hαdom : x + (α : ℝ) ∈ effectiveDomain f
    · by_cases hβdom : x - (β : ℝ) ∈ effectiveDomain f
      · have hα_top : (f (x + (α : ℝ)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
        have hα_bot : (f (x + (α : ℝ)) : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f (x + (α : ℝ)) : EReal) from (f (x + (α : ℝ))).2)
        have hβ_top : (f (x - (β : ℝ)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hβdom)
        have hβ_bot : (f (x - (β : ℝ)) : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f (x - (β : ℝ)) : EReal) from (f (x - (β : ℝ))).2)
        have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hx_bot : (f x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
        have hsum_pos : 0 < (α : ℝ) + (β : ℝ) := add_pos α.2 β.2
        have hweight_pos : 0 < (β : ℝ) / ((α : ℝ) + (β : ℝ)) := div_pos β.2 hsum_pos
        have hweight_lt_one : (β : ℝ) / ((α : ℝ) + (β : ℝ)) < 1 := by
          refine lt_of_not_ge ?_
          intro hle
          have hmul : (α : ℝ) + (β : ℝ) ≤ (β : ℝ) := by
            simpa using (one_le_div hsum_pos).mp hle
          have hα_nonpos : (α : ℝ) ≤ 0 := by
            linarith
          exact (not_le_of_gt α.2) hα_nonpos
        have hx_combo :
            x = ((β : ℝ) / ((α : ℝ) + (β : ℝ))) * (x + (α : ℝ)) +
              (1 - (β : ℝ) / ((α : ℝ) + (β : ℝ))) * (x - (β : ℝ)) := by
          field_simp [hsum_pos.ne']
          ring
        have hconvx :
            (f x : EReal) ≤
              ((β : ℝ) / ((α : ℝ) + (β : ℝ)) : EReal) * (f (x + (α : ℝ)) : EReal) +
                (1 - (β : ℝ) / ((α : ℝ) + (β : ℝ)) : EReal) * (f (x - (β : ℝ)) : EReal) := by
          -- Rewrite `x` as the convex combination of the two neighboring points.
          nth_rewrite 1 [hx_combo]
          exact hconv.ineq hαdom hβdom hweight_pos hweight_lt_one
        have hconv_real :
            (f x : EReal).toReal ≤
              (β : ℝ) / ((α : ℝ) + (β : ℝ)) * (f (x + (α : ℝ)) : EReal).toReal +
                (1 - (β : ℝ) / ((α : ℝ) + (β : ℝ))) * (f (x - (β : ℝ)) : EReal).toReal := by
          have hcast := hconvx
          rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hα_top hα_bot,
            ← EReal.coe_toReal hβ_top hβ_bot] at hcast
          have hcast' :
              (((f x : EReal).toReal : ℝ) : EReal) ≤
                (((β : ℝ) / ((α : ℝ) + (β : ℝ)) * (f (x + (α : ℝ)) : EReal).toReal +
                    (1 - (β : ℝ) / ((α : ℝ) + (β : ℝ))) * (f (x - (β : ℝ)) : EReal).toReal : ℝ) :
                  EReal) := by
            simpa [EReal.coe_add, EReal.coe_mul]
              using hcast
          exact EReal.coe_le_coe_iff.mp hcast'
        have hreal :
            ((f x : EReal).toReal - (f (x - (β : ℝ)) : EReal).toReal) / (β : ℝ) ≤
              ((f (x + (α : ℝ)) : EReal).toReal - (f x : EReal).toReal) / (α : ℝ) :=
          real_difference_quotient_le_of_convex_bound α.2 β.2 hconv_real
        have hleft :
            -directionalDifferenceQuotient f x 1 α ≤
              directionalDifferenceQuotient f x (-1) β := by
          rw [directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
              (f := f) hx α (by simpa [smul_eq_mul] using hαdom),
            directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
              (f := f) hx β (by simpa [smul_eq_mul] using hβdom)]
          have hleft' :
              -((((f (x + (α : ℝ)) : EReal).toReal - (f x : EReal).toReal) /
                  (α : ℝ) : ℝ) : EReal) ≤
                ((((f (x - (β : ℝ)) : EReal).toReal - (f x : EReal).toReal) /
                    (β : ℝ) : ℝ) : EReal) := by
            let A :=
              ((f (x + (α : ℝ)) : EReal).toReal - (f x : EReal).toReal) / (α : ℝ)
            let B :=
              ((f (x - (β : ℝ)) : EReal).toReal - (f x : EReal).toReal) / (β : ℝ)
            have hAB : -B ≤ A := by
              dsimp [A, B]
              have hB :
                  -(((f (x - (β : ℝ)) : EReal).toReal - (f x : EReal).toReal) / (β : ℝ)) =
                    ((f x : EReal).toReal - (f (x - (β : ℝ)) : EReal).toReal) / (β : ℝ) := by
                ring
              rw [hB]
              exact hreal
            have hreal'' : -A ≤ B := by
              simpa using neg_le_neg hAB
            rw [← EReal.coe_neg]
            exact_mod_cast hreal''
          simpa [smul_eq_mul, one_mul, mul_neg, sub_eq_add_neg] using hleft'
        simpa [directionalDifferenceQuotient, smul_eq_mul] using hleft
      · -- If the left endpoint is outside the domain, its quotient is `⊤`.
        -- The comparison is then trivial.
        rw [directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
            (f := f) hx β (by simpa using hβdom)]
        simp
    · -- If the right endpoint is outside the domain, the right quotient is `⊤`.
      -- Then `-⊤` is a lower bound.
      rw [directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
          (f := f) hx α (by simpa using hαdom)]
      simp
  -- The right derivative is the infimum of all right secant quotients, so this lower bound closes.
  exact EReal.neg_le.mp hlower

omit hconv in
/-- Helper for Proposition 17 16: a subgradient at `x` gives a lower bound on every positive
directional increment quotient on `ℝ`. -/
private theorem mul_le_increment_quotient_of_mem_subdifferential
    {x u y : ℝ} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    {α : ℝ} (hα : 0 < α) :
    ((y * u : ℝ) : EReal) ≤
      (((f (x + α * y) : EReal) - (f x : EReal)) / α) := by
  have huα :
      (((α * y) * u : ℝ) : EReal) + (f x : EReal) ≤
        (f (x + α * y) : EReal) := by
    -- Evaluate the affine minorant inequality at the ray point `x + α * y`.
    calc
      (((α * y) * u : ℝ) : EReal) + (f x : EReal)
          = (⟪x + α * y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
              simp [real_inner_eq_mul, sub_eq_add_neg, mul_assoc]
      _ ≤ (f (x + α * y) : EReal) := (mem_subdifferential_iff f x u).1 hu (x + α * y)
  by_cases hxy : x + α * y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_top : (f (x + α * y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxy)
    have hxy_bot : (f (x + α * y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α * y) : EReal) from
        (f (x + α * y)).2)
    have huα_real :
        α * (y * u) + (f x : EReal).toReal ≤
          (f (x + α * y) : EReal).toReal := by
      -- Move the `EReal` inequality to the finite branch so the division is ordinary real algebra.
      have hcast :
          (((α * (y * u) + (f x : EReal).toReal : ℝ) : EReal)) ≤
            (((f (x + α * y) : EReal).toReal : ℝ) : EReal) := by
        calc
          (((α * (y * u) + (f x : EReal).toReal : ℝ) : EReal))
              = (((α * y) * u : ℝ) : EReal) + (f x : EReal) := by
                  rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                  simp [EReal.coe_mul, mul_assoc]
          _ ≤ (f (x + α * y) : EReal) := huα
          _ = (((f (x + α * y) : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hxy_top hxy_bot).symm
      exact_mod_cast hcast
    have hquot_real :
        y * u ≤
          ((f (x + α * y) : EReal).toReal - (f x : EReal).toReal) / α := by
      -- Divide by the positive step length `α`.
      refine (le_div_iff₀ hα).2 ?_
      linarith
    have hquot_cast :
        ((y * u : ℝ) : EReal) ≤
          ((((f (x + α * y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      exact_mod_cast hquot_real
    have hquot_eq :
        (((f (x + α * y) : EReal) - (f x : EReal)) / α) =
          ((((f (x + α * y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      -- Finite endpoint values identify the extended-real quotient with the real quotient.
      rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      simp
    rw [hquot_eq]
    exact hquot_cast
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hxy_top : (f (x + α * y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxy))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
    -- Outside the effective domain, the positive quotient is `⊤`, so the lower bound is automatic.
    rw [hxy_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    exact le_top

omit hconv in
/-- Helper for Proposition 17 16: a subgradient yields a lower bound for every scalar directional
derivative on `ℝ`. -/
private theorem mul_le_directionalDerivative_of_mem_subdifferential
    {x u : ℝ} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ∀ y : ℝ, ((y * u : ℝ) : EReal) ≤ f′(x; y) := by
  intro y
  rw [scalar_directionalDerivative]
  apply le_sInf
  rintro q ⟨α, rfl⟩
  -- Every positive directional difference quotient dominates the scalar pairing `y * u`.
  simpa [directionalDifferenceQuotient, smul_eq_mul, mul_left_comm, mul_assoc] using
    mul_le_increment_quotient_of_mem_subdifferential
      (f := f) (x := x) (u := u) (y := y) hx hu (α := (α : ℝ)) α.2

omit hconv in
/-- Helper for Proposition 17 16: pointwise domination by the scalar directional derivative
recovers the subgradient inequality on `ℝ`. -/
private theorem mem_subdifferential_of_forall_mul_le_directionalDerivative
    {x u : ℝ} (hx : x ∈ effectiveDomain f)
    (hu : ∀ y : ℝ, ((y * u : ℝ) : EReal) ≤ f′(x; y)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro z
  have hdir : (((z - x) * u : ℝ) : EReal) ≤ f′(x; z - x) := hu (z - x)
  -- Evaluate the directional-derivative bound in the source direction `z - x`.
  calc
    (⟪z - x, u⟫_ℝ : EReal) + (f x : EReal)
        = (((z - x) * u : ℝ) : EReal) + (f x : EReal) := by
            simp [real_inner_eq_mul]
    _ ≤ f′(x; z - x) + (f x : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdir (f x : EReal)
    _ ≤ (f z : EReal) := scalar_directionalDerivative_add_value_le (f := f) hx z

omit hconv in
/-- Helper for Proposition 17 16: every subgradient lies below the right derivative. -/
private theorem le_rightDerivative_of_mem_subdifferential
    {x u : ℝ} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ((u : ℝ) : EReal) ≤ f′₊(x) := by
  -- Test the global directional bound at the positive direction `1`.
  simpa [scalar_rightDerivative] using
    mul_le_directionalDerivative_of_mem_subdifferential
      (f := f) (x := x) (u := u) hx hu 1

omit hconv in
/-- Helper for Proposition 17 16: every subgradient lies above the left derivative. -/
private theorem leftDerivative_le_of_mem_subdifferential
    {x u : ℝ} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    f′₋(x) ≤ ((u : ℝ) : EReal) := by
  have hdir :
      (-((u : ℝ) : EReal)) ≤ f′(x; -1) := by
    -- Test the global directional bound at `-1` and rewrite the scalar product.
    simpa [EReal.coe_neg] using
      mul_le_directionalDerivative_of_mem_subdifferential
        (f := f) (x := x) (u := u) hx hu (-1)
  -- Negating the one-sided derivative turns the bound into the left-derivative inequality.
  simpa [scalar_leftDerivative] using EReal.neg_le.mp hdir

/-- Helper for Proposition 17 16: interval membership between the one-sided derivatives gives a
pointwise lower bound for all scalar directional derivatives. -/
private theorem mul_le_directionalDerivative_of_mem_Icc_oneSidedDerivatives
    {x u : ℝ} (hx : x ∈ effectiveDomain f)
    (hleft : f′₋(x) ≤ ((u : ℝ) : EReal)) (hright : ((u : ℝ) : EReal) ≤ f′₊(x)) :
    ∀ y : ℝ, ((y * u : ℝ) : EReal) ≤ f′(x; y) := by
  intro y
  rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
  · have hy_pos' : 0 < -y := by linarith
    have hneg_dir :
        (-((u : ℝ) : EReal)) ≤ f′(x; -1) := by
      -- Rewriting the left-derivative bound isolates the derivative in direction `-1`.
      exact EReal.neg_le.mp (by simpa [scalar_leftDerivative] using hleft)
    have hscaled :
        (-((u : ℝ) : EReal)) * (-y) ≤ f′(x; -1) * (-y) :=
      mul_le_mul_of_pos_right hneg_dir hy_pos'
    have hdir :
        f′(x; y) = f′(x; -1) * (-y) := by
      -- The negative direction is a positive multiple of `-1`.
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        directionalDerivative_mul_of_pos (f := f) hconv (x := x) (y := (-1 : ℝ)) hx hy_pos'
    calc
      ((y * u : ℝ) : EReal) = (-((u : ℝ) : EReal)) * (-y) := by
        simp [EReal.coe_mul, mul_comm]
      _ ≤ f′(x; -1) * (-y) := hscaled
      _ = f′(x; y) := hdir.symm
  · -- The zero direction is handled by Proposition 17.2 (5).
    simp [scalar_directionalDerivative_zero (f := f) hx]
  · have hscaled :
        ((u : ℝ) : EReal) * y ≤ f′₊(x) * y :=
      mul_le_mul_of_pos_right hright hy_pos
    have hdir :
        f′(x; y) = f′₊(x) * y := by
      -- Positive homogeneity rewrites the direction `y` as a positive multiple of `1`.
      simpa [scalar_rightDerivative, mul_comm, mul_left_comm, mul_assoc] using
        directionalDerivative_mul_of_pos (f := f) hconv (x := x) (y := (1 : ℝ)) hx hy_pos
    calc
      ((y * u : ℝ) : EReal) = ((u : ℝ) : EReal) * y := by
        simp [EReal.coe_mul, mul_comm]
      _ ≤ f′₊(x) * y := hscaled
      _ = f′(x; y) := hdir.symm

/-- Helper for Proposition 17 16: interval membership between the one-sided derivatives recovers
subgradient membership on `ℝ`. -/
private theorem mem_subdifferential_of_mem_Icc_oneSidedDerivatives
    {x u : ℝ} (hx : x ∈ effectiveDomain f)
    (hleft : f′₋(x) ≤ ((u : ℝ) : EReal)) (hright : ((u : ℝ) : EReal) ≤ f′₊(x)) :
    u ∈ (∂ f) x := by
  -- Route correction: instead of importing Proposition 17.14, rebuild its scalar consequence
  -- locally from the interval bounds and then apply Proposition 17.2 (2).
  exact
    mem_subdifferential_of_forall_mul_le_directionalDerivative
      (f := f) hx
      (mul_le_directionalDerivative_of_mem_Icc_oneSidedDerivatives
        (f := f) (hconv := hconv) (x := x) (u := u) hx hleft hright)

-- Proof sketch: specialize Proposition 17.14 (1) to `H = ℝ`, test the subgradient inequality on
-- the directions `1` and `-1`, and use clause (1) to identify the subdifferential with the real
-- preimage of the extended-real interval between the one-sided derivatives `f′₋(x)` and `f′₊(x)`.
/-- Proposition 17 16 (2): at an effective-domain point of a convex function on `ℝ`, the
subdifferential is the set of real numbers lying between the left and right derivatives. -/
theorem subdifferential_eq_Icc_oneSidedDerivatives
    {x : ℝ} (hx : x ∈ effectiveDomain f) :
    (∂ f) x =
      ((↑) : ℝ → EReal) ⁻¹' Set.Icc (f′₋(x)) (f′₊(x)) := by
  -- Route correction: keep the source proof local by extracting the two endpoint inequalities and
  -- rebuilding the full subgradient inequality from the sign split on scalar directions.
  ext u
  constructor
  · intro hu
    constructor
    · exact leftDerivative_le_of_mem_subdifferential (f := f) hx hu
    · exact le_rightDerivative_of_mem_subdifferential (f := f) hx hu
  · intro hu
    rw [Set.mem_preimage, Set.mem_Icc] at hu
    exact
      mem_subdifferential_of_mem_Icc_oneSidedDerivatives
        (f := f) (hconv := hconv) (x := x) (u := u) hx hu.1 hu.2

-- Proof sketch: apply Proposition 17.2 (3) to the pair `x < y`, then rewrite the directional
-- derivatives along `y - x` and `x - y` by factoring out the positive scalar `y - x`.
/-- Proposition 17 16 (3): along an increasing pair of effective-domain points of a convex
function on `ℝ`, the right derivative at the left point does not exceed the left derivative at the
right point. -/
theorem rightDerivative_le_leftDerivative_of_lt
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hxy : x < y) :
    f′₊(x) ≤ f′₋(y) := by
  -- Compare the two directional derivatives along the segment and cancel the positive length.
  have hxy_pos : 0 < y - x := sub_pos.mpr hxy
  have hseg :
      f′(x; y - x) ≤ -f′(y; x - y) :=
    scalar_directionalDerivative_le_neg_swap (f := f) hx hy
  have hx_mul :
      f′(x; y - x) = f′₊(x) * (y - x) := by
    simpa [scalar_rightDerivative, mul_comm] using
      directionalDerivative_mul_of_pos (f := f) hconv (x := x) (y := (1 : ℝ)) hx hxy_pos
  have hy_mul :
      -f′(y; x - y) = f′₋(y) * (y - x) := by
    have hdir :
        f′(y; x - y) = f′(y; -1) * (y - x) := by
      have hyx : x - y = (y - x) * (-1 : ℝ) := by ring
      rw [hyx]
      simpa [mul_comm] using
        directionalDerivative_mul_of_pos (f := f) hconv (x := y) (y := (-1 : ℝ)) hy hxy_pos
    calc
      -f′(y; x - y) = -(f′(y; -1) * (y - x)) := by rw [hdir]
      _ = (-f′(y; -1)) * (y - x) := by rw [neg_mul]
      _ = f′₋(y) * (y - x) := by simp [scalar_leftDerivative]
  have hmul : f′₊(x) * (y - x) ≤ f′₋(y) * (y - x) := by
    simpa [hx_mul, hy_mul] using hseg
  exact le_of_mul_le_mul_of_pos_right hmul hxy_pos

-- Proof sketch: if `x ≤ y` are both in the effective domain, apply clause (3) to compare the
-- right derivative at `x` with the left derivative at `y`, then insert clause (1) at `y`.
/-- Proposition 17 16 (4): the right derivative of a convex function on `ℝ` is increasing on its
effective domain. -/
theorem monotoneOn_rightDerivative :
    MonotoneOn (fun x : ℝ ↦ f′₊(x)) (effectiveDomain f) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hxy_lt | rfl
  · -- The strict comparison comes from clause (3), followed by clause (1) at the right endpoint.
    calc
      f′₊(x) ≤ f′₋(y) :=
        rightDerivative_le_leftDerivative_of_lt (f := f) (hconv := hconv) hx hy hxy_lt
      _ ≤ f′₊(y) := leftDerivative_le_rightDerivative (f := f) (hconv := hconv) hy
  · rfl

-- Proof sketch: if `x ≤ y` are both in the effective domain, combine clause (1) at `x` with
-- clause (3) to compare the left derivative at `x` and the left derivative at `y`.
/-- Proposition 17 16 (5): the left derivative of a convex function on `ℝ` is increasing on its
effective domain. -/
theorem monotoneOn_leftDerivative :
    MonotoneOn (fun x : ℝ ↦ f′₋(x)) (effectiveDomain f) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hxy_lt | rfl
  · -- The strict comparison comes from clause (1) at the left endpoint, then clause (3).
    calc
      f′₋(x) ≤ f′₊(x) := leftDerivative_le_rightDerivative (f := f) (hconv := hconv) hx
      _ ≤ f′₋(y) := rightDerivative_le_leftDerivative_of_lt (f := f) (hconv := hconv) hx hy hxy_lt
  · rfl

end DirectionalDerivativesAndSubgradients

end ERealFunction
