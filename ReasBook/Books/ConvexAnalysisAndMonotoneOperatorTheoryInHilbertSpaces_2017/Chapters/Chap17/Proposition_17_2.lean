import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Proposition_9_27
import BauschkeLean.Chap10.Definition_10_1
import BauschkeLean.Chap10.Proposition_10_3
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

noncomputable section

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- The directional derivative of an extended-real-valued function at `x` along `y`, encoded as
the infimum of the positive directional difference quotients. -/
noncomputable def directionalDerivative
    (x y : H) : EReal :=
  sInf (Set.range (directionalDifferenceQuotient f x y))

notation:arg f "′(" x "; " y ")" => directionalDerivative f x y

/-- The right derivative of an extended-real-valued function on `ℝ`, viewed as the
one-dimensional specialization of the canonical directional derivative owner. -/
noncomputable abbrev rightDerivative (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  f′(x; 1)

notation:arg f "′₊(" x ")" => rightDerivative f x

/-- The left derivative of an extended-real-valued function on `ℝ`, viewed as the
one-dimensional specialization of the canonical directional derivative owner. -/
noncomputable abbrev leftDerivative (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  -f′(x; -1)

notation:arg f "′₋(" x ")" => leftDerivative f x

/-- Source clause (i): formula (17.4). The canonical directional derivative is the
infimum of the positive-ray difference quotients viewed as a real-parameter image. -/
theorem directionalDerivative_eq_sInf_image_Ioi
    (x y : H) :
    directionalDerivative f x y =
      sInf ((fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) '' Set.Ioi (0 : ℝ)) := by
  -- Rewrite the infimum over positive scalars by forgetting the subtype wrapper.
  rw [directionalDerivative]
  congr 1
  ext ξ
  constructor
  · intro hξ
    rcases hξ with ⟨α, rfl⟩
    exact ⟨(α : ℝ), α.2, by simp [directionalDifferenceQuotient]⟩
  · intro hξ
    rcases hξ with ⟨α, hα, hξ⟩
    refine ⟨⟨α, hα⟩, ?_⟩
    simpa [directionalDifferenceQuotient] using hξ

/-- Directional-derivative helper: positive scaling of the direction rescales both the directional
quotient limit and the derivative value. -/
private theorem has_directional_derivative_at_smul_pos
    {x y : H} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x y ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c • y) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    -- Reparameterize the quotient by the positive scaling `α ↦ α * c`.
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hcoe_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top c
  have hcoe_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hmul :
      Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ξ * c)) := by
    -- Multiplying the reparameterized quotient transports the limit by the same factor.
    exact EReal.Tendsto.mul_const hcomp (Or.inr hcoe_bot) (Or.inr hcoe_top)
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α)
      (fun α ↦ q (α * c) * c) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hc0 : c ≠ 0 := hc.ne'
    have hcoeff : ((((α * c : ℝ) : EReal)⁻¹) * c) = ((α : EReal)⁻¹) := by
      rw [← EReal.coe_inv (α * c), ← EReal.coe_mul, ← EReal.coe_inv α]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        calc
          (α * c)⁻¹ * c = c / (α * c) := by
            rw [div_eq_mul_inv, mul_comm]
          _ = α⁻¹ := by
            simpa [mul_comm] using (div_mul_cancel_left₀ hc0 α)
    -- Rewrite the scaled quotient into the original quotient evaluated at `α * c`.
    calc
      ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) • y) : EReal) - (f x : EReal)) / α) := by
              simp [smul_smul, mul_comm]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) *
            ((((α * c : ℝ) : EReal)⁻¹) * c) := by
              rw [hcoeff]
      _ =
          ((((f (x + (α * c) • y) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
            rw [div_eq_mul_inv]
            exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by
            simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

/-- Directional-derivative helper: the positive directional difference quotient converges to the
canonical infimum-valued directional derivative along the right-hand filter at `0`. -/
private theorem directional_difference_quotient_tendsto_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Filter.Tendsto
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y))) := by
  -- Extend the positive-ray quotient to an ambient monotone function and identify its right limit.
  let g : ℝ → EReal := fun α ↦
    if hα : 0 < α then directionalDifferenceQuotient f x y ⟨α, hα⟩ else ⊥
  have hmono : Monotone g := by
    intro α β hαβ
    by_cases hβ : 0 < β
    · by_cases hα : 0 < α
      · have hsub : (⟨α, hα⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨β, hβ⟩ := hαβ
        simpa [g, hα, hβ] using directionalDifferenceQuotient_monotone f hconv hx y hsub
      · simp [g, hα, hβ]
    · have hβ_nonpos : β ≤ 0 := le_of_not_gt hβ
      have hα_nonpos : α ≤ 0 := le_trans hαβ hβ_nonpos
      have hα : ¬ 0 < α := not_lt.mpr hα_nonpos
      simp [g, hα, hβ]
  have htendsto :
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y))) := by
    have himage :
        g '' Set.Ioi (0 : ℝ) =
          (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) '' Set.Ioi (0 : ℝ) := by
      ext ξ
      constructor
      · intro hξ
        rcases hξ with ⟨α, hα, rfl⟩
        have hα' : 0 < α := hα
        refine ⟨α, hα, ?_⟩
        simp [g, directionalDifferenceQuotient, hα']
      · intro hξ
        rcases hξ with ⟨α, hα, rfl⟩
        have hα' : 0 < α := hα
        refine ⟨α, hα, ?_⟩
        simp [g, directionalDifferenceQuotient, hα']
    rw [directionalDerivative_eq_sInf_image_Ioi f x y]
    simpa [himage] using hmono.tendsto_nhdsGT (0 : ℝ)
  have hEq : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      g := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hα' : 0 < α := hα
    simp [g, directionalDifferenceQuotient, hα']
  exact Filter.Tendsto.congr' hEq.symm htendsto

/-- Source clause (i): at an effective-domain point of a convex function, the
directional derivative exists in the source sense, with value given by the infimum formula. -/
theorem hasDirectionalDerivativeAt_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) := by
  -- Package the canonical quotient limit as the source directional-derivative object.
  exact ⟨hx, directional_difference_quotient_tendsto_directionalDerivative
    f hconv hx y⟩

/-- Any source-facing directional derivative of a convex function agrees with the canonical
function-valued owner. -/
theorem directionalDerivative_eq_of_hasDirectionalDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} {ξ : EReal} (hξ : HasDirectionalDerivativeAt f x y ξ) :
    f′(x; y) = ξ := by
  -- The same quotient filter cannot converge to two different directional-derivative values.
  have hdir := hasDirectionalDerivativeAt_directionalDerivative f hconv hξ.1 y
  exact tendsto_nhds_unique hdir.2 hξ.2

/-- Directional-derivative helper: positive rescaling of the direction rescales the directional
derivative by the same positive factor. -/
private theorem directionalDerivative_smul_of_pos
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) {c : ℝ} (hc : 0 < c) :
    f′(x; c • y) = f′(x; y) * c := by
  have hdir : HasDirectionalDerivativeAt f x y (f′(x; y)) :=
    hasDirectionalDerivativeAt_directionalDerivative f hconv hx y
  have hscaled : HasDirectionalDerivativeAt f x (c • y) (f′(x; y) * c) := by
    -- Transport the canonical derivative limit through the positive reparameterization.
    exact has_directional_derivative_at_smul_pos f hdir hc
  exact directionalDerivative_eq_of_hasDirectionalDerivativeAt f hconv hscaled

-- Proof sketch: apply the convexity inequality to the segment from `x` to `y` and then rewrite
-- the resulting bound in terms of the directional derivative along `y - x`.
/-- Source clause (ii): the directional derivative toward `y` controls the secant
increment from `x` to `y`. -/
theorem directionalDerivative_add_value_le
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) := by
  let _ := hconv
  by_cases hy : y ∈ effectiveDomain f
  · have htest :
        f′(x; y - x) ≤ directionalDifferenceQuotient f x (y - x) ⟨1, by norm_num⟩ := by
      -- Test the defining infimum at the unit step, which lands exactly at `y`.
      rw [directionalDerivative]
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hquot :
        directionalDifferenceQuotient f x (y - x) ⟨1, by norm_num⟩ =
          (f y : EReal) - (f x : EReal) := by
      -- Evaluate the quotient at `α = 1`, where the ray endpoint is exactly `y`.
      simp [directionalDifferenceQuotient, sub_eq_add_neg]
    have hle : f′(x; y - x) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hquot] using htest
    exact (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).1 hle
  · have hfy_top : (f y : EReal) = ⊤ := by
      exact top_unique (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
    -- Outside the effective domain, the target value is `⊤`.
    simp [hfy_top]

-- Proof sketch: apply clause (ii) twice, once at `x` toward `y` and once at `y` toward `x`, then
-- combine the two inequalities.
/-- Source clause (iii): at two effective-domain points, opposite directional
derivatives along the connecting segment bound each other. -/
theorem directionalDerivative_le_neg_swap
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    f′(x; y - x) ≤ -f′(y; x - y) := by
  have hxy : f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) :=
    directionalDerivative_add_value_le f hconv hx y
  have hyx : f′(y; x - y) + (f y : EReal) ≤ (f x : EReal) :=
    directionalDerivative_add_value_le f hconv hy x
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hsecant_upper : f′(x; y - x) ≤ (f y : EReal) - (f x : EReal) := by
    -- Rewrite the first secant estimate into subtraction form.
    exact (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).2 hxy
  have hsecant_lower_value : (f y : EReal) ≤ (f x : EReal) - f′(y; x - y) := by
    -- Rewrite the second secant estimate so the same secant gap appears on the left.
    exact (EReal.le_sub_iff_add_le (.inr hfx_bot) (.inr hfx_top)).2
      (by simpa [add_comm] using hyx)
  have hsecant_lower : (f y : EReal) - (f x : EReal) ≤ -f′(y; x - y) := by
    exact (EReal.sub_le_iff_le_add (.inl hfx_bot) (.inl hfx_top)).2
      (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsecant_lower_value)
  exact le_trans hsecant_upper hsecant_lower

/-- Directional-derivative helper: if the ray endpoint is finite, then the directional difference
quotient is the corresponding real quotient viewed in `EReal`. -/
private theorem directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
    {x y : H} (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) • y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y a =
      ((((f (x + (a : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) /
        (a : ℝ) : ℝ) : EReal) := by
  -- Finite endpoint values let the quotient collapse to an ordinary real expression.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp ha)
  have hxa_bot : (f (x + (a : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) • y) : EReal) from
      (f (x + (a : ℝ) • y)).2)
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Directional-derivative helper: if the ray endpoint leaves the effective domain, then the
directional difference quotient is `⊤`. -/
private theorem directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
    {x y : H} (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) • y ∉ effectiveDomain f) :
    directionalDifferenceQuotient f x y a = ⊤ := by
  -- Once the endpoint value is `⊤`, the positive denominator preserves `⊤`.
  have hxa_top : (f (x + (a : ℝ) • y) : EReal) = ⊤ := by
    exact top_unique (not_lt.mp (by simpa [mem_effectiveDomain_iff] using ha))
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have ha_pos : (0 : EReal) < (a : ℝ) := by
    exact_mod_cast a.2
  have ha_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  change ((f (x + (a : ℝ) • y) : EReal) - (f x : EReal)) / (a : ℝ) = ⊤
  rw [hxa_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top ha_pos ha_top]

/-- Directional-derivative helper: a smaller positive point on a ray is the convex combination of
the base point and a larger ray endpoint with coefficient `a / b`. -/
private theorem rayPoint_eq_convexCombinationEndpoint
    (x y : H) {a b : ℝ} (hb : 0 < b) :
    x + a • y = (a / b) • (x + b • y) + (1 - a / b) • x := by
  -- Rewrite the smaller ray point into the affine shape consumed by convexity of the domain.
  have hab : (a / b) * b = a := by
    field_simp [hb.ne']
  calc
    x + a • y = x + (((a / b) * b) • y) := by rw [hab]
    _ = (1 : ℝ) • x + (a / b) • (b • y) := by simp [smul_smul]
    _ = ((a / b) + (1 - a / b)) • x + (a / b) • (b • y) := by simp
    _ = (a / b) • x + (1 - a / b) • x + (a / b) • (b • y) := by
          rw [add_smul]
    _ = (a / b) • x + ((a / b) • (b • y)) + (1 - a / b) • x := by
          abel_nf
    _ = (a / b) • (x + b • y) + (1 - a / b) • x := by
          simp [smul_add, add_assoc]

/-- Directional-derivative helper: once a positive ray endpoint stays in the effective domain, every
smaller positive point on the same ray stays there as well. -/
private theorem rayPoint_mem_effectiveDomain_of_le
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) {a b : Set.Ioi (0 : ℝ)}
    (hab : (a : ℝ) ≤ (b : ℝ))
    (hbmem : x + (b : ℝ) • y ∈ effectiveDomain f) :
    x + (a : ℝ) • y ∈ effectiveDomain f := by
  -- Convexity of the effective domain lets us contract the larger ray witness back toward `x`.
  rw [rayPoint_eq_convexCombinationEndpoint x y b.2]
  have hratio_nonneg : 0 ≤ (a : ℝ) / (b : ℝ) := by
    exact div_nonneg a.2.le b.2.le
  have hratio_le_one : (a : ℝ) / (b : ℝ) ≤ 1 := by
    exact (div_le_one b.2).2 hab
  exact hconv.convex_effectiveDomain hbmem hx hratio_nonneg
    (sub_nonneg.mpr hratio_le_one) (by ring)

/-- Directional-derivative helper: midpoint convexity of the finite directional difference quotients
comes from convexity of the real-valued representative on the effective domain. -/
private theorem directionalDifferenceQuotient_midpoint_le
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (u v : H) (a : Set.Ioi (0 : ℝ))
    (hu : x + (a : ℝ) • u ∈ effectiveDomain f)
    (hv : x + (a : ℝ) • v ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x ((1 / 2 : ℝ) • (u + v)) a ≤
      (1 / 2 : ℝ) • directionalDifferenceQuotient f x u a +
        (1 / 2 : ℝ) • directionalDifferenceQuotient f x v a := by
  have hmid_combo :
      (1 / 2 : ℝ) • (x + (a : ℝ) • u) + (1 / 2 : ℝ) • (x + (a : ℝ) • v) ∈ effectiveDomain f := by
    -- Convexity keeps the midpoint of the two ray endpoints inside the effective domain.
    exact hconv.convex_effectiveDomain hu hv (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hmid_eq :
      (1 / 2 : ℝ) • (x + (a : ℝ) • u) + (1 / 2 : ℝ) • (x + (a : ℝ) • v) =
        x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v)) := by
    calc
      (1 / 2 : ℝ) • (x + (a : ℝ) • u) + (1 / 2 : ℝ) • (x + (a : ℝ) • v)
          = ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • ((a : ℝ) • u)) +
              ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • ((a : ℝ) • v)) := by
                rw [smul_add, smul_add]
      _ = ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x) +
            ((1 / 2 : ℝ) • ((a : ℝ) • u) + (1 / 2 : ℝ) • ((a : ℝ) • v)) := by
              abel_nf
      _ = x + ((1 / 2 : ℝ) • ((a : ℝ) • u) + (1 / 2 : ℝ) • ((a : ℝ) • v)) := by
            rw [← add_smul]
            norm_num
      _ = x + (((1 / 2 : ℝ) * (a : ℝ)) • u + ((1 / 2 : ℝ) * (a : ℝ)) • v) := by
            simp [smul_smul]
      _ = x + (((1 / 2 : ℝ) * (a : ℝ)) • (u + v)) := by
            rw [← smul_add]
      _ = x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v)) := by
            simp [smul_smul, mul_comm]
  have hmid :
      x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v)) ∈ effectiveDomain f := by
    rw [← hmid_eq]
    exact hmid_combo
  have hineq_combo :
      (f ((1 / 2 : ℝ) • (x + (a : ℝ) • u) + (1 / 2 : ℝ) • (x + (a : ℝ) • v)) : EReal).toReal ≤
        (1 / 2 : ℝ) * (f (x + (a : ℝ) • u) : EReal).toReal +
          (1 / 2 : ℝ) * (f (x + (a : ℝ) • v) : EReal).toReal := by
    -- The real-valued representative is convex on the effective domain.
    exact hconv.toReal_convexOn_effectiveDomain.2 hu hv (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hineq :
      (f (x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v))) : EReal).toReal ≤
        (1 / 2 : ℝ) * (f (x + (a : ℝ) • u) : EReal).toReal +
          (1 / 2 : ℝ) * (f (x + (a : ℝ) • v) : EReal).toReal := by
    rw [← hmid_eq]
    exact hineq_combo
  have hsub :
      (f (x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v))) : EReal).toReal - (f x : EReal).toReal ≤
        (1 / 2 : ℝ) *
            ((f (x + (a : ℝ) • u) : EReal).toReal - (f x : EReal).toReal) +
          (1 / 2 : ℝ) *
            ((f (x + (a : ℝ) • v) : EReal).toReal - (f x : EReal).toReal) := by
    -- Subtract the common base value before normalizing by the step size.
    linarith
  have hreal :
      (((f (x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v))) : EReal).toReal -
          (f x : EReal).toReal) / (a : ℝ)) ≤
        (1 / 2 : ℝ) *
            (((f (x + (a : ℝ) • u) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ)) +
          (1 / 2 : ℝ) *
            (((f (x + (a : ℝ) • v) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ)) := by
    -- Divide the finite midpoint inequality by the positive step size.
    have hdiv :
        ((f (x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v))) : EReal).toReal - (f x : EReal).toReal) /
            (a : ℝ) ≤
          ((1 / 2 : ℝ) * ((f (x + (a : ℝ) • u) : EReal).toReal - (f x : EReal).toReal) +
              (1 / 2 : ℝ) * ((f (x + (a : ℝ) • v) : EReal).toReal - (f x : EReal).toReal)) /
            (a : ℝ) := by
      exact (div_le_div_iff_of_pos_right a.2).2 hsub
    simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hdiv
  -- Collapse the three finite quotients to their real representatives and cast the real estimate.
  rw [directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
      f hx a hmid,
    directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx a hu,
    directionalDifferenceQuotient_eq_coe_toReal_of_mem_effectiveDomain f hx a hv]
  have hcast :
      ((((f (x + (a : ℝ) • ((1 / 2 : ℝ) • (u + v))) : EReal).toReal -
            (f x : EReal).toReal) /
          (a : ℝ) : ℝ) : EReal) ≤
        (((((1 / 2 : ℝ) *
              (((f (x + (a : ℝ) • u) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ)) +
            (1 / 2 : ℝ) *
              (((f (x + (a : ℝ) • v) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ))) :
            ℝ) : EReal)) := by
    exact_mod_cast hreal
  simpa [EReal.real_smul_def, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc]
    using hcast

/-- Directional-derivative helper: a directional derivative value in the domain forces some
positive ray point to stay in the effective domain. -/
private theorem exists_ray_point_mem_effectiveDomain_of_mem_dom_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) {y : H}
    (hy : y ∈ dom (directionalDerivative f x)) :
    ∃ a : Set.Ioi (0 : ℝ), x + (a : ℝ) • y ∈ effectiveDomain f := by
  let _ := hconv
  -- If every positive ray point left the effective domain, the derivative would be `⊤`.
  by_contra hno
  have hquot : directionalDifferenceQuotient f x y = fun _ ↦ (⊤ : EReal) := by
    funext a
    exact directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
      f hx a (fun ha ↦ hno ⟨a, ha⟩)
  have htop : f′(x; y) = ⊤ := by
    rw [directionalDerivative, hquot]
    simp
  exact (not_mem_dom_iff (directionalDerivative f x) y).2 htop hy

/-- Directional-derivative helper: midpoint convexity of the quotient family survives in the limit
once both directional derivative values are finite above. -/
private theorem directionalDerivative_midpoint_le_of_mem_dom
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) {u v : H}
    (hu : u ∈ dom (directionalDerivative f x))
    (hv : v ∈ dom (directionalDerivative f x)) :
    f′(x; (1 / 2 : ℝ) • (u + v)) ≤
      (1 / 2 : ℝ) • f′(x; u) + (1 / 2 : ℝ) • f′(x; v) := by
  let qmid : ℝ → EReal := fun α ↦
    ((f (x + α • ((1 / 2 : ℝ) • (u + v))) : EReal) - (f x : EReal)) / α
  let qu : ℝ → EReal := fun α ↦ ((f (x + α • u) : EReal) - (f x : EReal)) / α
  let qv : ℝ → EReal := fun α ↦ ((f (x + α • v) : EReal) - (f x : EReal)) / α
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by
    norm_num
  have hqu_tendsto :
      Filter.Tendsto qu (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; u))) := by
    -- Identify the `u`-quotients with the canonical derivative limit.
    simpa [qu] using directional_difference_quotient_tendsto_directionalDerivative f hconv hx u
  have hqv_tendsto :
      Filter.Tendsto qv (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; v))) := by
    -- Identify the `v`-quotients with the canonical derivative limit.
    simpa [qv] using directional_difference_quotient_tendsto_directionalDerivative f hconv hx v
  have hqmid_tendsto :
      Filter.Tendsto qmid (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (f′(x; (1 / 2 : ℝ) • (u + v)))) := by
    -- The midpoint-direction quotient converges to the midpoint directional derivative.
    simpa [qmid] using
      directional_difference_quotient_tendsto_directionalDerivative
        f hconv hx ((1 / 2 : ℝ) • (u + v))
  have hqu_half_tendsto :
      Filter.Tendsto (fun α ↦ (1 / 2 : ℝ) • qu α) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) • f′(x; u))) := by
    -- Scale the `u`-limit by the fixed positive midpoint coefficient.
    simpa [EReal.real_smul_def] using
      (EReal.Tendsto.const_mul hqu_tendsto
        (Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)))
        (Or.inl (EReal.coe_ne_top (1 / 2 : ℝ))))
  have hqv_half_tendsto :
      Filter.Tendsto (fun α ↦ (1 / 2 : ℝ) • qv α) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) • f′(x; v))) := by
    -- Scale the `v`-limit by the same midpoint coefficient.
    simpa [EReal.real_smul_def] using
      (EReal.Tendsto.const_mul hqv_tendsto
        (Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)))
        (Or.inl (EReal.coe_ne_top (1 / 2 : ℝ))))
  have hu_ne_top : f′(x; u) ≠ ⊤ :=
    (mem_dom_iff_ne_top (directionalDerivative f x) u).1 hu
  have hv_ne_top : f′(x; v) ≠ ⊤ :=
    (mem_dom_iff_ne_top (directionalDerivative f x) v).1 hv
  have hhalf_nonneg_ereal : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
    exact_mod_cast hhalf_nonneg
  have hqu_half_ne_top : (1 / 2 : ℝ) • f′(x; u) ≠ ⊤ := by
    rw [EReal.real_smul_def, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg_ereal,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hu_ne_top⟩
  have hqv_half_ne_top : (1 / 2 : ℝ) • f′(x; v) ≠ ⊤ := by
    rw [EReal.real_smul_def, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg_ereal,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hv_ne_top⟩
  have hrhs_tendsto :
      Filter.Tendsto (fun α ↦ (1 / 2 : ℝ) • qu α + (1 / 2 : ℝ) • qv α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) • f′(x; u) + (1 / 2 : ℝ) • f′(x; v))) := by
    -- Addition is continuous at this finite-above limit pair, so the midpoint-scaled limits add.
    let p : ℝ → EReal × EReal := fun α ↦ ((1 / 2 : ℝ) • qu α, (1 / 2 : ℝ) • qv α)
    have hp_tendsto :
        Filter.Tendsto p (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (((1 / 2 : ℝ) • f′(x; u), (1 / 2 : ℝ) • f′(x; v)))) := by
      exact hqu_half_tendsto.prodMk_nhds hqv_half_tendsto
    exact
      (EReal.continuousAt_add (Or.inl hqu_half_ne_top) (Or.inr hqv_half_ne_top)).tendsto.comp
        hp_tendsto
  rcases exists_ray_point_mem_effectiveDomain_of_mem_dom_directionalDerivative
      f hconv hx hu with ⟨au, hau⟩
  rcases exists_ray_point_mem_effectiveDomain_of_mem_dom_directionalDerivative
      f hconv hx hv with ⟨av, hav⟩
  have hsmall :
      qmid ≤ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun α ↦ (1 / 2 : ℝ) • qu α + (1 / 2 : ℝ) • qv α := by
    -- Shrink to a common positive interval where both rays stay in the effective domain.
    have hmin_pos : 0 < min (au : ℝ) (av : ℝ) := by
      exact lt_min au.2 av.2
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hmin_pos)] with α hα
    have hα_pos : 0 < α := hα.1
    have hα_le_u : α ≤ (au : ℝ) := by
      exact le_trans (le_of_lt hα.2) (min_le_left _ _)
    have hα_le_v : α ≤ (av : ℝ) := by
      exact le_trans (le_of_lt hα.2) (min_le_right _ _)
    let aα : Set.Ioi (0 : ℝ) := ⟨α, hα_pos⟩
    have huα : x + α • u ∈ effectiveDomain f := by
      have huα' : x + (aα : ℝ) • u ∈ effectiveDomain f := by
        exact rayPoint_mem_effectiveDomain_of_le f hconv hx hα_le_u hau
      simpa [aα] using huα'
    have hvα : x + α • v ∈ effectiveDomain f := by
      have hvα' : x + (aα : ℝ) • v ∈ effectiveDomain f := by
        exact rayPoint_mem_effectiveDomain_of_le f hconv hx hα_le_v hav
      simpa [aα] using hvα'
    -- Apply the finite quotient midpoint inequality on that common interval.
    simpa [qmid, qu, qv, directionalDifferenceQuotient, smul_add, smul_smul, mul_comm,
      mul_left_comm, mul_assoc] using
      directionalDifferenceQuotient_midpoint_le f hconv hx u v ⟨α, hα_pos⟩ huα hvα
  exact le_of_tendsto_of_tendsto hqmid_tendsto hrhs_tendsto hsmall

/-- Directional-derivative helper: the directional derivative is positively homogeneous in its
direction variable at every effective-domain base point. -/
private theorem directionalDerivative_positivelyHomogeneous
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    PositivelyHomogeneous (directionalDerivative f x) := by
  intro a ha y
  -- Rewrite positive scaling through the canonical rescaling theorem.
  simpa [EReal.real_smul_def, mul_comm] using directionalDerivative_smul_of_pos f hconv hx ha

/-- Directional-derivative helper: midpoint control and positive homogeneity combine to give
subadditivity of the directional derivative on its natural domain. -/
private theorem directionalDerivative_subadditive
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    Subadditive (directionalDerivative f x) := by
  let g := directionalDerivative f x
  let hph := directionalDerivative_positivelyHomogeneous f hconv hx
  intro u v hu hv
  have hhalf_pos : 0 < (1 / 2 : ℝ) := by
    norm_num
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have htwo_nonneg : 0 ≤ (2 : ℝ) := by
    norm_num
  have hu_ne_top : g u ≠ ⊤ := (mem_dom_iff_ne_top g u).1 hu
  have hv_ne_top : g v ≠ ⊤ := (mem_dom_iff_ne_top g v).1 hv
  have hmid_le :
      g ((1 / 2 : ℝ) • (u + v)) ≤ (1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v :=
    directionalDerivative_midpoint_le_of_mem_dom f hconv hx hu hv
  have hhalf_nonneg_ereal : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
    exact_mod_cast (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hgu_half_ne_top : (1 / 2 : ℝ) • g u ≠ ⊤ := by
    rw [EReal.real_smul_def, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg_ereal,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hu_ne_top⟩
  have hgv_half_ne_top : (1 / 2 : ℝ) • g v ≠ ⊤ := by
    rw [EReal.real_smul_def, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg_ereal,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hv_ne_top⟩
  have hmid_dom : ((1 / 2 : ℝ) • (u + v)) ∈ dom g := by
    -- The midpoint value is finite above because it is bounded by a finite-above right-hand side.
    rw [mem_dom_iff_ne_top]
    intro htop
    have hsum_ne_top :
        (1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v ≠ ⊤ :=
      EReal.add_ne_top hgu_half_ne_top hgv_half_ne_top
    have hsum_top : (1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v = ⊤ := by
      have htop_le : (⊤ : EReal) ≤ (1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v := by
        rw [← htop]
        exact hmid_le
      exact le_antisymm le_top htop_le
    exact hsum_ne_top hsum_top
  have hsum_eq :
      g (u + v) = (2 : ℝ) • g ((1 / 2 : ℝ) • (u + v)) := by
    -- Positive homogeneity recovers the full sum from its midpoint rescaling.
    simpa [g, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      hph htwo_pos ((1 / 2 : ℝ) • (u + v))
  have hscale_le :
      (2 : ℝ) • g ((1 / 2 : ℝ) • (u + v)) ≤
        (2 : ℝ) • ((1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v) := by
    -- Multiply the midpoint inequality by the positive scalar `2`.
    simpa [EReal.real_smul_def] using
      mul_le_mul_of_nonneg_left hmid_le (by exact_mod_cast htwo_nonneg)
  have htwo_half : (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) = 1 := by
    rw [← EReal.coe_mul]
    norm_num
  have htwo_nonneg_ereal : (0 : EReal) ≤ ((2 : ℝ) : EReal) := by
    exact_mod_cast htwo_nonneg
  calc
    g (u + v) = (2 : ℝ) • g ((1 / 2 : ℝ) • (u + v)) := hsum_eq
    _ ≤ (2 : ℝ) • ((1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g v) := hscale_le
    _ = g u + g v := by
          rw [EReal.real_smul_def, EReal.real_smul_def, EReal.real_smul_def]
          rw [EReal.left_distrib_of_nonneg_of_ne_top htwo_nonneg_ereal (EReal.coe_ne_top (2 : ℝ))]
          rw [← mul_assoc, ← mul_assoc, htwo_half, one_mul, one_mul]

/-- Directional-derivative helper: the directional derivative in the zero direction is zero at an
effective-domain point. -/
private theorem directionalDerivative_zero_of_mem_effectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    f′(x; 0) = 0 := by
  let _ := hconv
  rw [directionalDerivative]
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hquot : directionalDifferenceQuotient f x (0 : H) = fun _ ↦ (0 : EReal) := by
    funext α
    -- The zero direction keeps the ray point fixed at `x`, so every positive quotient is `0`.
    simp [directionalDifferenceQuotient, EReal.sub_self hfx_top hfx_bot]
  simp [hquot]

/-- Directional-derivative helper: subadditivity and positive homogeneity imply convexity of the
directional derivative on its natural domain. -/
private theorem directionalDerivativeConvexOnDom
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    _root_.ConvexOn ℝ (dom (directionalDerivative f x)) (directionalDerivative f x) := by
  let g := directionalDerivative f x
  let hph := directionalDerivative_positivelyHomogeneous f hconv hx
  let hsub := directionalDerivative_subadditive f hconv hx
  have hzero : g 0 = 0 := by
    simpa [g] using directionalDerivative_zero_of_mem_effectiveDomain f hconv hx
  refine ⟨?_, ?_⟩
  · intro u hu v hv a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by
        linarith
      subst ha0
      subst hb1
      simpa using hv
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by
        linarith
      subst hb0
      subst ha1
      simpa using hu
    have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
    have hau : a • u ∈ dom g := by
      rw [mem_dom_iff_ne_top]
      rw [show g (a • u) = a • g u by simpa [g] using hph ha_pos u]
      rw [EReal.real_smul_def, EReal.mul_ne_top]
      have ha_nonneg_ereal : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha
      refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ha_nonneg_ereal,
        Or.inl (EReal.coe_ne_top a), Or.inr ((mem_dom_iff_ne_top g u).1 hu)⟩
    have hbv : b • v ∈ dom g := by
      rw [mem_dom_iff_ne_top]
      rw [show g (b • v) = b • g v by simpa [g] using hph hb_pos v]
      rw [EReal.real_smul_def, EReal.mul_ne_top]
      have hb_nonneg_ereal : (0 : EReal) ≤ (b : EReal) := by
        exact_mod_cast hb
      refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl hb_nonneg_ereal,
        Or.inl (EReal.coe_ne_top b), Or.inr ((mem_dom_iff_ne_top g v).1 hv)⟩
    rw [mem_dom_iff_ne_top]
    intro htop
    have hsum_ne_top : g (a • u) + g (b • v) ≠ ⊤ :=
      EReal.add_ne_top ((mem_dom_iff_ne_top g (a • u)).1 hau) ((mem_dom_iff_ne_top g (b • v)).1 hbv)
    have hsum_top : g (a • u) + g (b • v) = ⊤ := by
      apply le_antisymm le_top
      simpa [htop] using hsub hau hbv
    exact hsum_ne_top hsum_top
  · intro u hu v hv a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by
        linarith
      subst ha0
      subst hb1
      simp
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by
        linarith
      subst hb0
      subst ha1
      simp
    have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
    have hau : a • u ∈ dom g := by
      rw [mem_dom_iff_ne_top]
      rw [show g (a • u) = a • g u by simpa [g] using hph ha_pos u]
      rw [EReal.real_smul_def, EReal.mul_ne_top]
      have ha_nonneg_ereal : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha
      refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ha_nonneg_ereal,
        Or.inl (EReal.coe_ne_top a), Or.inr ((mem_dom_iff_ne_top g u).1 hu)⟩
    have hbv : b • v ∈ dom g := by
      rw [mem_dom_iff_ne_top]
      rw [show g (b • v) = b • g v by simpa [g] using hph hb_pos v]
      rw [EReal.real_smul_def, EReal.mul_ne_top]
      have hb_nonneg_ereal : (0 : EReal) ≤ (b : EReal) := by
        exact_mod_cast hb
      refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl hb_nonneg_ereal,
        Or.inl (EReal.coe_ne_top b), Or.inr ((mem_dom_iff_ne_top g v).1 hv)⟩
    -- Rewrite the convex combination into a sum of scaled directions and apply subadditivity.
    calc
      g (a • u + b • v) ≤ g (a • u) + g (b • v) := hsub hau hbv
      _ = a • g u + b • g v := by
            rw [show g (a • u) = a • g u by simpa [g] using hph ha_pos u]
            rw [show g (b • v) = b • g v by simpa [g] using hph hb_pos v]

/-- Directional-derivative helper: if a positive ray point lies in the effective domain, then the
direction belongs to the cone generated by the translated effective domain. -/
private theorem direction_mem_cone_of_ray_point_mem_effectiveDomain
    {x : H} (hx : x ∈ effectiveDomain f) {y : H} {a : ℝ} (ha : 0 < a)
    (hy : x + a • y ∈ effectiveDomain f) :
    y ∈ Set.cone (effectiveDomain f - ({x} : Set H)) := by
  let _ := hx
  -- The translated ray point is a cone generator, and positive rescaling recovers the direction.
  change y ∈ (ConvexCone.hull ℝ (effectiveDomain f - ({x} : Set H)) : Set H)
  have hdiff :
      x + a • y - x ∈ effectiveDomain f - ({x} : Set H) := by
    refine Set.mem_sub.mpr ⟨x + a • y, hy, x, by simp, ?_⟩
    simp
  have hscaled :
      a⁻¹ • (x + a • y - x) ∈
        (ConvexCone.hull ℝ (effectiveDomain f - ({x} : Set H)) : Set H) :=
    (ConvexCone.hull ℝ (effectiveDomain f - ({x} : Set H))).smul_mem (inv_pos.mpr ha)
      (ConvexCone.subset_hull hdiff)
  simpa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using hscaled

/-- Directional-derivative helper: if no positive ray point remains in the effective domain, then
the directional derivative is `⊤`. -/
private theorem directionalDerivative_eq_top_of_no_ray_point_mem_effectiveDomain
    {x : H} (hx : x ∈ effectiveDomain f) {y : H}
    (hy : ∀ a : Set.Ioi (0 : ℝ), x + (a : ℝ) • y ∉ effectiveDomain f) :
    f′(x; y) = ⊤ := by
  -- Every positive-ray quotient is already `⊤`, so their infimum is still `⊤`.
  have hquot :
      directionalDifferenceQuotient f x y = fun _ ↦ (⊤ : EReal) := by
    funext a
    exact directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
      f hx a (hy a)
  rw [directionalDerivative, hquot]
  simp

/-- Directional-derivative helper: directions in the cone generated by the translated effective
domain belong to the domain of the directional derivative. -/
private theorem mem_dom_directionalDerivative_of_mem_cone_effectiveDomain_sub_singleton
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) {y : H}
    (hy : y ∈ Set.cone (effectiveDomain f - ({x} : Set H))) :
    y ∈ dom (directionalDerivative f x) := by
  -- Extract a positive cone witness and transport the finite secant bound along positive scaling.
  have htranslate_convex : Convex ℝ (effectiveDomain f - ({x} : Set H)) := by
    exact hconv.convex_effectiveDomain.sub (convex_singleton x)
  change y ∈ (ConvexCone.hull ℝ (effectiveDomain f - ({x} : Set H)) : Set H) at hy
  rcases (ConvexCone.mem_hull_of_convex htranslate_convex).1 hy with ⟨a, ha, hay⟩
  rcases Set.mem_smul_set.mp hay with ⟨z, hz, rfl⟩
  rcases Set.mem_sub.mp hz with ⟨w, hw, x', hx', hzx⟩
  have hx' : x' = x := by simpa using hx'
  subst x'
  have hz_dir : z = w - x := by simpa using hzx.symm
  subst z
  have hw_dom : w - x ∈ dom (directionalDerivative f x) := by
    rw [mem_dom_iff]
    have hbound : f′(x; w - x) + (f x : EReal) ≤ (f w : EReal) :=
      directionalDerivative_add_value_le f hconv hx w
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hsecant :
        f′(x; w - x) ≤ (f w : EReal) - (f x : EReal) := by
      exact (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).2 hbound
    have hgap_ne_top : (f w : EReal) - (f x : EReal) ≠ ⊤ := by
      have hw_top : (f w : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hw)
      have hw_bot : (f w : EReal) ≠ ⊥ := (f w).property.ne'
      rw [← EReal.coe_toReal hw_top hw_bot, ← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_sub]
      exact EReal.coe_ne_top _
    rw [lt_top_iff_ne_top]
    intro htop
    exact hgap_ne_top (le_antisymm le_top (by simpa [htop] using hsecant))
  rw [mem_dom_iff_ne_top] at hw_dom ⊢
  rw [directionalDerivative_smul_of_pos f hconv hx ha, EReal.mul_ne_top]
  refine ⟨Or.inr (by exact_mod_cast ha.le), Or.inr (EReal.coe_ne_bot a),
    Or.inl hw_dom, Or.inr (EReal.coe_ne_top a)⟩

-- Proof sketch: use Proposition 9.27 to get monotonicity of the directional difference quotients,
-- then derive positive homogeneity and subadditivity from the infimum formula.
/-- Source clause (iv): for a convex function, the directional derivative map at a
fixed base point is sublinear. -/
theorem sublinear_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    Sublinear (directionalDerivative f x) := by
  -- Combine the scaling and midpoint-control helpers proved above.
  exact ⟨directionalDerivative_positivelyHomogeneous f hconv hx,
    directionalDerivative_subadditive f hconv hx⟩

variable {f}

/-- Source clause (v): an extended-real-valued map is proper in the Chapter 17 sense when its
finite-value domain is nonempty. This is weaker than the Chapter 1 owner `IsProper`, which also
forbids the value `⊥` everywhere. -/
def IsProperInChapter17Sense (g : H → EReal) : Prop :=
  (dom g).Nonempty

/-- Source clause (v): an extended-real-valued map is convex in the Chapter 17 sense when it is
convex on its finite-value domain. -/
def IsConvexInChapter17Sense (g : H → EReal) : Prop :=
  _root_.ConvexOn ℝ (dom g) g

/-- Unfolding companion for `IsProperInChapter17Sense`. -/
@[simp] theorem isProperInChapter17Sense_iff {H : Type*} (g : H → EReal) :
    IsProperInChapter17Sense g ↔ (dom g).Nonempty := by
  rfl

/-- Unfolding companion for `IsConvexInChapter17Sense`. -/
@[simp] theorem isConvexInChapter17Sense_iff (g : H → EReal) :
    IsConvexInChapter17Sense g ↔ _root_.ConvexOn ℝ (dom g) g := by
  rfl

-- Proof sketch: at an effective-domain point, every zero-direction difference quotient is the
-- finite value `(f x - f x) / α = 0`, so the defining infimum is `0`.
/-- Source clause (iv): at an effective-domain point, the directional derivative in
the zero direction is `0`. -/
theorem directionalDerivative_zero
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    f′(x; 0) = 0 := by
  exact directionalDerivative_zero_of_mem_effectiveDomain f hconv hx

/-- Directional-derivative helper: the finite-value domain of the directional derivative is exactly
the cone generated by the translated effective domain. -/
private theorem dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton_aux
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    dom (directionalDerivative f x) =
      Set.cone (effectiveDomain f - ({x} : Set H)) := by
  -- The finite-value domain is exactly the set of directions with a positive effective-domain ray.
  ext y
  constructor
  · intro hy
    rcases exists_ray_point_mem_effectiveDomain_of_mem_dom_directionalDerivative
        f hconv hx hy with ⟨a, ha⟩
    exact direction_mem_cone_of_ray_point_mem_effectiveDomain f hx a.2 ha
  · intro hy
    exact mem_dom_directionalDerivative_of_mem_cone_effectiveDomain_sub_singleton
      f hconv hx hy

-- Semantic recall note: `lean_leansearch` timed out on this clause, so the repair follows the
-- same-file Chapter 17 API instead. At an effective-domain boundary point, `f′(x; ·)` may
-- legitimately take the values `⊥` and `⊤` on different rays, so clause (v) uses the local
-- Chapter 17 predicates `IsProperInChapter17Sense` and `IsConvexInChapter17Sense` rather than the
-- stronger Chapter 1 owner `IsProper`.
/-- Proposition 17.2: companion bundle for clause (v). The directional-derivative map `f′(x; ·)`
has nonempty
natural domain, is convex on that natural domain, and its domain is the cone generated by the
translated effective domain. -/
theorem directionalDerivative_dom_nonempty_convexOn_dom_and_dom_eq_cone
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    (dom (directionalDerivative f x)).Nonempty ∧
      _root_.ConvexOn ℝ (dom (directionalDerivative f x)) (directionalDerivative f x) ∧
      dom (directionalDerivative f x) =
        Set.cone (effectiveDomain f - ({x} : Set H)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Use the zero direction as a canonical witness in the natural domain.
    refine ⟨0, ?_⟩
    rw [mem_dom_iff_ne_top]
    simp [directionalDerivative_zero hconv hx]
  · -- The convexity-on-domain clause was already established in the local API.
    exact directionalDerivativeConvexOnDom f hconv hx
  · -- The domain description is exactly the previously proved cone formula.
    exact dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton_aux hconv hx

/-- Companion for clause (v): `f′(x; ·)` has nonempty natural domain. -/
theorem directionalDerivative_dom_nonempty
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    (dom (directionalDerivative f x)).Nonempty := by
  -- Project the nonempty-domain witness from the bundled clause-(v) companion.
  exact (directionalDerivative_dom_nonempty_convexOn_dom_and_dom_eq_cone hconv hx).1

/-- Companion for clause (v): the source-facing convexity clause is expressed in Lean as
convexity of `f′(x; ·)` on its natural domain. -/
theorem directionalDerivative_convexOn_dom
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    _root_.ConvexOn ℝ (dom (directionalDerivative f x)) (directionalDerivative f x) := by
  -- Project the convexity-on-domain part of the direct clause-(v) translation.
  exact (directionalDerivative_dom_nonempty_convexOn_dom_and_dom_eq_cone hconv hx).2.1

/-- Companion: a real-linear minorant rules out `⊥` values of the directional derivative, so
together with the nonempty-domain clause it upgrades clause (v) to the stronger Chapter 1 owner
`IsProper`. This extra upgrade is not part of the source statement itself. -/
theorem directionalDerivative_isProper_chap01_of_linear_minorant
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (ℓ : H →ₗ[ℝ] ℝ)
    (hℓ : ∀ y : H, ((ℓ y : ℝ) : EReal) ≤ f′(x; y)) :
    IsProper (directionalDerivative f x) := by
  refine ⟨?_, directionalDerivative_dom_nonempty hconv hx⟩
  intro y hy
  have hle : ((ℓ y : ℝ) : EReal) ≤ (⊥ : EReal) := by
    simpa [hy] using hℓ y
  exact EReal.coe_ne_bot (ℓ y) (le_antisymm hle bot_le)

/-- Compatibility companion: the older Chapter 1 `IsProper` surface for `f′(x; ·)` is available
only after providing an explicit real-linear minorant. This avoids baking that stronger owner into
the clause-(v) repair while giving later items a discoverable upgrade theorem. -/
theorem directionalDerivative_isProper_chap01
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hminor : ∃ ℓ : H →ₗ[ℝ] ℝ, ∀ y : H, ((ℓ y : ℝ) : EReal) ≤ f′(x; y)) :
    IsProper (directionalDerivative f x) := by
  rcases hminor with ⟨ℓ, hℓ⟩
  exact directionalDerivative_isProper_chap01_of_linear_minorant hconv hx ℓ hℓ

-- Proof sketch: show that finite directional derivative values correspond exactly to directions in
-- the cone generated by `effectiveDomain f - x`.
/-- Companion for clause (v): the domain of the directional derivative is the cone
generated by the translated effective domain. -/
theorem dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    dom (directionalDerivative f x) =
      Set.cone (effectiveDomain f - ({x} : Set H)) := by
  exact dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton_aux hconv hx

/-- Companion for clause (v): the domain of `f′(x; ·)` is the cone generated by the translated
effective domain, in a name aligned with the other directional-derivative companions. -/
theorem directionalDerivative_dom_eq_cone_effectiveDomain_sub_singleton
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    dom (directionalDerivative f x) =
      Set.cone (effectiveDomain f - ({x} : Set H)) :=
  dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton hconv hx

-- Proof sketch: use the core assumption to obtain a symmetric effective-domain segment
-- `[x - β • y, x + β • y]` for every direction `y`, then bound the directional derivative above
-- and below by finite secant quotients.
/-- Source clause (vi): at a core point of the effective domain, every directional
derivative value is a real number. -/
theorem directionalDerivative_eq_coe_real_of_mem_core
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcore : x ∈ Set.core (effectiveDomain f)) :
    ∀ y : H, ∃ r : ℝ, f′(x; y) = (r : EReal) := by
  rcases Set.mem_core_iff.mp hxcore with ⟨hx, hcone_univ⟩
  let g := directionalDerivative f x
  let hsub := (sublinear_directionalDerivative f hconv hx).subadditive
  have hzero : g 0 = 0 := by
    simpa [g] using directionalDerivative_zero hconv hx
  have hdom_univ : dom g = (Set.univ : Set H) := by
    rw [show dom g = dom (directionalDerivative f x) by rfl]
    rw [dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton hconv hx, hcone_univ]
  intro y
  have hy_dom : y ∈ dom g := by
    simp [hdom_univ]
  have hnegy_dom : -y ∈ dom g := by
    simp [hdom_univ]
  have hy_ne_top : g y ≠ ⊤ := (mem_dom_iff_ne_top g y).1 hy_dom
  have hsum_nonneg : (0 : EReal) ≤ g y + g (-y) := by
    -- Subadditivity at `y` and `-y` forces the sum to dominate the zero-direction value.
    simpa [g, hzero] using hsub hy_dom hnegy_dom
  have hy_ne_bot : g y ≠ ⊥ := by
    -- Route correction: `dom = univ` only rules out `⊤`; use subadditivity with `-y` to rule out
    -- `⊥` as well.
    intro hy_bot
    have hsum_nonneg' := hsum_nonneg
    simp [g, hy_bot, EReal.bot_add] at hsum_nonneg'
  refine ⟨(g y).toReal, ?_⟩
  -- Once both infinities are excluded, the value is the real cast of its `toReal`.
  simpa [g] using (EReal.coe_toReal hy_ne_top hy_ne_bot).symm

/-- Source clause (vi): at a core point of the effective domain, the directional
derivative map is sublinear. -/
theorem sublinear_directionalDerivative_of_mem_core
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcore : x ∈ Set.core (effectiveDomain f)) :
    Sublinear (directionalDerivative f x) := by
  rcases Set.mem_core_iff.mp hxcore with ⟨hx, _⟩
  -- The core assumption contains the effective-domain membership needed by the global theorem.
  exact sublinear_directionalDerivative f hconv hx

/-- Source clause (i) of Proposition 17.2. Under the textbook proper/convex hypotheses, the
directional derivative exists in the source sense and is given by formula `(17.4)`. -/
theorem directionalDerivative_props_of_isProper_convex_1
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) ∧
      f′(x; y) =
        sInf ((fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) '' Set.Ioi (0 : ℝ)) := by
  let _ := hproper
  refine ⟨?_, ?_⟩
  · -- Reuse the canonical existence theorem for convex directional derivatives.
    exact hasDirectionalDerivativeAt_directionalDerivative f hconv hx y
  · -- Reuse the canonical infimum formula `(17.4)`.
    exact directionalDerivative_eq_sInf_image_Ioi f x y

/-- Source clause (ii) of Proposition 17.2. The directional derivative toward `y` controls the
secant increment from `x` to `y`. -/
theorem directionalDerivative_props_of_isProper_convex_2
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) :
    f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) := by
  let _ := hproper
  -- This is exactly the secant bound already proved as clause (ii).
  exact directionalDerivative_add_value_le f hconv hx y

/-- Source clause (iii) of Proposition 17.2. If `y ∈ dom f`, then opposite directional
derivatives along the segment from `x` to `y` bound each other. -/
theorem directionalDerivative_props_of_isProper_convex_3
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) :
    y ∈ effectiveDomain f → f′(x; y - x) ≤ -f′(y; x - y) := by
  let _ := hproper
  intro hy
  -- Apply the already packaged opposite-direction comparison.
  exact directionalDerivative_le_neg_swap f hconv hx hy

/-- Source clause (iv) of Proposition 17.2. The directional-derivative map at `x` is sublinear
and vanishes on the zero direction. -/
theorem directionalDerivative_props_of_isProper_convex_4
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    Sublinear (directionalDerivative f x) ∧ f′(x; 0) = 0 := by
  let _ := hproper
  refine ⟨?_, ?_⟩
  · -- Reuse the global sublinearity theorem at the effective-domain base point.
    exact sublinear_directionalDerivative f hconv hx
  · -- Reuse the zero-direction normalization.
    exact directionalDerivative_zero hconv hx

/-- Source clause (v) of Proposition 17.2. In the textbook Chapter 17 sense,
`f′(x; ·)` is proper and convex, and its domain is the cone generated by the translated
effective domain. Here proper means nonempty finite-value domain, while convex means convexity on
that natural domain. -/
theorem directionalDerivative_props_of_isProper_convex_5
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    IsProperInChapter17Sense (directionalDerivative f x) ∧
      IsConvexInChapter17Sense (directionalDerivative f x) ∧
      dom (directionalDerivative f x) =
        Set.cone (effectiveDomain f - ({x} : Set H)) := by
  let _ := hproper
  rcases directionalDerivative_dom_nonempty_convexOn_dom_and_dom_eq_cone hconv hx with
    ⟨hdom, hconvDom, hcone⟩
  refine ⟨?_, ?_, hcone⟩
  · -- Translate the nonempty finite-value domain into the repaired Chapter 17 notion of properness.
    simpa using hdom
  · -- Translate convexity-on-domain into the repaired Chapter 17 notion of convexity.
    simpa using hconvDom

/-- Source clause (vi) of Proposition 17.2. If `x ∈ core (dom f)`, then the
directional-derivative map is real-valued and sublinear. -/
theorem directionalDerivative_props_of_isProper_convex_6
    (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} :
    x ∈ Set.core (effectiveDomain f) →
      (∀ z : H, ∃ r : ℝ, f′(x; z) = (r : EReal)) ∧
      Sublinear (directionalDerivative f x) := by
  let _ := hproper
  intro hxcore
  refine ⟨?_, ?_⟩
  · -- The core-point API already provides real-valuedness in every direction.
    exact directionalDerivative_eq_coe_real_of_mem_core hconv hxcore
  · -- The same core-point API provides sublinearity.
    exact sublinear_directionalDerivative_of_mem_core hconv hxcore

-- `hproper` is explicit here to match the textbook hypotheses, even though the codomain
-- `Set.Ioi (⊥ : EReal)` and the point hypothesis `hx` already encode the non-`⊥` and
-- nonempty-domain parts needed by the local Chapter 17 API.

end RealVectorSpace

end

end ERealFunction
