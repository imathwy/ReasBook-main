import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Proposition_9_27
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap17.Definition_17_20

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

/-- Helper for Proposition 17 21: the directional derivative is the infimum of the positive
directional difference quotients. -/
noncomputable def directionalDerivative
    {H : Type u} [AddCommGroup H] [Module ℝ H]
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) : EReal :=
  sInf (Set.range (directionalDifferenceQuotient f x y))

notation:arg f "′(" x "; " y ")" => directionalDerivative f x y

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

/-- Helper for Proposition 17 21: the subtype-valued range of the directional difference quotient
agrees with the image of the underlying real-parameter quotient on the positive ray. -/
private theorem directionalDerivative_eq_sInf_image_Ioi
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

/-- Helper for Proposition 17 21: the positive directional quotient tends to the canonical
directional derivative along the right-hand filter at `0`. -/
private theorem directional_difference_quotient_tendsto_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Filter.Tendsto
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y))) := by
  -- Route correction: keep Proposition 17.21 self-contained by rebuilding the Proposition 17.2
  -- right-limit owner locally from the monotone positive quotient family.
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
    -- Extend the positive-ray quotients to an ambient monotone map and identify its right limit.
    rw [directionalDerivative_eq_sInf_image_Ioi (f := f) x y]
    simpa [himage] using hmono.tendsto_nhdsGT (0 : ℝ)
  have hEq : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      g := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hα' : 0 < α := hα
    simp [g, directionalDifferenceQuotient, hα']
  exact Filter.Tendsto.congr' hEq.symm htendsto

/-- Helper for Proposition 17 21: the canonical directional derivative exists at effective-domain
points of a convex function. -/
theorem hasDirectionalDerivativeAt_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) := by
  -- Package the canonical quotient limit as the source directional-derivative object.
  exact ⟨hx, directional_difference_quotient_tendsto_directionalDerivative
    (f := f) hconv hx y⟩

/-- Helper for Proposition 17 21: any directional derivative in the source sense equals the
canonical infimum-valued directional derivative. -/
theorem directionalDerivative_eq_of_hasDirectionalDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} {ξ : EReal} (hξ : HasDirectionalDerivativeAt f x y ξ) :
    f′(x; y) = ξ := by
  -- The convex directional derivative is uniquely determined by the right-limit quotient.
  have hdir := hasDirectionalDerivativeAt_directionalDerivative (f := f) hconv hξ.1 y
  exact tendsto_nhds_unique hdir.2 hξ.2

/-- Helper for Proposition 17 21: the directional derivative in the zero direction is zero at an
effective-domain point. -/
theorem directionalDerivative_zero
    {x : H} (hx : x ∈ effectiveDomain f) :
    f′(x; (0 : H)) = 0 := by
  rw [directionalDerivative]
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hquot : directionalDifferenceQuotient f x (0 : H) = fun _ ↦ (0 : EReal) := by
    funext α
    simp [directionalDifferenceQuotient, EReal.sub_self hfx_top hfx_bot]
  -- Every positive zero-direction quotient is exactly `0`, so the infimum is `0`.
  simp [hquot]

/-- Helper for Proposition 17 21: the directional derivative toward `y` controls the secant
increment from `x` to `y`. -/
theorem directionalDerivative_add_value_le
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) := by
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

/-- Helper for Proposition 17 21: along a finite ray point, the extended-real quotient is the
coercion of the ordinary real quotient for `toReal`. -/
theorem differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
    {x d : H} (hx : x ∈ effectiveDomain f) {α : ℝ} (hα : 0 < α)
    (hαdom : x + α • d ∈ effectiveDomain f) :
    (((f (x + α • d) : EReal) - (f x : EReal)) / α) =
      ((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  -- Rewrite both finite endpoint values through `toReal`, then the quotient is purely real.
  have _ : α ≠ 0 := hα.ne'
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • d) : EReal) from (f (x + α • d)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 17 21: at a finite base point, a negative positive-direction quotient
is exactly the statement that the step value strictly drops. -/
theorem differenceQuotient_lt_zero_iff_value_drop
    {x y : H} (hx : x ∈ effectiveDomain f) {α : ℝ} (hα : 0 < α) :
    (((f (x + α • y) : EReal) - (f x : EReal)) / α) < 0 ↔
      f.asEReal (x + α • y) < f.asEReal x := by
  by_cases hαdom : x + α • y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hαdom_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
    have hαdom_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from (f (x + α • y)).2)
    -- On the finite branch, both sides reduce to the ordinary real inequality after clearing the
    -- positive denominator `α`.
    rw [differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain (f := f) hx hα hαdom]
    rw [show (0 : EReal) = ((0 : ℝ) : EReal) by norm_num, EReal.coe_lt_coe_iff]
    rw [Function.asEReal_apply, Function.asEReal_apply, ← EReal.coe_toReal hαdom_top hαdom_bot,
      ← EReal.coe_toReal hx_top hx_bot, EReal.coe_lt_coe_iff]
    constructor
    · intro hquot
      have hnum : (f (x + α • y) : EReal).toReal - (f x : EReal).toReal < 0 := by
        have hnum' :
            (f (x + α • y) : EReal).toReal - (f x : EReal).toReal < 0 * α :=
          (div_lt_iff₀ hα).1 hquot
        simpa using hnum'
      linarith
    · intro hdrop
      have hnum : (f (x + α • y) : EReal).toReal - (f x : EReal).toReal < 0 := by
        linarith
      exact (div_lt_iff₀ hα).2 (by simpa using hnum)
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hαdom_top : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hαdom))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
    have hquot_top :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) = ⊤ := by
      rw [hαdom_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    -- Outside the effective domain, the endpoint value and the positive quotient are both `⊤`.
    rw [hquot_top, Function.asEReal_apply, hαdom_top]
    simp

-- Proof sketch: combine the monotonicity of directional difference quotients from Proposition
-- 9.27 with the infimum formula from Proposition 17.2 (1); strict decrease on a short initial ray
-- is equivalent to the limit infimum, hence the directional derivative, being strictly negative.
include hconv in
/-- Proposition 17 21 (1): for a proper convex `]-∞,+∞]`-valued function, a vector `y` is a
descent direction at an effective-domain point `x` exactly when the directional derivative
`f'(x; y)` is strictly negative. -/
theorem isDescentDirectionAt_iff_directionalDerivative_lt_zero
    {x y : H} (hx : x ∈ effectiveDomain f) :
    IsDescentDirectionAt f x y ↔ f′(x; y) < 0 := by
  constructor
  · rintro ⟨_, ε, hεpos, hdrop⟩
    have hquot_neg :
        (((f (x + ε • y) : EReal) - (f x : EReal)) / ε) < 0 := by
      exact (differenceQuotient_lt_zero_iff_value_drop (f := f) hx hεpos).2
        (by simpa using hdrop ⟨hεpos, le_rfl⟩)
    -- A single negative positive quotient forces the infimum of all such quotients below `0`.
    rw [directionalDerivative]
    exact lt_of_le_of_lt (sInf_le ⟨⟨ε, hεpos⟩, rfl⟩) hquot_neg
  · intro hdir
    rw [directionalDerivative_eq_sInf_image_Ioi (f := f) x y] at hdir
    obtain ⟨q, hqmem, hqneg⟩ := (sInf_lt_iff).1 hdir
    rcases hqmem with ⟨β, hβpos, rfl⟩
    have hmono := directionalDifferenceQuotient_monotone f hconv hx y
    refine ⟨hx, β, hβpos, ?_⟩
    intro α hα
    have hle :
        directionalDifferenceQuotient f x y ⟨α, hα.1⟩ ≤
          directionalDifferenceQuotient f x y ⟨β, hβpos⟩ := by
      exact hmono hα.2
    have hquot_neg :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) < 0 := by
      exact lt_of_le_of_lt (by simpa [directionalDifferenceQuotient] using hle)
        (by simpa [directionalDifferenceQuotient] using hqneg)
    exact (differenceQuotient_lt_zero_iff_value_drop (f := f) hx hα.1).1 hquot_neg

end RealVectorSpace

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

/-- Helper for Proposition 17 21: a negative finite Gâteaux slope forces the ray to stay inside
the effective domain near the base point. -/
theorem eventually_mem_effectiveDomain_of_negative_gateaux_slope
    {x d : H} (_hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x)
    (hslope : ((toDual ℝ H gradf) d : ℝ) < 0) :
    ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f := by
  let r : ℝ → ℝ := fun α ↦ (((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ)
  let L : ℝ := ((toDual ℝ H gradf) d : ℝ)
  have hreal : Filter.Tendsto r (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    -- The Chapter 2 Gâteaux derivative controls the real quotient along the ray.
    simpa [r, L, one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hgrad.tendsto_directionalDifferenceQuotient d
  have hnear : ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), r α ∈ Set.Ioo (L - 1) 0 := by
    exact hreal (Ioo_mem_nhds (by linarith [hslope]) (by simpa [L] using hslope))
  by_cases hfx_pos : 0 < (f x : EReal).toReal
  · let δ : ℝ := (f x : EReal).toReal / (1 - L)
    have hδpos : 0 < δ := by
      dsimp [δ]
      have hden : 0 < 1 - L := by linarith [hslope]
      exact div_pos hfx_pos hden
    have hδmem : Set.Iio δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδpos)
    filter_upwards [hnear, hδmem, self_mem_nhdsWithin] with α hαnear hαlt hα
    by_contra hαdom
    have hαtop : (f (x + α • d) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hαdom))
    have hEq : r α = -((f x : EReal).toReal) / α := by
      dsimp [r]
      rw [hαtop]
      simp [sub_eq_add_neg]
    have hden : 0 < 1 - L := by linarith [hslope]
    have hmul : α * (1 - L) < (f x : EReal).toReal := by
      exact (lt_div_iff₀ hden).1 (by simpa [δ] using hαlt)
    have hbound : 1 - L < (f x : EReal).toReal / α := by
      exact (lt_div_iff₀ hα).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    have hsmall : -((f x : EReal).toReal) / α < L - 1 := by
      have hsmall' : -((f x : EReal).toReal / α) < L - 1 := by
        linarith
      simpa [neg_div] using hsmall'
    have hnotin : r α ∉ Set.Ioo (L - 1) 0 := by
      rw [hEq]
      intro hr
      exact (not_lt_of_ge hsmall.le) hr.1
    exact hnotin hαnear
  · have hnum_nonneg : 0 ≤ -((f x : EReal).toReal) := by
      linarith
    filter_upwards [hnear, self_mem_nhdsWithin] with α hαnear hα
    by_contra hαdom
    have hαtop : (f (x + α • d) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hαdom))
    have hEq : r α = -((f x : EReal).toReal) / α := by
      dsimp [r]
      rw [hαtop]
      simp [sub_eq_add_neg]
    have hnonneg : 0 ≤ -((f x : EReal).toReal) / α := by
      exact div_nonneg hnum_nonneg hα.le
    have hnotin : r α ∉ Set.Ioo (L - 1) 0 := by
      rw [hEq]
      intro hr
      exact (not_lt_of_ge hnonneg) hr.2
    exact hnotin hαnear

/-- Helper for Proposition 17 21: once the ray is eventually in the effective domain, the real
Gâteaux derivative of `toReal` upgrades to the Chapter 17 directional derivative of `f`. -/
theorem hasDirectionalDerivativeAt_of_hasGateauxDerivativeAt_of_eventually_mem_effectiveDomain
    {x d : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x)
    (hevent : ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x d ((((toDual ℝ H gradf) d : ℝ) : EReal)) := by
  have hreal :
      Filter.Tendsto
        (fun α : ℝ ↦ (((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((toDual ℝ H gradf) d)) := by
    -- Rewrite the Gâteaux quotient into the ordinary scalar quotient for `toReal`.
    simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hgrad.tendsto_directionalDifferenceQuotient d
  have hcoe :
      Filter.Tendsto
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((((toDual ℝ H gradf) d : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 hreal
  have hEq :
      (fun α : ℝ ↦ ((f (x + α • d) : EReal) - (f x : EReal)) / α) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal))) := by
    filter_upwards [hevent, self_mem_nhdsWithin] with α hαdom hα
    simpa using
      differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain (f := f) hx hα hαdom
  exact ⟨hx, Filter.Tendsto.congr' hEq.symm hcoe⟩

/-- Helper for Proposition 17 21: along the negative gradient, the directional derivative equals
`-‖gradf‖²`. -/
theorem directionalDerivative_eq_neg_norm_sq_of_hasGateauxDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x) :
    f′(x; -gradf) = (-(‖gradf‖ ^ 2) : EReal) := by
  by_cases hzero : gradf = 0
  · subst hzero
    -- In the zero-gradient case, the negative-gradient direction is the zero direction.
    simpa using directionalDerivative_zero (f := f) hx
  · have hslope_eq :
        ((toDual ℝ H gradf) (-gradf) : ℝ) = -(‖gradf‖ ^ 2) := by
      calc
        ((toDual ℝ H gradf) (-gradf) : ℝ) = ⟪gradf, -gradf⟫_ℝ := by
          simp [toDual_apply_eq_toDualMap_apply, toDualMap_apply_apply]
        _ = -(‖gradf‖ ^ 2) := by
          rw [inner_neg_right, real_inner_self_eq_norm_sq]
    have hslope : ((toDual ℝ H gradf) (-gradf) : ℝ) < 0 := by
      rw [hslope_eq]
      have hnorm_pos : 0 < ‖gradf‖ := norm_pos_iff.mpr hzero
      have hsq_pos : 0 < ‖gradf‖ ^ 2 := by
        nlinarith [sq_pos_of_pos hnorm_pos]
      linarith
    have hevent :=
      eventually_mem_effectiveDomain_of_negative_gateaux_slope
        (f := f) hx gradf hgrad hslope
    have hdir :
        HasDirectionalDerivativeAt f x (-gradf) ((((toDual ℝ H gradf) (-gradf) : ℝ) : EReal)) :=
      hasDirectionalDerivativeAt_of_hasGateauxDerivativeAt_of_eventually_mem_effectiveDomain
        (f := f) hx gradf hgrad hevent
    calc
      f′(x; -gradf) = ((((toDual ℝ H gradf) (-gradf) : ℝ) : EReal)) := by
        exact directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := f) hconv hdir
      _ = (-(‖gradf‖ ^ 2) : EReal) := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hslope_eq

omit [CompleteSpace H] in
/-- Helper for Proposition 17 21: if `y` stays in the effective domain, then the segment from `x`
toward `y` remains in the effective domain for all sufficiently small positive steps. -/
theorem eventually_mem_effectiveDomain_toward_point
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • (y - x) ∈ effectiveDomain f := by
  have hsegment :
      ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 → x + α • (y - x) ∈ effectiveDomain f := by
    -- Convexity of the effective domain gives the whole secant segment from `x` to `y`.
    intro α hα0 hα1
    have hconvex : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
    exact hconvex.add_smul_sub_mem hx hy ⟨hα0, hα1⟩
  have hα_mem :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with
      α hα0 hα1
    exact ⟨hα0, hα1.le⟩
  filter_upwards [hα_mem] with α hα
  exact hsegment hα.1.le hα.2

/-- Helper for Proposition 17 21: a Gâteaux gradient at `x` defines the usual supporting
hyperplane inequality for every comparison point `y`. -/
theorem gateaux_gradient_support_inequality
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x) :
    (⟪y - x, gradf⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
  by_cases hy : y ∈ effectiveDomain f
  · have hevent :=
      eventually_mem_effectiveDomain_toward_point (f := f) hconv hx hy
    have hdir :
        HasDirectionalDerivativeAt f x (y - x)
          ((((toDual ℝ H gradf) (y - x) : ℝ) : EReal)) :=
      hasDirectionalDerivativeAt_of_hasGateauxDerivativeAt_of_eventually_mem_effectiveDomain
        (f := f) hx gradf hgrad hevent
    have hdir_eq :
        (⟪y - x, gradf⟫_ℝ : EReal) = f′(x; y - x) := by
      calc
        (⟪y - x, gradf⟫_ℝ : EReal)
            = ((((toDual ℝ H gradf) (y - x) : ℝ) : EReal)) := by
                simp [toDual_apply_eq_toDualMap_apply, toDualMap_apply_apply, real_inner_comm]
        _ = f′(x; y - x) := by
              simpa using
                (directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := f) hconv hdir).symm
    -- Identify the source directional derivative with the Gâteaux pairing and apply the secant
    -- bound from clause (2) of the local Proposition 17.2 replacement.
    rw [hdir_eq]
    exact directionalDerivative_add_value_le (f := f) hx y
  · have hfy_top : (f y : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
    rw [hfy_top]
    exact le_top

-- Proof sketch: Proposition 17.6 gives the supporting-hyperplane inequality, so `gradf = 0`
-- would force `x` to be a global minimizer; the differentiability formula then gives
-- `f′(x; -gradf) = -‖gradf‖^2 < 0`, and clause (1) turns that strict negativity into descent.
include hconv in
/-- Proposition 17 21 (2): if a convex `]-∞,+∞]`-valued function has Gâteaux gradient `gradf` at
an effective-domain point `x` and `x` is not a minimizer, then the negative gradient `-gradf` is a
descent direction of `f` at `x`. -/
theorem neg_gateauxGradient_isDescentDirectionAt_of_not_mem_argmin
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x)
    (hxnot : x ∉ Argmin f.asEReal) :
    IsDescentDirectionAt f x (-gradf) := by
  have hgrad_ne : gradf ≠ 0 := by
    intro hzero
    have hxmin : x ∈ Argmin f.asEReal := by
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro y
      simpa [Function.asEReal_apply, hzero] using
        gateaux_gradient_support_inequality (f := f) hconv (x := x) (y := y) hx gradf hgrad
    exact hxnot hxmin
  have hdir_eq :=
    directionalDerivative_eq_neg_norm_sq_of_hasGateauxDerivativeAt
      (f := f) hconv hx gradf hgrad
  have hdir_neg : f′(x; -gradf) < 0 := by
    rw [hdir_eq]
    have hsq_pos : 0 < ‖gradf‖ ^ 2 := by
      have hnorm_pos : 0 < ‖gradf‖ := norm_pos_iff.mpr hgrad_ne
      nlinarith [sq_pos_of_pos hnorm_pos]
    have hneg : (-(‖gradf‖ ^ 2) : ℝ) < 0 := by
      linarith
    have hnegE : (((-(‖gradf‖ ^ 2) : ℝ) : EReal) < ((0 : ℝ) : EReal)) := by
      exact EReal.coe_lt_coe_iff.mpr hneg
    simpa using hnegE
  exact (isDescentDirectionAt_iff_directionalDerivative_lt_zero
    (f := f) hconv hx).2 hdir_neg

end DifferentiabilityOfConvexFunctions

end

end ERealFunction
