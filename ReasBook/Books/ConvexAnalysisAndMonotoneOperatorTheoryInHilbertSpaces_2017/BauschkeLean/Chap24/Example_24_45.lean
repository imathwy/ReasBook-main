import Mathlib
import BauschkeLean.Chap09.Proposition_9_34
import BauschkeLean.Chap24.Proposition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Filter
open scoped Topology

noncomputable section

namespace ERealFunction

attribute [local instance] Classical.propDecidable

/-- Helper for Example 24.45: the real-valued interior branch
`ξ ↦ -(2 / π) log (cos ((π / 2) ξ)) - ξ² / 2`. -/
private def logCosBarrierMinusHalfSqSeed (ξ : ℝ) : ℝ :=
  -((2 / Real.pi) * Real.log (Real.cos ((Real.pi / 2) * ξ))) -
    (1 / 2 : ℝ) * ξ ^ (2 : ℕ)

/-- The `]-∞,+∞]`-valued function equal to `-(2 / π) log (cos ((π / 2) ξ)) - ξ² / 2` on `|ξ| < 1`
and to `+∞` on `|ξ| ≥ 1`. -/
def log_cos_barrier_minus_half_sq : ℝ → Set.Ioi (⊥ : EReal) :=
  ι[Set.Ioo (-1) 1] +
    (fun ξ : ℝ ↦
      -((2 / Real.pi) * Real.log (Real.cos ((Real.pi / 2) * ξ))) -
        (1 / 2 : ℝ) * ξ ^ (2 : ℕ)).toEReal

/-- Helper for Example 24.45: any finite real value, viewed in `EReal`, lies above `⊥`. -/
private theorem coe_real_mem_Ioi_bot (r : ℝ) :
    (⊥ : EReal) < ((r : ℝ) : EReal) :=
  EReal.bot_lt_coe r

/-- Helper for Example 24.45: the exterior `+∞` branch also lies above `⊥`. -/
private theorem top_mem_Ioi_bot_local :
    (⊥ : EReal) < (⊤ : EReal) :=
  bot_lt_top

/-- Helper for Example 24.45: package a real branch as finite on `]α,β[` and `+∞` outside. -/
private noncomputable def finiteOnOpenInterval (f : ℝ → ℝ) (α β : EReal) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if _hx : x ∈ erealOpenInterval α β then
      ⟨((f x : ℝ) : EReal), coe_real_mem_Ioi_bot (f x)⟩
    else
      ⟨(⊤ : EReal), top_mem_Ioi_bot_local⟩

/-- Helper for Example 24.45: the effective domain of the finite-open-interval model is exactly
the underlying open interval. -/
private theorem finiteOnOpenInterval_effectiveDomain (f : ℝ → ℝ) (α β : EReal) :
    effectiveDomain (finiteOnOpenInterval f α β) = erealOpenInterval α β := by
  -- The interior branch is finite, while every exterior point is sent to `+∞`.
  ext x
  by_cases hx : x ∈ erealOpenInterval α β
  · simp [mem_effectiveDomain_iff, finiteOnOpenInterval, hx]
  · simp [mem_effectiveDomain_iff, finiteOnOpenInterval, hx]

/-- Helper for Example 24.45: a genuine one-sided `EReal` limit above `⊥` forces the corresponding
one-sided `liminf` to stay above `⊥`. -/
private theorem boundary_liminf_gt_bot_of_tendsto
    {g : ℝ → Set.Ioi (⊥ : EReal)} {x : ℝ} {s : Set ℝ} {a : EReal}
    (hs : Filter.NeBot (nhdsWithin x s))
    (h : Filter.Tendsto (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x s) (nhds a)) (ha : ⊥ < a) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x s) := by
  -- A convergent filter has `liminf` equal to its limit value.
  let _ : Filter.NeBot (nhdsWithin x s) := hs
  rw [h.liminf_eq]
  exact ha

/-- Helper for Example 24.45: strict convexity of the finite real seed on the open interval gives
strict convexity of its `]-∞,+∞]`-valued open-interval model. -/
-- TODO: cast the strict Jensen inequality from the real seed to `EReal` and then simplify the
-- active branch of `finiteOnOpenInterval`.
private theorem strictlyConvex_finiteOnOpenInterval_of_strictConvexOn
    {f : ℝ → ℝ} {α β : EReal} (hf : StrictConvexOn ℝ (erealOpenInterval α β) f) :
    StrictlyConvex (finiteOnOpenInterval f α β) := by
  intro x hx y hy hxy a ha0 ha1
  -- The effective-domain hypotheses put both points back on the real open interval.
  have hx' : x ∈ erealOpenInterval α β := by
    simpa [finiteOnOpenInterval_effectiveDomain] using hx
  have hy' : y ∈ erealOpenInterval α β := by
    simpa [finiteOnOpenInterval_effectiveDomain] using hy
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hab : a + (1 - a) = 1 := by ring
  have hxy' : a • x + (1 - a) • y ∈ erealOpenInterval α β := by
    exact hf.1 hx' hy' ha0.le hb0.le hab
  -- Jensen's strict inequality for the real seed transfers directly to `EReal`.
  have hineq :
      f (a * x + (1 - a) * y) < a * f x + (1 - a) * f y :=
    hf.2 hx' hy' hxy ha0 hb0 hab
  have hineqE :
      (((f (a * x + (1 - a) * y) : ℝ) : EReal)) <
        (((a * f x + (1 - a) * f y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  have hxyE : a * x + (1 - a) * y ∈ erealOpenInterval α β := by
    simpa [smul_eq_mul] using hxy'
  calc
    (finiteOnOpenInterval f α β (a • x + (1 - a) • y) : EReal)
        = (finiteOnOpenInterval f α β (a * x + (1 - a) * y) : EReal) := by
            simp [smul_eq_mul]
    _ = (((f (a * x + (1 - a) * y) : ℝ) : EReal)) := by
            simp [finiteOnOpenInterval, hxyE]
    _ < (((a * f x + (1 - a) * f y : ℝ) : EReal)) := hineqE
    _ = (a : EReal) * (finiteOnOpenInterval f α β x : EReal) +
          (1 - a : EReal) * (finiteOnOpenInterval f α β y : EReal) := by
            simp [finiteOnOpenInterval, hx', hy', EReal.coe_mul, EReal.coe_add]

/-- Helper for Example 24.45: the open `EReal` interval `]-1,1[` is the ordinary real interval
`(-1,1)`. -/
-- TODO: translate the endpoint comparisons in `erealOpenInterval` back to the real inequalities
-- `-1 < x` and `x < 1`.
private theorem erealOpenInterval_neg_one_one :
    erealOpenInterval (-1 : EReal) (1 : EReal) = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    -- Rewrite the `EReal` endpoint inequalities as ordinary real inequalities.
    rw [mem_erealOpenInterval_iff] at hx
    have hxL' : (((-1 : ℝ) : EReal) < (x : EReal)) := by
      simpa using hx.1
    have hxR' : ((x : EReal) < ((1 : ℝ) : EReal)) := by
      simpa using hx.2
    exact ⟨by exact_mod_cast hxL', by exact_mod_cast hxR'⟩
  · intro hx
    -- The converse direction is the same coercion step in reverse.
    rw [mem_erealOpenInterval_iff]
    have hxL' : (((-1 : ℝ) : EReal) < (x : EReal)) := by
      exact_mod_cast hx.1
    have hxR' : ((x : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast hx.2
    simpa using ⟨hxL', hxR'⟩

/-- Helper for Example 24.45: the open-interval owner associated with the log-cos seed. -/
private noncomputable def logCosBarrierMinusHalfSqOpenInterval :
    ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval logCosBarrierMinusHalfSqSeed (-1) 1

/-- Helper for Example 24.45: on `(-1,1)`, the textbook barrier agrees with the real seed. -/
private theorem log_cos_barrier_minus_half_sq_apply_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (log_cos_barrier_minus_half_sq x : EReal) = (logCosBarrierMinusHalfSqSeed x : EReal) := by
  -- Interior points activate the zero indicator branch.
  simp [log_cos_barrier_minus_half_sq, logCosBarrierMinusHalfSqSeed, hx]

/-- Helper for Example 24.45: outside `(-1,1)`, the textbook barrier is `+∞`. -/
-- TODO: show that the indicator contributes `⊤` and the finite branch remains strictly above
-- `⊥`, so the sum is forced to be `⊤`.
private theorem log_cos_barrier_minus_half_sq_apply_of_not_mem_Ioo {x : ℝ}
    (hx : x ∉ Set.Ioo (-1 : ℝ) 1) :
    (log_cos_barrier_minus_half_sq x : EReal) = ⊤ := by
  -- Outside the open interval, the indicator branch is `+∞`, so the full sum is `+∞`.
  simpa [log_cos_barrier_minus_half_sq, indicator_apply, hx, logCosBarrierMinusHalfSqSeed] using
    (EReal.top_add_coe (logCosBarrierMinusHalfSqSeed x))

/-- Helper for Example 24.45: on `(-1,1)`, coercing back to `ℝ` recovers the real seed. -/
private theorem log_cos_barrier_minus_half_sq_toReal_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (log_cos_barrier_minus_half_sq x : EReal).toReal = logCosBarrierMinusHalfSqSeed x := by
  -- Once the value is known to be finite, `toReal` simply removes the coercion.
  rw [log_cos_barrier_minus_half_sq_apply_of_mem_Ioo hx]
  simpa [logCosBarrierMinusHalfSqSeed] using (EReal.toReal_coe (logCosBarrierMinusHalfSqSeed x))

/-- Helper for Example 24.45: the effective domain of the textbook barrier is the open interval
`(-1,1)`. -/
private theorem log_cos_barrier_minus_half_sq_effectiveDomain :
    effectiveDomain log_cos_barrier_minus_half_sq = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    by_contra hx'
    simp [mem_effectiveDomain_iff, log_cos_barrier_minus_half_sq_apply_of_not_mem_Ioo hx'] at hx
  · intro hx
    rw [mem_effectiveDomain_iff, log_cos_barrier_minus_half_sq_apply_of_mem_Ioo hx]
    exact EReal.coe_lt_top _

/-- Helper for Example 24.45: the seed derivative on `(-1,1)` is
`tan ((π / 2) x) - x`. -/
-- TODO: rewrite the scalar composition consistently with right multiplication by `π / 2` and
-- then simplify the coefficient `(2 / π) * (π / 2)` to `1`.
private theorem logCosBarrierMinusHalfSqSeed_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt logCosBarrierMinusHalfSqSeed (Real.tan ((Real.pi / 2) * x) - x) x := by
  -- First place `(π / 2) * x` in the standard tangent interval.
  have hxscaled :
      ((Real.pi / 2) * x) ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    constructor
    · nlinarith [hx.1, Real.pi_pos]
    · nlinarith [hx.2, Real.pi_pos]
  have hcos_pos : 0 < Real.cos ((Real.pi / 2) * x) :=
    Real.cos_pos_of_mem_Ioo hxscaled
  -- Differentiate the logarithmic part by the chain rule.
  have hinner :
      HasDerivAt (fun y : ℝ ↦ Real.cos ((Real.pi / 2) * y))
        (-Real.sin ((Real.pi / 2) * x) * (Real.pi / 2)) x := by
    have hmul : HasDerivAt (fun y : ℝ ↦ y * (Real.pi / 2)) (Real.pi / 2) x := by
      simpa using (hasDerivAt_id x).mul_const (Real.pi / 2)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_cos (x * (Real.pi / 2))).comp x hmul
  have hlogcos :
      HasDerivAt (fun y : ℝ ↦ Real.log (Real.cos ((Real.pi / 2) * y)))
        (-(Real.pi / 2) * Real.tan ((Real.pi / 2) * x)) x := by
    simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_log hcos_pos.ne').comp x hinner
  have hcoeff : (-(2 / Real.pi) : ℝ) * (-(Real.pi / 2)) = 1 := by
    field_simp [Real.pi_ne_zero]
  have hfirst :
      HasDerivAt
        (fun y : ℝ ↦ -((2 / Real.pi) * Real.log (Real.cos ((Real.pi / 2) * y))))
        (Real.tan ((Real.pi / 2) * x)) x := by
    -- The constants collapse to `1`, leaving exactly `tan ((π / 2) x)`.
    convert hlogcos.const_mul (-(2 / Real.pi) : ℝ) using 1
    · funext y
      ring
    · rw [show (-(2 / Real.pi) : ℝ) * (-(Real.pi / 2) * Real.tan ((Real.pi / 2) * x)) =
        Real.tan ((Real.pi / 2) * x) by
          calc
            (-(2 / Real.pi) : ℝ) * (-(Real.pi / 2) * Real.tan ((Real.pi / 2) * x))
                = ((-(2 / Real.pi) : ℝ) * (-(Real.pi / 2))) * Real.tan ((Real.pi / 2) * x) := by
                    ring
            _ = Real.tan ((Real.pi / 2) * x) := by simp [hcoeff]]
  -- The quadratic correction contributes the linear term `x`.
  have hquadratic :
      HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ)) x x := by
    have hquadratic_raw :
        HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ)) ((1 / 2 : ℝ) * (2 * x)) x := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)
    exact hquadratic_raw.congr_deriv (by ring)
  -- Combine the two scalar derivatives to recover the textbook first-order formula.
  convert hfirst.sub hquadratic using 1

/-- Helper for Example 24.45: the second derivative of the seed is positive on `(-1,1)`. -/
-- TODO: identify `deriv^[2]` with `(π / 2) / cos((π / 2) x)^2 - 1` by freezing the first
-- derivative on a neighborhood of `x`, then use `cos^2 ≤ 1` and `1 < π / 2`.
private theorem logCosBarrierMinusHalfSqSeed_deriv2_pos {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < (deriv^[2] logCosBarrierMinusHalfSqSeed) x := by
  -- Differentiate the explicit first-derivative formula on a neighborhood of `x`.
  have hxscaled :
      ((Real.pi / 2) * x) ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    constructor
    · nlinarith [hx.1, Real.pi_pos]
    · nlinarith [hx.2, Real.pi_pos]
  have hcos_pos : 0 < Real.cos ((Real.pi / 2) * x) :=
    Real.cos_pos_of_mem_Ioo hxscaled
  have hinterval : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hderiv_eq :
      (fun y : ℝ ↦ deriv logCosBarrierMinusHalfSqSeed y) =ᶠ[𝓝 x]
        (fun y : ℝ ↦ Real.tan ((Real.pi / 2) * y) - y) := by
    filter_upwards [hinterval] with y hy
    exact (logCosBarrierMinusHalfSqSeed_hasDerivAt hy).deriv
  have htan :
      HasDerivAt (fun y : ℝ ↦ Real.tan ((Real.pi / 2) * y))
        (((1 / Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ)) * (Real.pi / 2))) x := by
    have hmul : HasDerivAt (fun y : ℝ ↦ y * (Real.pi / 2)) (Real.pi / 2) x := by
      simpa using (hasDerivAt_id x).mul_const (Real.pi / 2)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_tan_of_mem_Ioo (by simpa [mul_comm] using hxscaled)).comp x hmul
  have hformula :
      HasDerivAt (fun y : ℝ ↦ Real.tan ((Real.pi / 2) * y) - y)
        (((Real.pi / 2) / Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ)) - 1) x := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htan.sub (hasDerivAt_id x)
  have hderiv2 :
      HasDerivAt (fun y : ℝ ↦ deriv logCosBarrierMinusHalfSqSeed y)
        (((Real.pi / 2) / Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ)) - 1) x := by
    exact hformula.congr_of_eventuallyEq hderiv_eq
  have hvalue :
      (deriv^[2] logCosBarrierMinusHalfSqSeed) x =
        ((Real.pi / 2) / Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ)) - 1 := by
    simpa using hderiv2.deriv
  rw [hvalue]
  have hcos_le_one : Real.cos ((Real.pi / 2) * x) ≤ 1 := by
    exact (abs_le.mp (Real.abs_cos_le_one ((Real.pi / 2) * x))).2
  have hcos_sq_lt_pi_half : Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ) < Real.pi / 2 := by
    have hcos_sq_le_one : Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ) ≤ 1 := by
      nlinarith [hcos_pos, hcos_le_one]
    have hpi_half_gt_one : (1 : ℝ) < Real.pi / 2 := by
      nlinarith [Real.pi_gt_three]
    exact lt_of_le_of_lt hcos_sq_le_one hpi_half_gt_one
  have hdiv_gt_one :
      1 < (Real.pi / 2) / Real.cos ((Real.pi / 2) * x) ^ (2 : ℕ) := by
    rw [one_lt_div_iff]
    left
    exact ⟨by positivity, hcos_sq_lt_pi_half⟩
  linarith

/-- Helper for Example 24.45: the log-cos seed is strictly convex on `(-1,1)`. -/
private theorem logCosBarrierMinusHalfSqSeed_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) logCosBarrierMinusHalfSqSeed := by
  -- The seed is continuous on the open interval because it is differentiable there, and its second
  -- derivative is strictly positive there.
  have hdiff :
      DifferentiableOn ℝ logCosBarrierMinusHalfSqSeed (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (logCosBarrierMinusHalfSqSeed_hasDerivAt hx).differentiableAt.differentiableWithinAt
  apply strictConvexOn_of_deriv2_pos' (convex_Ioo (-1 : ℝ) 1)
  · exact hdiff.continuousOn
  · intro x hx
    exact logCosBarrierMinusHalfSqSeed_deriv2_pos hx

/-- Helper for Example 24.45: near `-1`, the open-interval model agrees with the real seed. -/
private theorem logCosBarrierMinusHalfSqOpenInterval_eventuallyEq_seed_at_neg_one :
    Filter.EventuallyEq (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
      (fun x : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval x : EReal))
      (fun x : ℝ ↦ (logCosBarrierMinusHalfSqSeed x : EReal)) := by
  -- Moving slightly to the right of `-1` keeps the point inside the interval `(-1,1)`.
  have hlt :
      Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
    exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
      (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  filter_upwards [hlt] with x hx
  have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.1, hx.2⟩
  have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [erealOpenInterval_neg_one_one] using hxIoo
  simp [logCosBarrierMinusHalfSqOpenInterval, finiteOnOpenInterval, hxE, logCosBarrierMinusHalfSqSeed]

/-- Helper for Example 24.45: near `1`, the open-interval model agrees with the real seed. -/
private theorem logCosBarrierMinusHalfSqOpenInterval_eventuallyEq_seed_at_one :
    Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (fun x : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval x : EReal))
      (fun x : ℝ ↦ (logCosBarrierMinusHalfSqSeed x : EReal)) := by
  -- Moving slightly to the left of `1` keeps the point inside the interval `(-1,1)`.
  have hgt :
      Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  filter_upwards [hgt] with x hx
  have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
  have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [erealOpenInterval_neg_one_one] using hxIoo
  simp [logCosBarrierMinusHalfSqOpenInterval, finiteOnOpenInterval, hxE, logCosBarrierMinusHalfSqSeed]

/-- Helper for Example 24.45: `x ↦ cos ((π / 2) x)` tends to `0+` as `x → -1+`. -/
private theorem cos_scaled_tendsto_nhdsGT_zero_at_neg_one_right :
    Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  -- Split the one-sided limit into convergence to `0` and eventual positivity.
  have h0' :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (nhds ((fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x)) (-1))) := by
    have hcont : Continuous (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x)) := by
      continuity
    exact hcont.continuousAt.continuousWithinAt.tendsto
  have h0 :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : ℝ)) := by
    simpa using h0'
  have hlt :
      Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
    exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
      (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hpos :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (Filter.principal (Set.Ioi (0 : ℝ))) := by
    rw [Filter.tendsto_principal]
    filter_upwards [hlt] with x hx
    have hxscaled :
        ((Real.pi / 2) * x) ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
      have hpi_half_pos : 0 < Real.pi / 2 := by positivity
      constructor
      · have hxleft : -1 < x := hx.1
        nlinarith
      · have hxright : x < 1 := hx.2
        nlinarith
    exact Real.cos_pos_of_mem_Ioo hxscaled
  change
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
  exact Filter.tendsto_inf.2 ⟨h0, hpos⟩

/-- Helper for Example 24.45: `x ↦ cos ((π / 2) x)` tends to `0+` as `x → 1-`. -/
private theorem cos_scaled_tendsto_nhdsGT_zero_at_one_left :
    Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  -- The same decomposition works when approaching `1` from the left.
  have h0' :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds ((fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x)) 1)) := by
    have hcont : Continuous (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x)) := by
      continuity
    exact hcont.continuousAt.continuousWithinAt.tendsto
  have h0 :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
    simpa using h0'
  have hgt :
      Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hpos :
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Filter.principal (Set.Ioi (0 : ℝ))) := by
    rw [Filter.tendsto_principal]
    filter_upwards [hgt] with x hx
    have hxscaled :
        ((Real.pi / 2) * x) ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
      have hpi_half_pos : 0 < Real.pi / 2 := by positivity
      constructor
      · have hxleft : -1 < x := hx.2
        nlinarith
      · have hxright : x < 1 := hx.1
        nlinarith
    exact Real.cos_pos_of_mem_Ioo hxscaled
  change
      Filter.Tendsto (fun x : ℝ ↦ Real.cos ((Real.pi / 2) * x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
  exact Filter.tendsto_inf.2 ⟨h0, hpos⟩

/-- Helper for Example 24.45: the open-interval model tends to `+∞` when approaching `-1` from the
right. -/
-- TODO: compose `Real.tendsto_cos_neg_pi_div_two` and `Real.tendsto_log_nhdsGT_zero`, then add
-- the bounded quadratic term to recover `logCosBarrierMinusHalfSqSeed → +∞`.
private theorem logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_neg_one :
    Filter.Tendsto (fun x : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval x : EReal))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds ⊤) := by
  -- Replace the open-interval model by the real seed and push the logarithmic barrier to `+∞`.
  have hlog :
      Filter.Tendsto (fun x : ℝ ↦ Real.log (Real.cos ((Real.pi / 2) * x)))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) Filter.atBot := by
    exact Real.tendsto_log_nhdsGT_zero.comp cos_scaled_tendsto_nhdsGT_zero_at_neg_one_right
  have hbarrier :
      Filter.Tendsto
        (fun x : ℝ ↦ -((2 / Real.pi) * Real.log (Real.cos ((Real.pi / 2) * x))))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) Filter.atTop := by
    have hpos : 0 < (2 / Real.pi : ℝ) := by
      positivity
    have hneg : (-(2 / Real.pi) : ℝ) < 0 := neg_neg_of_pos hpos
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      hlog.atBot_mul_const_of_neg hneg
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  have hlt :
      Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
    exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
      (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hquadratic :
      ∀ᶠ x in nhdsWithin (-1 : ℝ) (Set.Ioi (-1)),
        -((1 / 2 : ℝ) * x ^ (2 : ℕ)) > -1 := by
    filter_upwards [hlt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := hx
    nlinarith [hxIoo.1, hxIoo.2]
  have hseed :
      ∀ᶠ x in nhdsWithin (-1 : ℝ) (Set.Ioi (-1)), M < logCosBarrierMinusHalfSqSeed x := by
    filter_upwards [hbarrier.eventually_gt_atTop (M + 1), hquadratic] with x hxbarrier hxquadratic
    dsimp [logCosBarrierMinusHalfSqSeed] at hxbarrier hxquadratic ⊢
    nlinarith
  filter_upwards [logCosBarrierMinusHalfSqOpenInterval_eventuallyEq_seed_at_neg_one, hseed] with x
      hxEq hxSeed
  rw [hxEq]
  exact_mod_cast hxSeed

/-- Helper for Example 24.45: the open-interval model tends to `+∞` when approaching `1` from the
left. -/
-- TODO: compose `Real.tendsto_cos_pi_div_two` and `Real.tendsto_log_nhdsGT_zero`, then add the
-- bounded quadratic term to recover `logCosBarrierMinusHalfSqSeed → +∞`.
private theorem logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_one :
    Filter.Tendsto (fun x : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval x : EReal))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds ⊤) := by
  -- The right endpoint is the symmetric barrier blow-up.
  have hlog :
      Filter.Tendsto (fun x : ℝ ↦ Real.log (Real.cos ((Real.pi / 2) * x)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atBot := by
    exact Real.tendsto_log_nhdsGT_zero.comp cos_scaled_tendsto_nhdsGT_zero_at_one_left
  have hbarrier :
      Filter.Tendsto
        (fun x : ℝ ↦ -((2 / Real.pi) * Real.log (Real.cos ((Real.pi / 2) * x))))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atTop := by
    have hpos : 0 < (2 / Real.pi : ℝ) := by
      positivity
    have hneg : (-(2 / Real.pi) : ℝ) < 0 := neg_neg_of_pos hpos
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      hlog.atBot_mul_const_of_neg hneg
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  have hgt :
      Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hquadratic :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1),
        -((1 / 2 : ℝ) * x ^ (2 : ℕ)) > -1 := by
    filter_upwards [hgt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
    nlinarith [hxIoo.1, hxIoo.2]
  have hseed :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), M < logCosBarrierMinusHalfSqSeed x := by
    filter_upwards [hbarrier.eventually_gt_atTop (M + 1), hquadratic] with x hxbarrier hxquadratic
    dsimp [logCosBarrierMinusHalfSqSeed] at hxbarrier hxquadratic ⊢
    nlinarith
  filter_upwards [logCosBarrierMinusHalfSqOpenInterval_eventuallyEq_seed_at_one, hseed] with x
      hxEq hxSeed
  rw [hxEq]
  exact_mod_cast hxSeed

/-- Helper for Example 24.45: the left endpoint `-1` has one-sided `liminf` above `⊥`. -/
private theorem logCosBarrierMinusHalfSqOpenInterval_neg_one_liminf_gt_bot (x : ℝ)
    (hx : (-1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : x = -1 := by
    have hxE : (((-1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (-1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The explicit `+∞` boundary limit forces the right-sided liminf above `⊥`.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Ioi_neBot le_rfl)
    logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_neg_one bot_lt_top

/-- Helper for Example 24.45: the right endpoint `1` has one-sided `liminf` above `⊥`. -/
private theorem logCosBarrierMinusHalfSqOpenInterval_one_liminf_gt_bot (x : ℝ)
    (hx : (1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Iio x)) := by
  have hx' : x = 1 := by
    have hxE : (((1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The explicit `+∞` boundary limit forces the left-sided liminf above `⊥`.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Iio_neBot le_rfl)
    logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_one bot_lt_top

/-- Helper for Example 24.45: the textbook barrier agrees with the canonical one-sided-limit
extension of its open-interval seed. -/
-- TODO: split into the interior branch, the two endpoint `liminf = +∞` branches, and the
-- exterior `+∞` branch of `oneSidedLimitExtensionEReal`.
private theorem log_cos_barrier_minus_half_sq_eq_oneSidedLimitExtension :
    log_cos_barrier_minus_half_sq =
      oneSidedLimitExtension logCosBarrierMinusHalfSqOpenInterval (-1) 1
        (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_neg_one_liminf_gt_bot x hx)
        (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_one_liminf_gt_bot x hx) :=
  by
    funext x
    apply Subtype.ext
    by_cases hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1
    · -- On the interior interval, both functions evaluate through the finite branch.
      have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
        simpa [erealOpenInterval_neg_one_one] using hxIoo
      rw [oneSidedLimitExtension_coe]
      simp [oneSidedLimitExtensionEReal, hxE, log_cos_barrier_minus_half_sq_apply_of_mem_Ioo hxIoo,
        logCosBarrierMinusHalfSqOpenInterval, finiteOnOpenInterval]
    · by_cases hx_neg_one : x = -1
      · -- At `-1`, the extension inserts the computed right-sided liminf `+∞`.
        subst x
        have hliminf :
            Filter.liminf (fun y : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval y : EReal))
              (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) = ⊤ := by
          exact logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_neg_one.liminf_eq
        rw [oneSidedLimitExtension_coe]
        simp [oneSidedLimitExtensionEReal, hliminf, log_cos_barrier_minus_half_sq_apply_of_not_mem_Ioo,
          erealOpenInterval_neg_one_one]
      · by_cases hx_one : x = 1
        · -- At `1`, the left-sided liminf is again `+∞`.
          subst x
          have hliminf :
              Filter.liminf (fun y : ℝ ↦ (logCosBarrierMinusHalfSqOpenInterval y : EReal))
                (nhdsWithin (1 : ℝ) (Set.Iio 1)) = ⊤ := by
            exact logCosBarrierMinusHalfSqOpenInterval_tendsto_top_at_one.liminf_eq
          have hmem : (1 : ℝ) ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
            rw [erealOpenInterval_neg_one_one]
            norm_num
          have hleft : ¬ (-1 : EReal) = ((1 : ℝ) : EReal) := by
            intro h
            have h' : (((-1 : ℝ) : EReal) = ((1 : ℝ) : EReal)) := by
              simpa using h
            have : (-1 : ℝ) = 1 := by
              exact_mod_cast h'
            norm_num at this
          have hone : (1 : EReal) = ((1 : ℝ) : EReal) := by
            norm_num
          have hx_one_not_mem : (1 : ℝ) ∉ Set.Ioo (-1 : ℝ) 1 := by
            norm_num
          rw [oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal]
          rw [if_neg hmem, if_neg hleft, if_pos hone]
          simpa [hliminf] using log_cos_barrier_minus_half_sq_apply_of_not_mem_Ioo hx_one_not_mem
        · -- Away from the closed interval, both definitions are on the exterior `+∞` branch.
          have hxnotmem : x ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
            simpa [erealOpenInterval_neg_one_one] using hxIoo
          have hxleft : ¬ (-1 : EReal) = (x : EReal) := by
            intro h
            have hE : (((-1 : ℝ) : EReal) = (x : EReal)) := by
              simpa using h
            have h' : (-1 : ℝ) = x := by
              exact_mod_cast hE
            exact hx_neg_one h'.symm
          have hxright : ¬ (1 : EReal) = (x : EReal) := by
            intro h
            have hE : (((1 : ℝ) : EReal) = (x : EReal)) := by
              simpa using h
            have h' : (1 : ℝ) = x := by
              exact_mod_cast hE
            exact hx_one h'.symm
          rw [oneSidedLimitExtension_coe]
          simp [oneSidedLimitExtensionEReal, hxnotmem,
            log_cos_barrier_minus_half_sq_apply_of_not_mem_Ioo hxIoo, hxleft, hxright]

/-- The log-cos barrier example belongs to `Γ₀(ℝ)`. -/
-- TODO: after proving strict convexity of the finite seed and the extension identity, apply
-- `oneSidedLimitExtension_mem_gammaZero` and rewrite back to the textbook function.
theorem log_cos_barrier_minus_half_sq_mem_gammaZero :
    log_cos_barrier_minus_half_sq ∈ Γ₀(ℝ) :=
  by
    -- Proposition 9.34 applies to the finite open-interval model once strict convexity is known.
    have hmem :
        oneSidedLimitExtension logCosBarrierMinusHalfSqOpenInterval (-1) 1
            (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_neg_one_liminf_gt_bot x hx)
            (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_one_liminf_gt_bot x hx) ∈
          Γ₀(ℝ) := by
      have hdom :
          effectiveDomain logCosBarrierMinusHalfSqOpenInterval =
            erealOpenInterval (-1 : EReal) (1 : EReal) := by
        simpa [logCosBarrierMinusHalfSqOpenInterval] using
          finiteOnOpenInterval_effectiveDomain logCosBarrierMinusHalfSqSeed (-1) 1
      have hstrict : StrictlyConvex logCosBarrierMinusHalfSqOpenInterval := by
        simpa [logCosBarrierMinusHalfSqOpenInterval] using
          strictlyConvex_finiteOnOpenInterval_of_strictConvexOn
            (α := (-1 : EReal)) (β := (1 : EReal)) (by
              simpa [erealOpenInterval_neg_one_one] using logCosBarrierMinusHalfSqSeed_strictConvexOn)
      exact oneSidedLimitExtension_mem_gammaZero logCosBarrierMinusHalfSqOpenInterval (-1) 1
        (by
          have h : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
            exact EReal.coe_lt_coe_iff.2 (by norm_num)
          simpa using h) hdom hstrict
        (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_neg_one_liminf_gt_bot x hx)
        (fun {x} hx ↦ logCosBarrierMinusHalfSqOpenInterval_one_liminf_gt_bot x hx)
    -- Rewrite the canonical extension result back to the textbook function.
    simpa [log_cos_barrier_minus_half_sq_eq_oneSidedLimitExtension] using hmem

/-- Helper for Example 24.45: the scaled arctangent candidate lies in the interior effective
domain of the log-cos barrier. -/
-- TODO: rewrite `(2 / π) * arctan x` as `arctan x / (π / 2)` and transport
-- `Real.arctan_mem_Ioo x` through division by the positive scalar `π / 2`.
private theorem scaled_arctan_mem_interior_effectiveDomain_log_cos_barrier_minus_half_sq (x : ℝ) :
    (2 / Real.pi) * Real.arctan x ∈ interior (effectiveDomain log_cos_barrier_minus_half_sq) := by
  -- The scaled arctangent stays inside `(-1,1)` because `arctan x ∈ (-π/2, π/2)`.
  have hp_mem : (2 / Real.pi) * Real.arctan x ∈ Set.Ioo (-1 : ℝ) 1 := by
    have hscale :
        (2 / Real.pi) * Real.arctan x = Real.arctan x / (Real.pi / 2) := by
      field_simp [Real.pi_ne_zero]
    constructor
    · rw [hscale]
      rw [lt_div_iff₀]
      · nlinarith [Real.neg_pi_div_two_lt_arctan x]
      · positivity
    · rw [hscale]
      rw [div_lt_iff₀]
      · nlinarith [Real.arctan_lt_pi_div_two x]
      · positivity
  simpa [log_cos_barrier_minus_half_sq_effectiveDomain, isOpen_Ioo.interior_eq] using hp_mem

/-- Helper for Example 24.45: at the scaled arctangent point, the Gâteaux gradient of the finite
representative is `x - (2 / π) arctan x`. -/
-- TODO: use the interior-branch eventual equality to transfer the scalar derivative of the seed
-- to the `toReal` representative of the barrier, then identify the resulting `toSpanSingleton`
-- map with `InnerProductSpace.toDualMap` on `ℝ`.
private theorem scaled_arctan_hasGateauxDerivative_log_cos_barrier_minus_half_sq (x : ℝ) :
    HasGateauxDerivativeAt
      (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal)
      (InnerProductSpace.toDualMap ℝ ℝ (x - (2 / Real.pi) * Real.arctan x))
      ((2 / Real.pi) * Real.arctan x) :=
  by
    let p : ℝ := (2 / Real.pi) * Real.arctan x
    have hp_mem : p ∈ Set.Ioo (-1 : ℝ) 1 := by
      -- The candidate point is the scaled arctangent from the previous lemma.
      simpa [p, log_cos_barrier_minus_half_sq_effectiveDomain, isOpen_Ioo.interior_eq] using
        scaled_arctan_mem_interior_effectiveDomain_log_cos_barrier_minus_half_sq x
    have hseed_eventually :
        (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal) =ᶠ[𝓝 p]
          logCosBarrierMinusHalfSqSeed := by
      -- In a neighborhood of `p`, the barrier stays on its finite interior branch.
      have hnhds : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 p := isOpen_Ioo.mem_nhds hp_mem
      filter_upwards [hnhds] with ξ hξ
      exact log_cos_barrier_minus_half_sq_toReal_of_mem_Ioo hξ
    have hscaled_eval : (Real.pi / 2) * p = Real.arctan x := by
      -- The scaling constants are mutual inverses.
      dsimp [p]
      field_simp [Real.pi_ne_zero]
    have hseed_deriv :
        HasDerivAt logCosBarrierMinusHalfSqSeed (x - p) p := by
      -- Evaluate the closed derivative formula at the arctangent point.
      have hraw :
          HasDerivAt logCosBarrierMinusHalfSqSeed
            (Real.tan ((Real.pi / 2) * p) - p) p :=
        logCosBarrierMinusHalfSqSeed_hasDerivAt hp_mem
      refine hraw.congr_deriv ?_
      rw [hscaled_eval, Real.tan_arctan]
    have htarget_deriv :
        HasDerivAt
          (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal)
          (x - p) p := by
      exact hseed_deriv.congr_of_eventuallyEq hseed_eventually
    have hgrad :
        HasGradientAt
          (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal)
          (x - p) p := by
      exact htarget_deriv.hasGradientAt'
    have hGateaux :
        HasGateauxDerivativeAt
          (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal)
          (InnerProductSpace.toDual ℝ ℝ (x - p)) p := by
      exact hgrad.hasFDerivAt.hasGateauxDerivativeAt
    simpa [p, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hGateaux

/-- Example 24.45: if `φ(ξ) = -(2 / π) log (cos ((π / 2) ξ)) - ξ² / 2` for `|ξ| < 1` and
`φ(ξ) = +∞` for `|ξ| ≥ 1`, then `Prox_φ = (2 / π) arctan`. -/
-- TODO: once the candidate point is known to lie in `interior (effectiveDomain φ)` and its
-- Gâteaux gradient is identified as `x - p`, close with Proposition 24.1.
theorem prox_log_cos_barrier_minus_half_sq_eq_arctan :
    Prox[log_cos_barrier_minus_half_sq, log_cos_barrier_minus_half_sq_mem_gammaZero] =
      fun x : ℝ ↦ (2 / Real.pi) * Real.arctan x :=
  by
    funext x
    let p : ℝ := (2 / Real.pi) * Real.arctan x
    have hp :
        p ∈ interior (effectiveDomain log_cos_barrier_minus_half_sq) := by
      -- The proximal candidate lies in the interior effective domain.
      simpa [p] using scaled_arctan_mem_interior_effectiveDomain_log_cos_barrier_minus_half_sq x
    have hgrad :
        HasGateauxDerivativeAt
          (fun ξ ↦ (log_cos_barrier_minus_half_sq ξ : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ ℝ (x - p))
          p := by
      -- Its Gâteaux gradient is the residual `x - p`.
      simpa [p] using scaled_arctan_hasGateauxDerivative_log_cos_barrier_minus_half_sq x
    have hprox :
        p = Prox[log_cos_barrier_minus_half_sq, log_cos_barrier_minus_half_sq_mem_gammaZero] x := by
      -- Proposition 24.1 closes the proximal identity from `grad φ(p) + p = x`.
      exact
        (eq_proximityOperator_iff_gateauxGradient_add_eq
          log_cos_barrier_minus_half_sq log_cos_barrier_minus_half_sq_mem_gammaZero hp hgrad).2
          (by
            dsimp [p]
            abel_nf)
    simpa [p] using hprox.symm

end ERealFunction
