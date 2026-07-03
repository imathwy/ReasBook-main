import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.LeftRightLim

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_5_24_2 (from Chap05) -/
noncomputable section

open Filter
open scoped Rockafellar Topology

namespace Function

variable {𝕜 : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: this example gives a concrete convex but nonclosed function on an ordered scalar
  line `𝕜`, for which the left-limit identity from Theorem 5.24.1 fails.
- `core/canonical`: the owner abstractions are the chapter one-dimensional derivative owners
  `Function.rightDerivative` and `Function.leftDerivative`, together with the canonical strict
  one-sided limit owner `Function.leftLim` and the ambient closedness owners
  `LowerSemicontinuousAt` / `LowerSemicontinuous`, plus the chapter owner predicates
  `Function.IsConvex 𝕜`, `Function.IsProper`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the source example is not a new derivative-profile owner; it is the explicit
  counterexample function together with owner-level convexity/properness data, the failure of the
  closed-proper-convex owner, and the derivative formulas showing that
  `(rightDerivative f).leftLim 0 ≠ leftDerivative f 0`.
- Domain-style sampling used here: the chapter owners `Function.IsConvex 𝕜`,
  `Function.IsProper`, and `Function.IsClosedProperConvex`; mathlib's
  `LowerSemicontinuousAt` / `LowerSemicontinuous`, the one-sided filter notation `𝓝[<] x` and
  strict-limit owner `leftLim`; and the chapter derivative owners `Function.rightDerivative`,
  `Function.leftDerivative`, together with the owner theorem `Function.leftLim_rightDerivative`
  from `Theorem_5_24_1`, whose conclusion this example shows can fail without closedness.
- Primitive data vs derived API:
  - primitive data: the explicit extended-real-valued function on `𝕜`;
  - derived API: owner-level convexity and properness of the explicit function, failure of the
    closedness owner already at the boundary point `0`, the global non-lower-semicontinuity
    consequence, the explicit owner-level right-derivative profile, the explicit owner-level left
    derivative at `0`, the strict left limit of the right derivative at `0`, and the resulting
    failure of the Chapter 24 identity.
- Layer target: `source-facing`, via the explicit counterexample function from the text.
-/

/-- The explicit Chapter 24 counterexample: it is `0` on `(-∞, 0)`, `1` at `0`, and `+∞` on
`(0, ∞)`. -/
def leftRayBoundaryJumpFunction (𝕜 : Type*) [Preorder 𝕜] [Zero 𝕜] [One 𝕜] :
    𝕜 → WithBotTop 𝕜 := by
  classical
  exact fun x ↦
    if x < (0 : 𝕜) then ((0 : 𝕜) : WithBotTop 𝕜)
    else if x = (0 : 𝕜) then ((1 : 𝕜) : WithBotTop 𝕜)
    else ⊤

/-- On the open left ray `(-∞, 0)`, the counterexample has value `0`. -/
@[simp] theorem leftRayBoundaryJumpFunction_of_lt [Preorder 𝕜] [Zero 𝕜] [One 𝕜]
    {x : 𝕜} (hx : x < 0) :
    leftRayBoundaryJumpFunction 𝕜 x = 0 := by
  classical
  simp [leftRayBoundaryJumpFunction, hx]

/-- At the boundary point `0`, the counterexample takes the value `1`. -/
@[simp] theorem leftRayBoundaryJumpFunction_zero [Preorder 𝕜] [Zero 𝕜] [One 𝕜] :
    leftRayBoundaryJumpFunction 𝕜 (0 : 𝕜) = (1 : WithBotTop 𝕜) := by
  classical
  unfold leftRayBoundaryJumpFunction
  simp
  rfl

/-- On the open right ray `(0, ∞)`, the counterexample takes the value `+∞`. -/
@[simp] theorem leftRayBoundaryJumpFunction_of_pos [Preorder 𝕜] [Zero 𝕜] [One 𝕜]
    {x : 𝕜} (hx : 0 < x) :
    leftRayBoundaryJumpFunction 𝕜 x = ⊤ := by
  classical
  unfold leftRayBoundaryJumpFunction
  split_ifs with hlt heq
  · exact (not_lt_of_gt hx hlt).elim
  · exact (hx.ne' heq).elim
  · rfl

section Ordered

variable [LinearOrder 𝕜] [Zero 𝕜] [One 𝕜]

/-- The effective domain of the counterexample is the closed left ray `(-∞, 0]`. -/
theorem mem_dom_leftRayBoundaryJumpFunction_iff {x : 𝕜} :
    x ∈ dom(leftRayBoundaryJumpFunction 𝕜) ↔ x ≤ 0 := by
  rw [mem_effectiveDomain]
  by_cases hx : x < 0
  · have hxle : x ≤ 0 := hx.le
    constructor
    · intro _
      exact hxle
    · intro _
      simpa [leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hx] using
        (WithBotTop.coe_lt_top (0 : 𝕜))
  · by_cases hx0 : x = 0
    · subst hx0
      constructor
      · intro _
        exact le_rfl
      · intro _
        simpa [leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using
          (WithBotTop.coe_lt_top (1 : 𝕜))
    · have hxle : 0 ≤ x := not_lt.mp hx
      have hxpos : 0 < x := lt_of_le_of_ne hxle (Ne.symm hx0)
      have hxnle : ¬ x ≤ 0 := not_le.mpr hxpos
      simp [leftRayBoundaryJumpFunction_of_pos (𝕜 := 𝕜) hxpos, hxnle]

/-- The Chapter 24 counterexample is proper: it is finite at `0` and nowhere equals `-∞`. -/
theorem leftRayBoundaryJumpFunction_isProper :
    (leftRayBoundaryJumpFunction 𝕜).IsProper := by
  rw [Function.isProper_iff]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · change leftRayBoundaryJumpFunction 𝕜 0 < ⊤
    rw [leftRayBoundaryJumpFunction_zero]
    exact WithBotTop.coe_lt_top 1
  · intro x
    by_cases hx : x < 0
    · rw [leftRayBoundaryJumpFunction_of_lt hx]
      simp
    · by_cases hx0 : x = 0
      · rw [hx0, leftRayBoundaryJumpFunction_zero]
        change ((1 : 𝕜) : WithBotTop 𝕜) ≠ ⊥
        simp
      · have hxne : 0 ≠ x := by simpa [eq_comm] using hx0
        have hxpos : 0 < x := lt_of_le_of_ne (not_lt.mp hx) hxne
        rw [leftRayBoundaryJumpFunction_of_pos hxpos]
        simp

end Ordered

section Convexity

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The Chapter 24 counterexample is convex in the chapter epigraph sense. -/
theorem leftRayBoundaryJumpFunction_isConvex :
    (leftRayBoundaryJumpFunction 𝕜).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_lt_affine_upper_bound]
  intro x y α β t hx hy ht0 ht1
  have hx_mem_dom : x ∈ dom(leftRayBoundaryJumpFunction 𝕜) := by
    exact (mem_effectiveDomain).2 (lt_trans hx (WithBotTop.coe_lt_top α))
  have hy_mem_dom : y ∈ dom(leftRayBoundaryJumpFunction 𝕜) := by
    exact (mem_effectiveDomain).2 (lt_trans hy (WithBotTop.coe_lt_top β))
  have hx_le : x ≤ 0 := (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).1 hx_mem_dom
  have hy_le : y ≤ 0 := (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).1 hy_mem_dom
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht1
  have hγ_pos : 0 < (1 - t) * α + t * β := by
    have hα_pos : 0 < α := by
      by_cases hx0 : x = 0
      · have hα_gt1 : (1 : 𝕜) < α := by
          exact WithBotTop.coe_lt_coe.mp (by
            simpa [hx0, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using hx)
        exact lt_trans zero_lt_one hα_gt1
      · have hxlt : x < 0 := lt_of_le_of_ne hx_le (by simpa [eq_comm] using hx0)
        have hα_gt0 : (0 : 𝕜) < α := by
          exact WithBotTop.coe_lt_coe.mp (by
            simpa [leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hxlt] using hx)
        exact hα_gt0
    have hβ_pos : 0 < β := by
      by_cases hy0 : y = 0
      · have hβ_gt1 : (1 : 𝕜) < β := by
          exact WithBotTop.coe_lt_coe.mp (by
            simpa [hy0, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using hy)
        exact lt_trans zero_lt_one hβ_gt1
      · have hylt : y < 0 := lt_of_le_of_ne hy_le (by simpa [eq_comm] using hy0)
        have hβ_gt0 : (0 : 𝕜) < β := by
          exact WithBotTop.coe_lt_coe.mp (by
            simpa [leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hylt] using hy)
        exact hβ_gt0
    exact add_pos
      (mul_pos h1t_pos hα_pos)
      (mul_pos ht0 hβ_pos)
  let z : 𝕜 := (1 - t) * x + t * y
  have hz_le : z ≤ 0 := by
    dsimp [z]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1.le) hx_le)
      (mul_nonpos_of_nonneg_of_nonpos ht0.le hy_le)
  rcases lt_or_eq_of_le hz_le with hzlt | hz0
  · have hz_value : leftRayBoundaryJumpFunction 𝕜 z = 0 := by
      exact leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hzlt
    have hγ_pos' : (0 : WithBotTop 𝕜) < ((1 - t) * α + t * β : 𝕜) := by
      exact WithBotTop.coe_lt_coe.mpr hγ_pos
    simpa [z, hz_value] using hγ_pos'
  · have hx_not_lt : ¬ x < 0 := by
      intro hxlt
      have hzlt' : z < 0 := by
        dsimp [z]
        simpa using add_lt_add_of_lt_of_le
          (mul_neg_of_pos_of_neg h1t_pos hxlt)
          (mul_nonpos_of_nonneg_of_nonpos ht0.le hy_le)
      have hz0lt0 : (0 : 𝕜) < 0 := by
        rwa [hz0] at hzlt'
      exact (lt_irrefl (0 : 𝕜) hz0lt0).elim
    have hy_not_lt : ¬ y < 0 := by
      intro hylt
      have hzlt' : z < 0 := by
        dsimp [z]
        simpa using add_lt_add_of_le_of_lt
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1.le) hx_le)
          (mul_neg_of_pos_of_neg ht0 hylt)
      have hz0lt0 : (0 : 𝕜) < 0 := by
        rwa [hz0] at hzlt'
      exact (lt_irrefl (0 : 𝕜) hz0lt0).elim
    have hx_zero : x = 0 := le_antisymm hx_le (not_lt.mp hx_not_lt)
    have hy_zero : y = 0 := le_antisymm hy_le (not_lt.mp hy_not_lt)
    have hα_gt1 : (1 : 𝕜) < α := by
      exact WithBotTop.coe_lt_coe.mp (by
        simpa [hx_zero, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using hx)
    have hβ_gt1 : (1 : 𝕜) < β := by
      exact WithBotTop.coe_lt_coe.mp (by
        simpa [hy_zero, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using hy)
    have hγ_gt1 : (1 : 𝕜) < (1 - t) * α + t * β := by
      have hmain :
          (1 - t) * (1 : 𝕜) + t * (1 : 𝕜) < (1 - t) * α + t * β := by
        exact add_lt_add
          (mul_lt_mul_of_pos_left hα_gt1 h1t_pos)
          (mul_lt_mul_of_pos_left hβ_gt1 ht0)
      have hone : (1 : 𝕜) = (1 - t) * (1 : 𝕜) + t * (1 : 𝕜) := by ring
      calc
        (1 : 𝕜) = (1 - t) * (1 : 𝕜) + t * (1 : 𝕜) := hone
        _ < (1 - t) * α + t * β := hmain
    have hγ_gt1' : ((1 : 𝕜) : WithBotTop 𝕜) < ((1 - t) * α + t * β : 𝕜) := by
      exact WithBotTop.coe_lt_coe.mpr hγ_gt1
    simpa [z, hz0, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)] using hγ_gt1'

end Convexity

section TopologicalClosedness

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- The counterexample already fails lower semicontinuity at the boundary point `0`. -/
-- Proof sketch: along points `x < 0` tending to `0`, the function value is constantly `0`, while
-- the value at `0` is `1`, so lower semicontinuity fails at the boundary.
theorem leftRayBoundaryJumpFunction_not_lowerSemicontinuousAt_zero :
    ¬ LowerSemicontinuousAt (leftRayBoundaryJumpFunction 𝕜) (0 : 𝕜) := by
  intro h
  have hwithin :
      LowerSemicontinuousWithinAt (leftRayBoundaryJumpFunction 𝕜) (Set.Iio (0 : 𝕜)) (0 : 𝕜) :=
    h.lowerSemicontinuousWithinAt (Set.Iio (0 : 𝕜))
  rw [lowerSemicontinuousWithinAt_iff] at hwithin
  have hpos :
      ∀ᶠ x in 𝓝[Set.Iio (0 : 𝕜)] (0 : 𝕜),
        (0 : WithBotTop 𝕜) < leftRayBoundaryJumpFunction 𝕜 x := by
    have h0ltfx0 : (0 : WithBotTop 𝕜) < leftRayBoundaryJumpFunction 𝕜 (0 : 𝕜) := by
      rw [leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)]
      exact WithBotTop.coe_lt_coe.mpr (zero_lt_one : (0 : 𝕜) < 1)
    exact hwithin 0 h0ltfx0
  have hzero :
      ∀ᶠ x in 𝓝[Set.Iio (0 : 𝕜)] (0 : 𝕜),
        leftRayBoundaryJumpFunction 𝕜 x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hx
  have hfalse : ∀ᶠ x in 𝓝[Set.Iio (0 : 𝕜)] (0 : 𝕜), False := by
    filter_upwards [hpos, hzero] with x hxpos hxzero
    have hcontra : (0 : WithBotTop 𝕜) < (0 : WithBotTop 𝕜) := by
      calc
        (0 : WithBotTop 𝕜) < leftRayBoundaryJumpFunction 𝕜 x := hxpos
        _ = (0 : WithBotTop 𝕜) := by simp [hxzero]
    exact (lt_irrefl (0 : WithBotTop 𝕜) hcontra).elim
  have hne : NeBot (𝓝[Set.Iio (0 : 𝕜)] (0 : 𝕜)) :=
    nhdsWithin_Iio_neBot (a := (0 : 𝕜)) (b := (0 : 𝕜)) le_rfl
  exact hne.ne (eventually_false_iff_eq_bot.mp hfalse)

-- The counterexample is not closed, hence not lower semicontinuous.
theorem leftRayBoundaryJumpFunction_not_lowerSemicontinuous :
    ¬ LowerSemicontinuous (leftRayBoundaryJumpFunction 𝕜) := by
  intro h
  exact leftRayBoundaryJumpFunction_not_lowerSemicontinuousAt_zero (h.lowerSemicontinuousAt 0)

variable [TopologicalSpace (WithBotTop 𝕜)]

/-- The explicit counterexample is convex and proper, but it is not closed, so it does not
satisfy the closed-proper-convex owner required by Theorem 5.24.1. -/
theorem leftRayBoundaryJumpFunction_not_isClosedProperConvex :
    ¬ IsClosedProperConvex[𝕜] (leftRayBoundaryJumpFunction 𝕜) := by
  intro h
  exact leftRayBoundaryJumpFunction_not_lowerSemicontinuous h.closed

end TopologicalClosedness

section Derivative

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]

/-- The Chapter 24 owner `Function.rightDerivative` has the explicit profile stated in the
counterexample. -/
theorem rightDerivative_leftRayBoundaryJumpFunction (x : 𝕜) :
    (leftRayBoundaryJumpFunction 𝕜)′+ x = if x < 0 then 0 else ⊤ := by
  by_cases hx : x < 0
  · simp [hx]
    let f : 𝕜 → WithBotTop 𝕜 := leftRayBoundaryJumpFunction 𝕜
    change sInf (Function.directionalDifferenceQuotientAt f x 1 ''
      {t : 𝕜 | 0 < t ∧ f (x + t) < ⊤}) = 0
    have hx_val : f x = 0 := by
      simpa [f] using leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hx
    have hnonneg :
        ∀ a ∈ Function.directionalDifferenceQuotientAt f x 1 '' {t : 𝕜 | 0 < t ∧ f (x + t) < ⊤},
          (0 : WithBotTop 𝕜) ≤ a := by
      intro a ha
      rcases ha with ⟨t, ht, rfl⟩
      rcases ht with ⟨ht_pos, ht_fin⟩
      have hxt_dom : x + t ∈ dom(f) := (mem_effectiveDomain).2 ht_fin
      have hxt_le : x + t ≤ 0 := (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).1 (by
        simpa [f] using hxt_dom)
      rcases lt_or_eq_of_le hxt_le with hxt_lt | hxt_eq
      · have hxt_val : f (x + t) = 0 := by
          simpa [f] using leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hxt_lt
        unfold Function.directionalDifferenceQuotientAt
        rw [show x + t • (1 : 𝕜) = x + t by simp, hxt_val, hx_val]
        simp
      · have hxt_val : f (x + t) = 1 := by
          simp [f, hxt_eq, leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)]
        unfold Function.directionalDifferenceQuotientAt
        rw [show x + t • (1 : 𝕜) = x + t by simp, hxt_val, hx_val]
        refine le_of_lt ?_
        have hdiv_pos : (0 : WithBotTop 𝕜) < ((t : WithBotTop 𝕜)⁻¹) := by
          simpa [div_eq_mul_inv, WithBotTop.coe_inv] using
            (WithBotTop.coe_lt_coe.mpr (div_pos zero_lt_one ht_pos))
        have hsub : (1 - (0 : WithBotTop 𝕜)) = (1 : WithBotTop 𝕜) := by simp
        rw [hsub, WithBotTop.div_eq_mul_inv]
        have hone :
            (1 : WithBotTop 𝕜) * ((t : WithBotTop 𝕜)⁻¹) = ((t : WithBotTop 𝕜)⁻¹) := by
          have hcoeinv : ((t : WithBotTop 𝕜)⁻¹) = ((t⁻¹ : 𝕜) : WithBotTop 𝕜) := by
            simp [WithBotTop.coe_inv]
          rw [hcoeinv]
          change
            ((1 : 𝕜) : WithBotTop 𝕜) * ((t⁻¹ : 𝕜) : WithBotTop 𝕜) =
              ((t⁻¹ : 𝕜) : WithBotTop 𝕜)
          rw [← WithBotTop.coe_mul]
          simp
        rw [hone]
        exact hdiv_pos
    have hzero_mem :
        (0 : WithBotTop 𝕜) ∈ Function.directionalDifferenceQuotientAt f x 1 ''
          {t : 𝕜 | 0 < t ∧ f (x + t) < ⊤} := by
      refine ⟨(-x / 2), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · nlinarith [hx]
        · have hxhalf_lt : x + (-x / 2) < 0 := by nlinarith [hx]
          have hxhalf_val : f (x + (-x / 2)) = 0 := by
            simpa [f] using leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hxhalf_lt
          rw [hxhalf_val]
          exact WithBotTop.coe_lt_top 0
      · unfold Function.directionalDifferenceQuotientAt
        have hxhalf_lt : x + (-x / 2) < 0 := by nlinarith [hx]
        have hxhalf_val : f (x + (-x / 2)) = 0 := by
          simpa [f] using leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hxhalf_lt
        rw [show x + (-x / 2) • (1 : 𝕜) = x + (-x / 2) by simp, hxhalf_val, hx_val]
        simp
    refine le_antisymm ?_ ?_
    · exact sInf_le hzero_mem
    · exact le_sInf hnonneg
  · have hx_nonneg : 0 ≤ x := not_lt.mp hx
    simp [hx]
    change
      sInf (Function.directionalDifferenceQuotientAt (leftRayBoundaryJumpFunction 𝕜) x 1 ''
        {t : 𝕜 | 0 < t ∧ leftRayBoundaryJumpFunction 𝕜 (x + t) < ⊤}) = ⊤
    have hempty :
        {t : 𝕜 | 0 < t ∧ leftRayBoundaryJumpFunction 𝕜 (x + t) < ⊤} = ∅ := by
      ext t
      constructor
      · intro ht
        rcases ht with ⟨ht_pos, ht_fin⟩
        have ht_dom : x + t ∈ dom(leftRayBoundaryJumpFunction 𝕜) :=
          (mem_effectiveDomain).2 ht_fin
        have hxt_le : x + t ≤ 0 :=
          (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).1 ht_dom
        have hxt_pos : 0 < x + t := lt_of_lt_of_le ht_pos (le_add_of_nonneg_left hx_nonneg)
        exact (not_lt_of_ge hxt_le hxt_pos).elim
      · intro ht
        cases ht
    simp [hempty]

/-- The Chapter 24 owner `Function.leftDerivative` takes the value `+∞` at the boundary point
`0` for this counterexample. -/
theorem leftDerivative_leftRayBoundaryJumpFunction_zero :
    (leftRayBoundaryJumpFunction 𝕜)′- 0 = ⊤ := by
  let S : Set (WithBotTop 𝕜) :=
    (fun t : 𝕜 ↦ -directionalDifferenceQuotientAt (leftRayBoundaryJumpFunction 𝕜) 0 (-1) t) ''
      {t : 𝕜 | 0 < t ∧ (0 : 𝕜) - t ∈ dom(leftRayBoundaryJumpFunction 𝕜)}
  have hleft : (leftRayBoundaryJumpFunction 𝕜)′- 0 = sSup S := by
    rfl
  rw [hleft]
  refine (sSup_eq_top).2 ?_
  intro b hb
  cases b using WithBotTop.rec with
  | bot =>
      let t : 𝕜 := 1
      have ht : 0 < t := by
        dsimp [t]
        exact zero_lt_one
      have hdom : (0 : 𝕜) - t ∈ dom(leftRayBoundaryJumpFunction 𝕜) := by
        refine (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).2 ?_
        dsimp [t]
        linarith
      have hslope :
          -directionalDifferenceQuotientAt (leftRayBoundaryJumpFunction 𝕜) 0 (-1) t =
            (((1 : 𝕜) / t : 𝕜) : WithBotTop 𝕜) := by
        unfold directionalDifferenceQuotientAt
        have harg : (0 : 𝕜) + t • (-1 : 𝕜) = -t := by
          simp [smul_eq_mul]
        rw [harg]
        have hlt : -t < (0 : 𝕜) := by
          have : (0 : 𝕜) < t := ht
          linarith
        rw [leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hlt,
          leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)]
        have hsub : ((0 : WithBotTop 𝕜) - (1 : WithBotTop 𝕜)) = (-1 : WithBotTop 𝕜) := by
          norm_num
        rw [hsub]
        simp [WithBotTop.div_eq_mul_inv, div_eq_mul_inv, WithBotTop.coe_inv]
        have hmul :
            (-1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹ =
              -((1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹) := by
          simpa using
            (WithBotTop.neg_mul (x := (1 : WithBotTop 𝕜)) (y := (WithBotTop.coe t)⁻¹))
        calc
          -(-1 * (WithBotTop.coe t)⁻¹) = -(-((1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹)) := by
            rw [hmul]
          _ = (1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹ := by simp
          _ = (WithBotTop.coe t)⁻¹ := by
            have hcoeinv : (WithBotTop.coe t)⁻¹ = ((t⁻¹ : 𝕜) : WithBotTop 𝕜) := by
              simp [WithBotTop.coe_inv]
            rw [hcoeinv]
            change
              ((1 : 𝕜) : WithBotTop 𝕜) * ((t⁻¹ : 𝕜) : WithBotTop 𝕜) =
                ((t⁻¹ : 𝕜) : WithBotTop 𝕜)
            rw [← WithBotTop.coe_mul]
            simp
      refine ⟨((1 : 𝕜) / t : 𝕜), ?_, ?_⟩
      · refine ⟨t, ⟨ht, hdom⟩, ?_⟩
        simp [hslope]
      · have hbot : (⊥ : WithBotTop 𝕜) < (((1 : 𝕜) / t : 𝕜) : WithBotTop 𝕜) :=
          WithBotTop.bot_lt_coe (((1 : 𝕜) / t : 𝕜))
        simpa using hbot
  | coe β =>
      let c : 𝕜 := |β| + 1
      let t : 𝕜 := c⁻¹
      have hc_pos : 0 < c := by
        dsimp [c]
        exact add_pos_of_nonneg_of_pos (abs_nonneg β) zero_lt_one
      have ht : 0 < t := by
        dsimp [t]
        exact inv_pos.mpr hc_pos
      have hdom : (0 : 𝕜) - t ∈ dom(leftRayBoundaryJumpFunction 𝕜) := by
        refine (mem_dom_leftRayBoundaryJumpFunction_iff (𝕜 := 𝕜)).2 ?_
        exact sub_nonpos.mpr ht.le
      have hslope :
          -directionalDifferenceQuotientAt (leftRayBoundaryJumpFunction 𝕜) 0 (-1) t =
            (((1 : 𝕜) / t : 𝕜) : WithBotTop 𝕜) := by
        unfold directionalDifferenceQuotientAt
        have harg : (0 : 𝕜) + t • (-1 : 𝕜) = -t := by
          simp [smul_eq_mul]
        rw [harg]
        have hlt : -t < (0 : 𝕜) := by
          have : (0 : 𝕜) < t := ht
          linarith
        rw [leftRayBoundaryJumpFunction_of_lt (𝕜 := 𝕜) hlt,
          leftRayBoundaryJumpFunction_zero (𝕜 := 𝕜)]
        have hsub : ((0 : WithBotTop 𝕜) - (1 : WithBotTop 𝕜)) = (-1 : WithBotTop 𝕜) := by
          norm_num
        rw [hsub]
        simp [WithBotTop.div_eq_mul_inv, div_eq_mul_inv, WithBotTop.coe_inv]
        have hmul :
            (-1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹ =
              -((1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹) := by
          simpa using
            (WithBotTop.neg_mul (x := (1 : WithBotTop 𝕜)) (y := (WithBotTop.coe t)⁻¹))
        calc
          -(-1 * (WithBotTop.coe t)⁻¹) = -(-((1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹)) := by
            rw [hmul]
          _ = (1 : WithBotTop 𝕜) * (WithBotTop.coe t)⁻¹ := by simp
          _ = (WithBotTop.coe t)⁻¹ := by
            have hcoeinv : (WithBotTop.coe t)⁻¹ = ((t⁻¹ : 𝕜) : WithBotTop 𝕜) := by
              simp [WithBotTop.coe_inv]
            rw [hcoeinv]
            change
              ((1 : 𝕜) : WithBotTop 𝕜) * ((t⁻¹ : 𝕜) : WithBotTop 𝕜) =
                ((t⁻¹ : 𝕜) : WithBotTop 𝕜)
            rw [← WithBotTop.coe_mul]
            simp
      have hbeta_lt_c : β < c := by
        have h1 : β ≤ |β| := le_abs_self β
        have h2 : |β| < |β| + 1 := by
          exact lt_add_of_pos_right _ (show (0 : 𝕜) < 1 by exact zero_lt_one)
        exact lt_of_le_of_lt h1 h2
      have hone_div : (1 : 𝕜) / t = c := by
        dsimp [t]
        calc
          (1 : 𝕜) / c⁻¹ = (1 : 𝕜) * c := by
            rw [div_eq_mul_inv, inv_inv]
          _ = c := by simp
      refine ⟨((1 : 𝕜) / t : 𝕜), ?_, ?_⟩
      · refine ⟨t, ⟨ht, hdom⟩, ?_⟩
        simp [hslope]
      · have hb_lt : (β : WithBotTop 𝕜) < (((1 : 𝕜) / t : 𝕜) : WithBotTop 𝕜) := by
          exact WithBotTop.coe_lt_coe.mpr (by simpa [hone_div] using hbeta_lt_c)
        simpa using hb_lt
  | top =>
      exact (lt_irrefl (⊤ : WithBotTop 𝕜) hb).elim

end Derivative

section DerivativeTopological

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

/-- The canonical strict left limit of the Chapter 24 owner `Function.rightDerivative` at `0` is
`0` for this counterexample. -/
theorem leftLim_rightDerivative_leftRayBoundaryJumpFunction_zero :
    ((leftRayBoundaryJumpFunction 𝕜)′+).leftLim 0 = 0 := by
  have hprofile :
      (leftRayBoundaryJumpFunction 𝕜)′+ =
        fun x : 𝕜 ↦ if x < 0 then (0 : WithBotTop 𝕜) else ⊤ := by
    funext x
    simpa using rightDerivative_leftRayBoundaryJumpFunction x
  rw [hprofile]
  refine leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) ?_
  have hconst :
      Tendsto (fun _ : 𝕜 ↦ (0 : WithBotTop 𝕜)) (𝓝[<] (0 : 𝕜)) (𝓝 (0 : WithBotTop 𝕜)) :=
    tendsto_const_nhds
  have heq :
      (fun _ : 𝕜 ↦ (0 : WithBotTop 𝕜)) =ᶠ[𝓝[<] (0 : 𝕜)]
        fun x : 𝕜 ↦ if x < 0 then (0 : WithBotTop 𝕜) else ⊤ := by
    filter_upwards [show Set.Iio (0 : 𝕜) ∈ 𝓝[<] (0 : 𝕜) by
      exact self_mem_nhdsWithin] with x hx
    have hx' : x < 0 := hx
    simp [hx']
  exact hconst.congr' heq

/-- Example 5.24.2: for the explicit convex proper but nonclosed function that is `0` on
`(-∞, 0)`, `1` at `0`, and `+∞` on `(0, ∞)`, the Chapter 24 identity
`(rightDerivative f).leftLim x = leftDerivative f x` fails at `x = 0`. -/
-- Proof sketch: the previous owner-level formulas give
-- `(rightDerivative leftRayBoundaryJumpFunction).leftLim 0 = 0` and
-- `leftDerivative leftRayBoundaryJumpFunction 0 = ⊤`. Since `0 ≠ ⊤` in `WithBotTop 𝕜`, the
-- Chapter 24 left-limit identity cannot hold at the boundary.
theorem leftLimit_identity_fails_for_leftRayBoundaryJumpFunction :
    ((leftRayBoundaryJumpFunction 𝕜)′+).leftLim 0 ≠
      (leftRayBoundaryJumpFunction 𝕜)′- 0 := by
  rw [leftLim_rightDerivative_leftRayBoundaryJumpFunction_zero,
    leftDerivative_leftRayBoundaryJumpFunction_zero]
  change ((0 : 𝕜) : WithBotTop 𝕜) ≠ ⊤
  simpa using (WithBotTop.coe_ne_top (a := (0 : 𝕜)))

end DerivativeTopological

end Function

/-! ### Proposition_5_24_2 (from Chap05) -/
noncomputable section

universe u v

open Filter
open scoped Topology

section

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_iterated : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.2 studies the directional derivatives of the convex
  direction-function `y ↦ directionalDerivativeAt f x y` at a direction `y` where that value is
  finite, and compares every such iterated directional derivative with the first-order directional
  derivative in the same direction.
- `core/canonical`: the owner abstraction is already the Chapter 23 directional-derivative owner
  `Function.directionalDerivativeAt`; the proposition should therefore remain on
  `directionalDerivativeAt (directionalDerivativeAt f x) y z` rather than introducing a second
  local wrapper such as `secondDirectionalDerivativeAt`.
- `bridge/view`: the first displayed formula in the source is exactly the canonical owner
  definition of `Function.directionalDerivativeAt`, specialized to the function
  `directionalDerivativeAt f x : E → WithTopBot 𝕜`; the only new theorem-level content here is the
  inequality against `directionalDerivativeAt f x z`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from
  `Items/Chap05/Lemma_23_0_1.lean`;
- the chapter effective-domain owner `dom(·)` and its membership bridge
  `mem_effectiveDomain` from `Items/Chap01/Definition_4_4.lean`;
- `Function.directionalDerivativeAt_eq_sInf_directionalDifferenceQuotientAt` from
  `Items/Chap05/Theorem_23_1.lean`, which gives the canonical finite-point owner formula reused
  here for the iterated derivative after the proposition's own finiteness hypotheses are first
  used to recover the missing lower finiteness `f x ≠ ⊥`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point`,
  `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point`, and
  `Function.directionalDerivativeAt_zero_of_finite_point` from
  `Items/Chap05/Theorem_23_1.lean`,
  which are the nearest owner-level regularity package for the direction-function
  `y ↦ directionalDerivativeAt f x y` once that lower finiteness has been recovered.

Primitive data vs derived API:
- primitive data: the convex function `f`, the finite base point `x ∈ dom(f)`, the direction `y`
  where `directionalDerivativeAt f x y` is finite, and the comparison direction `z`;
- primitive owner reused from upstream: `Function.directionalDerivativeAt`;
- owner-side abstraction governing the proof shape: the proposition first derives the missing
  lower finiteness `f x ≠ ⊥` from the finiteness of `directionalDerivativeAt f x y`, then applies
  the finite-point Chapter 23 owner package to the direction-function
  `g := directionalDerivativeAt f x`; Proposition 5.24.2 is therefore a thin owner-level
  inequality for the existing directional-derivative owner rather than a new
  “second directional derivative” API;
- the finite-value hypothesis at the iterated base point is surfaced with the canonical
  primitive owner pair `y ∈ dom(directionalDerivativeAt f x)` and
  `directionalDerivativeAt f x y ≠ ⊥`.
- derived API: the iterated-owner inequality below. The notation-level source identity
  `f'(x; y; z) = lim ...` is not a second owner and is handled by direct recall of the owner
  definition `Function.directionalDerivativeAt`.

Layer target: `bridge/view`. The proposition does not define a new mathematical owner; it gives a
source-facing inequality for the existing Chapter 23 owner.

Ambient-assumption minimization:
- the statement uses only convexity on a scalar-action space and the existing
  `WithTopBot 𝕜`-input directional-derivative owner, so it stays at
  `[AddCommMonoid E] [SMul 𝕜 E]` with the scalar/order/topology assumptions already required by
  the owner package from `Theorem_23_1`;
- no additional norm/topology/inner-product/finite-dimensional structure on `E` is needed on the
  public theorem surface.
-/

/- Proposition 5.24.2 first reuses the canonical Chapter 23 owner definition for directional
derivatives, specialized to the convex direction-function `directionalDerivativeAt f x`. -/
recall Function.directionalDerivativeAt
    {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
    (f : E → WithTopBot 𝕜) (x d : E) : WithTopBot 𝕜 :=
  limUnder (𝓝[>] (0 : 𝕜)) (directionalDifferenceQuotientAt f x d)

-- Proof sketch: first use the proposition's own finiteness hypotheses on
-- `g := directionalDerivativeAt f x` to recover the missing lower finiteness `f x ≠ ⊥`. The
-- finite-point owner package from Theorem 23.1 then applies to `g`, making it convex,
-- positively homogeneous, and normalized by `g 0 = 0`. Apply the owner formula for
-- `directionalDerivativeAt g y z` at the finite point `y`, and bound each positive difference
-- quotient of `g` by the subadditivity estimate `g (y + t • z) ≤ g y + t • g z`.
/-- Owner-level comparison at the primitive directional-function layer: if `g` is convex,
positively homogeneous, normalized by `g 0 = 0`, and finite at `y`, then every directional
derivative of `g` at `y` is bounded above by the first-order value `g z` in the comparison
direction. -/
theorem directionalDerivativeAt_le_of_isConvex_of_positivelyHomogeneous_of_zero
    {g : E → WithTopBot 𝕜}
    (hg_convex : g.IsConvex 𝕜) (hg_hom : g.PositivelyHomogeneous 𝕜) (hg_zero : g 0 = 0)
    {y : E} (hy : y ∈ dom(g)) (hy_bot : g y ≠ ⊥) (z : E) :
    directionalDerivativeAt g y z ≤ g z := by
  sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_second : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

/-- Proposition 5.24.2, owner form: if `f` is convex, `x ∈ dom(f)`, and the directional
derivative `directionalDerivativeAt f x y` is finite, then the directional derivatives of the
convex direction-function `directionalDerivativeAt f x` at `y` are bounded above by the
first-order directional derivative in the same comparison direction. The source notation
`f'(x; y; z)` is represented canonically by
`directionalDerivativeAt (directionalDerivativeAt f x) y z`. -/
theorem iterated_directionalDerivativeAt_le
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) {x : E} (hx : x ∈ dom(f))
    {y : E} (hy : y ∈ dom(directionalDerivativeAt f x))
    (hy_bot : directionalDerivativeAt f x y ≠ ⊥) (z : E) :
    directionalDerivativeAt (directionalDerivativeAt f x) y z ≤ directionalDerivativeAt f x z := by
  have hx_bot : f x ≠ ⊥ := by
    sorry
  let g : E → WithTopBot 𝕜 := directionalDerivativeAt f x
  have hg_convex : g.IsConvex 𝕜 := by
    simpa [g] using
      (Function.isConvex_directionalDerivativeAt_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hg_hom : g.PositivelyHomogeneous 𝕜 := by
    simpa [g] using
      (Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hg_zero : g 0 = 0 := by
    simpa [g] using
      (Function.directionalDerivativeAt_zero_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hy' : y ∈ dom(g) := by
    simpa [g] using hy
  have hy_bot' : g y ≠ ⊥ := by
    simpa [g] using hy_bot
  simpa [g] using
    (directionalDerivativeAt_le_of_isConvex_of_positivelyHomogeneous_of_zero
      (g := g) hg_convex hg_hom hg_zero hy' hy_bot' z)

end Function

end

/-! ### Remark_5_24_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithTopBot 𝕜}
local notation "fStar" => (f⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.2 identifies the range of `∂f` with the conjugate-side
  subdifferential domain and places that range between `ri(dom f⋆)` and `dom(f⋆)`.
- `core/canonical`: the owner statements are intrinsic on `gph∂`, relation inversion
  `SetRel.inv`, the codomain-explicit conjugate-domain owner `dom∂[E](fStar)`, and the
  primal range owner `cod∂(f)`.
- `bridge/view`: the Euclidean self-dual graph view is downstream; this item keeps the canonical
  dual/primal owner surface.

Domain-style sampling used here:
- `gph∂[Y](·)` and `dom∂[Y](·)` from Definitions 5.24.3/5.24.1;
- relation-owner lemmas `SetRel.inv`, `SetRel.dom_inv`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from Text 26.0.1.

Primitive data vs derived API:
- primitive graph-level bridge input:
  `gph∂[E](fStar) = (gph∂(f)).inv`;
- primitive conjugate-side owner set: `dom∂[E](fStar)`, with codomain parameter explicit because
  it is not recoverable from `fStar`;
- derived source-facing bridge API: codomain/domain transport from `cod∂(f)`
  along graph inversion.

Layer target: `bridge/view`.
-/

/-- Relation-level bridge: if the conjugate-side intrinsic graph is the inverse of the primal
graph, then the canonical range owner `cod∂(f)` equals the conjugate-side domain owner
`dom∂[E](fStar)`. -/
theorem codSubdifferential_eq_domSubdifferential_convexConjugate_of_graph_eq_inv
    (hgraph : gph∂[E](fStar) = (gph∂(f)).inv) :
    cod∂(f) = dom∂[E](fStar) := by
  calc
    cod∂(f) = (gph∂[E](fStar)).dom := by
      simpa [SetRel.dom_inv] using congrArg SetRel.dom hgraph.symm
    _ = dom∂[E](fStar) := rfl

/-- The range of the intrinsic subdifferential graph equals the conjugate-side subdifferential
domain with explicit primal codomain parameter. -/
theorem codSubdifferential_eq_domSubdifferential_convexConjugate
    (hf : IsClosedProperConvex[𝕜] f) :
    cod∂(f) = dom∂[E](fStar) := by
  exact codSubdifferential_eq_domSubdifferential_convexConjugate_of_graph_eq_inv
    (_root_.subdifferentialGraph_convexConjugate_eq_inv hf)

-- Proof sketch: first identify `cod∂(f)` with `dom∂[E](fStar)`.
-- Then transport any already-available conjugate-side domain sandwich
-- `riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ⊆ dom(fStar)` across that equality.
/-- Transport lemma at owner level: a conjugate-side sandwich on `dom∂[E](fStar)` transfers to
the primal range owner `cod∂(f)` once `cod∂(f) = dom∂[E](fStar)` is known. -/
theorem codSubdifferential_between_riDom_and_dom_convexConjugate_of_eq
    (hcod : cod∂(f) = dom∂[E](fStar))
    (hdom_conj : riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ∧ dom∂[E](fStar) ⊆ dom(fStar)) :
    riDom[𝕜](fStar) ⊆ cod∂(f) ∧ cod∂(f) ⊆ dom(fStar) := by
  constructor
  · intro x hx
    exact hcod.symm ▸ hdom_conj.1 hx
  · intro x hx
    exact hdom_conj.2 (by rwa [hcod] at hx)

/-- Remark 5.24.2, intrinsic owner form: if the conjugate-side sandwich is available at codomain
`E`, then the range owner `cod∂(f)` lies between `riDom[𝕜](fStar)` and `dom(fStar)`. -/
theorem codSubdifferential_between_riDom_and_dom_convexConjugate
    (hf : IsClosedProperConvex[𝕜] f)
    (hdom_conj : riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ∧ dom∂[E](fStar) ⊆ dom(fStar)) :
    riDom[𝕜](fStar) ⊆ cod∂(f) ∧ cod∂(f) ⊆ dom(fStar) := by
  exact codSubdifferential_between_riDom_and_dom_convexConjugate_of_eq
    (codSubdifferential_eq_domSubdifferential_convexConjugate hf) hdom_conj

end

/-! ### Theorem_5_24_2 (from Chap05) -/
noncomputable section

namespace Function

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.2 identifies the one-dimensional scalar-line subdifferential
  `∂[𝕜]f(x)` with the interval of scalar slopes lying between the left and right derivatives from
  Theorem 5.24.1.
- `core/canonical`: the relevant owners already exist as `_root_.subdifferentialAt`,
  `Function.leftDerivative`, and `Function.rightDerivative`.
- `bridge/view`: the theorem is the one-dimensional comparison between the Chapter 23
  subdifferential owner and the Chapter 24 one-sided derivative owners, not a new interval-valued
  wrapper.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and
  `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from
  `Items/Chap05/Theorem_23_2.lean`;
- `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point` and
  `Function.directionalDerivativeAt_zero_of_finite_point` from
  `Items/Chap05/Theorem_23_1.lean`;
- `Function.leftDerivative`, `Function.rightDerivative`,
  `Function.rightDerivative_eq_directionalDerivativeAt_one`, and
  `Function.leftDerivative_eq_neg_directionalDerivativeAt_neg_one`,
  `Function.leftDerivative_eq_top_of_not_mem_dom_of_nonempty_inter_Iio`, and
  `Function.rightDerivative_eq_bot_of_not_mem_dom_of_nonempty_inter_Ioi` from
  `Items/Chap05/Theorem_5_24_1.lean`;
- the ambient closed/proper/convex owner `Function.IsClosedProperConvex` from
  `Items/Chap03/Text_12_3_6.lean`, reused through Theorem 5.24.1.

Primitive data vs derived API:
- primitive data: a convex function `f : 𝕜 → WithTopBot 𝕜`, a point `x : 𝕜`, and the finite-point
  guards `x ∈ dom(f)` and `f x ≠ ⊥`;
- primitive owners reused from upstream: `subdifferentialAt`, `leftDerivative`, `rightDerivative`;
- derived API: the interval description of the one-dimensional fiber `∂f(x)`.

Layer target: `bridge/view`.

Scalar-layer note:
- the theorem is one-dimensional but not intrinsically real; it is stated on an ordered scalar
  line `𝕜` and reuses the canonical scalar-line pairing `⟪u, v⟫ₚ = u * v` only as a thin bridge to
  the Chapter 23 subdifferential owner.
- closedness/properness are not part of the primitive bridge data here: they are only needed
  upstream for the global continuity/off-domain consequences in Theorem 5.24.1, while the local
  interval fiber description itself only uses convexity and finiteness at `x`.
-/

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]

/-- The canonical one-dimensional pairing on a scalar line is ordinary multiplication. -/
local instance instHasPairingScalarLine_5242 : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: specialize `mem_subdifferentialAt_iff_le_directionalDerivativeAt` to `E = 𝕜`,
-- `Y = 𝕜` with scalar-line pairing `⟪u, v⟫ₚ = u * v`, where directions `1` and `-1` recover the
-- endpoint slope inequalities.
/-- Theorem 5.24.2, atomic membership form: a scalar slope belongs to the one-dimensional
subdifferential at `x` exactly when it lies between the left and right derivatives at `x`. -/
@[simp] theorem mem_subdifferentialAt_iff_mem_Icc_leftDerivative_rightDerivative
    {f : 𝕜 → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜)
    (x : 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (xStar : 𝕜) :
    xStar ∈ (∂[𝕜]f(x)) ↔
      ((xStar : WithTopBot 𝕜) ∈ Set.Icc (f′- x) (f′+ x)) := by
  sorry

/-- Theorem 5.24.2: for a convex extended-valued function finite at `x`, the one-dimensional
scalar-line subdifferential `∂[𝕜]f(x)` is exactly the set of scalar slopes lying between the left
and right derivatives at `x`. -/
theorem subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative
    {f : 𝕜 → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜)
    (x : 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 |
        (xStar : WithTopBot 𝕜) ∈ Set.Icc (f′- x) (f′+ x)} := by
  ext xStar
  exact
    (mem_subdifferentialAt_iff_mem_Icc_leftDerivative_rightDerivative
      hf_convex x hx hx_bot xStar)

end

end Function

/-! ### Definition_5_24_3 (from Chap05) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.3 introduces the graph of the subdifferential multifunction,
  i.e. the set of pairs `(x, x⋆)` with `x⋆ ∈ ∂f(x)`.
- `core/canonical`: the chapter owner for the subdifferential itself is `_root_.subdifferentialAt`,
  while graph-shaped multivalued objects in the project are organized as relations `SetRel`.
- `bridge/view`: the source graph of `∂f` is therefore the canonical relation view
  `subdifferentialGraph f Y : SetRel E Y` (defaulting to `Y = StrongDual 𝕜 E`), not a second
  packaged owner beside `_root_.subdifferentialAt`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean),
  the Chapter 23 owner for the subdifferential itself;
- `SetRel`, `SetRel.dom`, and `SetRel.cod` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean),
  the canonical owner layer for graphs/domains/ranges of multivalued mappings;
- `Function.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean),
  the Fréchet-Riesz vector-valued bridge reused in the inner-product-space specialization below.

Primitive data vs derived API:
- primitive owner input: the subdifferential owner `_root_.subdifferentialAt f x`;
- derived bridge API: the relation `subdifferentialGraph f`, the source-set image owner
  `subdifferentialImage f S`, and their pointwise membership theorems.

Layer target: `bridge/view`. Definition 5.24.3 does not introduce a second owner beside
`subdifferentialAt`; it places the existing owner in the chapter's canonical `SetRel` graph/image
language.
-/

/-- Definition 5.24.3: the graph of the subdifferential multifunction is the relation whose pairs
are exactly `(x, x⋆)` with `x⋆ ∈ ∂f(x)`. The codomain owner is pairing-parametric and defaults to
`StrongDual 𝕜 E`. -/
abbrev subdifferentialGraph (f : E → WithTopBot 𝕜)
    (Y : Type (max u v) := StrongDual 𝕜 E)
    [HasPairing E Y 𝕜] : SetRel E Y :=
  {p | p.2 ∈ ∂[Y]f(p.1)}

scoped[Rockafellar] notation "gph∂[" Y_ "](" f ")" =>
  _root_.subdifferentialGraph (f := f) (Y := Y_)
scoped[Rockafellar] notation "gph∂(" f ")" =>
  _root_.subdifferentialGraph (f := f)

/-- A pair belongs to the canonical graph relation of the subdifferential exactly when its second
coordinate is a subgradient at its first coordinate. -/
@[simp] theorem mem_subdifferentialGraph {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} {xStar : Y} :
    x ~[gph∂[Y](f)] xStar ↔ xStar ∈ ∂[Y]f(x) :=
  by rfl

/-- Pairing transport API for `subdifferentialGraph`: if two pairings on `(E, Y, 𝕜)` are
pointwise equal, they induce the same graph relation. -/
theorem subdifferentialGraph_eq_of_pairing_eq
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    {pairing₁ pairing₂ : HasPairing E Y 𝕜}
    (hpair : ∀ x : E, ∀ y : Y,
      @HasPairing.pairing E Y 𝕜 pairing₁ x y =
        @HasPairing.pairing E Y 𝕜 pairing₂ x y) :
    @_root_.subdifferentialGraph 𝕜 _ _ _ E _ _ _ f Y pairing₁ =
      @_root_.subdifferentialGraph 𝕜 _ _ _ E _ _ _ f Y pairing₂ := by
  ext p
  rcases p with ⟨x, xStar⟩
  change
      xStar ∈ @_root_.subdifferentialAt 𝕜 _ _ E _ f x Y pairing₁ ↔
      xStar ∈ @_root_.subdifferentialAt 𝕜 _ _ E _ f x Y pairing₂
  rw [subdifferentialAt_eq_of_pairing_eq (f := f) (x := x) (Y := Y) hpair]

/-- The source set `∂f(S)` of all subgradients taken at base points in `S`, defined intrinsically
as the relation image of `S` under the canonical graph owner `subdifferentialGraph`. The codomain
owner is pairing-parametric and defaults to `StrongDual 𝕜 E`. -/
abbrev subdifferentialImage (f : E → WithTopBot 𝕜) (S : Set E)
    (Y : Type (max u v) := StrongDual 𝕜 E) [HasPairing E Y 𝕜] : Set Y :=
  SetRel.image (subdifferentialGraph (Y := Y) f) S

scoped[Rockafellar] notation "∂[" Y_ "]" f "(" S ")" =>
  _root_.subdifferentialImage (f := f) (S := S) (Y := Y_)
scoped[Rockafellar] notation "∂" f "(" S ")" =>
  _root_.subdifferentialImage (f := f) (S := S)

/-- Pairing-level membership form of `subdifferentialImage`. -/
@[simp] theorem mem_subdifferentialImage_pairing {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {S : Set E} {xStar : Y} :
    xStar ∈ (∂[Y]f(S)) ↔ ∃ x ∈ S, xStar ∈ ∂[Y]f(x) := by
  constructor
  · intro hxStar
    rcases (SetRel.mem_image.mp hxStar) with ⟨x, hxS, hxGraph⟩
    exact ⟨x, hxS, (mem_subdifferentialGraph.mp hxGraph)⟩
  · rintro ⟨x, hxS, hxSubgrad⟩
    exact SetRel.mem_image.mpr ⟨x, hxS, (mem_subdifferentialGraph.mpr hxSubgrad)⟩

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

/-- Membership in `∂f(S)` means exactly that the candidate dual vector belongs to
`subdifferentialAt f x` at some base point `x ∈ S`. -/
@[simp] theorem mem_subdifferentialImage
    {f : E → WithTopBot 𝕜} {S : Set E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f(S)) ↔ ∃ x ∈ S, xStar ∈ ∂ f at x := by
  exact
    mem_subdifferentialImage_pairing
      (f := f) (Y := StrongDual 𝕜 E) (S := S) (xStar := xStar)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for the inner-product-space graph bridge.

- `source-facing`: later Section 24 items in textbook coordinate models speak about vector
  subgradients `x⋆ ∈ ∂f(x)`.
- `core/canonical`: the owner graph remains `_root_.subdifferentialGraph f`, here specialized to
  the continuous-dual codomain.
- `bridge/view`: `Function.subdifferentialGraph f` transports that owner along the canonical
  inner-product-to-dual map, so it is only the vector-valued graph view of the same object.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from this file;
- `Function.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean);
- mathlib's canonical embedding owner `InnerProductSpace.toDualMap`, and its complete-space
  specialization equivalence `InnerProductSpace.toDual`.

Primitive data vs derived API:
- primitive owner: `_root_.subdifferentialGraph f`, the canonical dual-valued graph relation;
- derived bridge API: the relation `Function.subdifferentialGraph f`, obtained by pulling that
  owner back along `Prod.map id (InnerProductSpace.toDualMap 𝕜 E)`, and its pointwise membership
  simplification in vector form.

Layer target: `bridge/view`.
-/

namespace Function

/-- On an ordered inner-product space, the vector-valued subdifferential graph is the canonical
pullback of the intrinsic dual-valued graph `_root_.subdifferentialGraph` along
`InnerProductSpace.toDualMap` on the second coordinate. -/
abbrev subdifferentialGraph (f : E → WithTopBot 𝕜) : SetRel E E :=
  (Prod.map id (InnerProductSpace.toDualMap 𝕜 E)) ⁻¹' (_root_.subdifferentialGraph f)

@[simp] theorem mem_subdifferentialGraph {f : E → WithTopBot 𝕜} {x xStar : E} :
    x ~[subdifferentialGraph f] xStar ↔ xStar ∈ subdifferentialAt f x :=
  by rfl

/-- The domain of the vector-valued subdifferential graph agrees with the domain of the
intrinsic dual-valued graph on complete spaces. This is the owner-level Fréchet-Riesz bridge for
graph-domain
statements. -/
theorem subdifferentialGraph_dom_eq_intrinsic (f : E → WithTopBot 𝕜) [CompleteSpace E] :
    (subdifferentialGraph f).dom = (_root_.subdifferentialGraph f).dom := by
  ext x
  rw [SetRel.mem_dom, SetRel.mem_dom]
  constructor
  · rintro ⟨xStar, hxStar⟩
    refine ⟨InnerProductSpace.toDualMap 𝕜 E xStar, ?_⟩
    have hxMem : xStar ∈ subdifferentialAt f x :=
      Function.mem_subdifferentialGraph.mp hxStar
    have hxDual : InnerProductSpace.toDualMap 𝕜 E xStar ∈ ∂ f at x := by
      change InnerProductSpace.toDualMap 𝕜 E xStar ∈
          _root_.subdifferentialAt (Y := StrongDual 𝕜 E) f x
      exact hxMem
    exact _root_.mem_subdifferentialGraph.mpr hxDual
  · rintro ⟨xDual, hxDual⟩
    refine ⟨(InnerProductSpace.toDual 𝕜 E).symm xDual, ?_⟩
    have hrepr :
        InnerProductSpace.toDualMap 𝕜 E ((InnerProductSpace.toDual 𝕜 E).symm xDual) = xDual := by
      ext z
      change inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm xDual) z = xDual z
      exact InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (E := E) (x := z) (y := xDual)
    have hxDualMem : xDual ∈ ∂ f at x :=
      _root_.mem_subdifferentialGraph.mp hxDual
    have hxMem : (InnerProductSpace.toDual 𝕜 E).symm xDual ∈ subdifferentialAt f x := by
      change InnerProductSpace.toDualMap 𝕜 E ((InnerProductSpace.toDual 𝕜 E).symm xDual) ∈
          _root_.subdifferentialAt (Y := StrongDual 𝕜 E) f x
      rw [hrepr]
      exact hxDualMem
    exact Function.mem_subdifferentialGraph.mpr hxMem

end Function

end

/-! ### Proposition_5_24_3 (from Chap05) -/
noncomputable section

open scoped BigOperators Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [AddCommMonoid 𝕜] [Preorder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [AddRightReflectLE 𝕜]
variable {E : Type u} [Sub E]

/-- Primitive cyclic inequality for subgradient cycles: if each `xStar i` is a subgradient of `f`
at `x i`, then the cyclic pairing sum is nonpositive. This is the owner-level inequality behind
cyclic monotonicity of the subdifferential graph. -/
theorem sum_nonpos_of_subgradient_cycle
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)} [HasPairing E Y 𝕜]
    {m : ℕ} {x : Fin (m + 1) → E} {xStar : Fin (m + 1) → Y}
    (hf : f.IsProper) (hx : ∀ i, xStar i ∈ ∂[Y]f(x i)) :
    ∑ i : Fin (m + 1), ⟪x (i + 1) - x i, xStar i⟫ₚ ≤ (0 : 𝕜) := by
  rcases hf.nonempty_dom with ⟨y, hy⟩
  have hsub :
      ∀ i z, f z ≥ f (x i) + (((⟪z - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) := by
    intro i z
    exact (mem_subdifferentialAt_pairing.mp (hx i)) z
  have hx_top : ∀ i, f (x i) ≠ ⊤ := by
    intro i htop
    have hsub_y :
        f y ≥ f (x i) + (((⟪y - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) := by
      simpa using hsub i y
    have htop_le_aux :
        (⊤ : WithTopBot 𝕜) + (((⟪y - x i, xStar i⟫ₚ : 𝕜)) : WithTopBot 𝕜) ≤ f y := by
      simpa [htop] using hsub_y
    have htop_le : (⊤ : WithTopBot 𝕜) ≤ f y := by
      calc
        (⊤ : WithTopBot 𝕜) =
            (⊤ : WithTopBot 𝕜) + (((⟪y - x i, xStar i⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by
              simp
        _ ≤ f y := htop_le_aux
    exact (not_le_of_gt hy) htop_le
  have hx_bot : ∀ i, f (x i) ≠ ⊥ := fun i ↦ hf.ne_bot (x i)
  have hx_finite : ∀ i, ∃ v : 𝕜, ((v : 𝕜) : WithTopBot 𝕜) = f (x i) := by
    intro i
    rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨hx_top i, hx_bot i⟩ with ⟨v, hv⟩
    exact ⟨v, hv⟩
  choose v hv using hx_finite
  let Δ : Fin (m + 1) → 𝕜 := fun i ↦ ⟪x (i + 1) - x i, xStar i⟫ₚ
  have hstep : ∀ i, v i + Δ i ≤ v (i + 1) := by
    intro i
    have hsub_step :
        f (x (i + 1)) ≥
          f (x i) + (((Δ i : 𝕜)) : WithTopBot 𝕜) := by
      simpa [Δ] using hsub i (x (i + 1))
    have hsub' :
        ((v i : 𝕜) : WithTopBot 𝕜) + (((Δ i : 𝕜)) : WithTopBot 𝕜) ≤
          ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by
      calc
        ((v i : 𝕜) : WithTopBot 𝕜) +
              (((Δ i : 𝕜)) : WithTopBot 𝕜)
            = f (x i) + (((Δ i : 𝕜)) : WithTopBot 𝕜) := by rw [hv i]
        _ ≤ f (x (i + 1)) := hsub_step
        _ = ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by rw [hv (i + 1)]
    have hsub'' :
        ((v i + Δ i : 𝕜) : WithTopBot 𝕜) ≤
          ((v (i + 1) : 𝕜) : WithTopBot 𝕜) := by
      simpa [WithBotTop.coe_add] using hsub'
    exact (WithBotTop.coe_le_coe).1 hsub''
  have hshift :
      ∑ i : Fin (m + 1), v (i + 1) = ∑ i : Fin (m + 1), v i := by
    simpa using
      (Fintype.sum_equiv (Equiv.addRight (1 : Fin (m + 1)))
        (fun i ↦ v (i + 1)) (fun i ↦ v i) fun i ↦ rfl)
  have hsum_nonpos :
      ∑ i : Fin (m + 1), Δ i + ∑ i : Fin (m + 1), v i ≤
        ∑ i : Fin (m + 1), v i := by
    calc
      ∑ i : Fin (m + 1), Δ i + ∑ i : Fin (m + 1), v i
          = ∑ i : Fin (m + 1), (v i + Δ i) := by
            rw [add_comm]
            symm
            rw [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin (m + 1), v (i + 1) := by
            exact Finset.sum_le_sum (fun i _ ↦ hstep i)
      _ = ∑ i : Fin (m + 1), v i := hshift
  exact (add_le_iff_nonpos_left).1 hsum_nonpos

/-- Proposition 5.24.3: the subdifferential graph relation is cyclically monotone. The theorem is
stated on the intrinsic pairing-defined graph relation
`{p : E × Y | p.2 ∈ ∂[Y]f(p.1)}`, which is definitionally the same relation as `gph∂[Y](f)` when
the Chapter 5 graph owner is available. -/
theorem subdifferentialGraph_cyclicallyMonotone
    {f : E → WithTopBot 𝕜} {Y : Type (max u v)} [HasPairing E Y 𝕜]
    (hf : f.IsProper) :
    CMon[𝕜](({p : E × Y | p.2 ∈ ∂[Y]f(p.1)} : SetRel E Y)) := by
  refine ⟨fun m x xStar hx ↦ ?_⟩
  exact sum_nonpos_of_subgradient_cycle (hf := hf)
    (x := x) (xStar := xStar)
    (fun i ↦ by simpa using hx i)

end

/-! ### Remark_5_24_3 (from Chap05) -/
namespace SetRel

section

variable {ι : Type*} [LE ι]
variable {α : Type*} [LE α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.3 characterizes the Chapter 5 owner
  `SetRel.IsCompleteNondecreasingCurve` on relations `Γ : SetRel ι α`.
- `core/canonical`: mathlib's order-theoretic owner for a maximal chain is
  `IsMaxChain`, and on `ι × α` the ambient relation `(· ≤ ·)` is the coordinatewise order relation.
- `bridge/view`: this standalone item file reuses the canonical bridge theorem from
  `Definition_5_24_4` directly and only provides directional projection lemmas for source-style
  forward/backward use.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` and `Function.completeNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`, the project owners for
  the source notion and its witness-side graph realization;
- `Function.leftLim` and `Function.rightLim` from
  `.lake/packages/mathlib/Mathlib/Topology/Order/LeftRightLim.lean`, the canonical owners for the
  one-sided limits used in that witness-side realization;
- `IsChain` and `IsMaxChain` from mathlib's
  `.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean`, the canonical owners for chain and
  maximal-chain structure;
- the product order relation on `ι × α`, whose `≤` is exactly the coordinatewise ordering
  appearing in the source.

Primitive data vs derived API:
- primitive source-facing owner: `SetRel.IsCompleteNondecreasingCurve Γ`;
- primitive canonical comparison owner: `IsMaxChain (· ≤ ·) Γ`;
- derived API kept here: only directional projection lemmas from the upstream equivalence, with no
  local duplicate `↔` theorem and no extra chain wrapper or maximal-curve package.

Layer target: `bridge/view`.

Semantic-fidelity audit:
- the source-facing owner `SetRel.IsCompleteNondecreasingCurve` from Definition 5.24.4 remains the
  main mathematical notion on the left side;
- the right side reuses the exact mathlib order-theoretic owner `IsMaxChain` for the coordinatewise
  order on `ι × α`, with no new wrapper around chains or maximality;
- this file therefore operates purely at the `bridge/view` layer, does not introduce any second
  owner for complete non-decreasing curves, and does not duplicate the upstream bridge theorem name.
-/

/-- A complete non-decreasing curve in `ι × α` is a maximal chain for the coordinatewise order. -/
@[simp] theorem IsCompleteNondecreasingCurve.isMaxChain {Γ : SetRel ι α}
    (hΓ : Γ.IsCompleteNondecreasingCurve) :
    IsMaxChain (· ≤ ·) Γ :=
  (isCompleteNondecreasingCurve_iff_isMaxChain Γ).1 hΓ

/-- A maximal chain in `ι × α` for the coordinatewise order is a complete non-decreasing curve. -/
@[simp] theorem IsMaxChain.isCompleteNondecreasingCurve {Γ : SetRel ι α}
    (hΓ : IsMaxChain (· ≤ ·) Γ) :
    Γ.IsCompleteNondecreasingCurve :=
  (isCompleteNondecreasingCurve_iff_isMaxChain Γ).2 hΓ

end

end SetRel

/-! ### Theorem_5_24_3 (from Chap05) -/
noncomputable section

open scoped Topology Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.3 studies an extended-valued function `φ` on an ordered scalar
  line, squeezed pointwise between the source one-sided derivatives `f′-` and `f′+` of a proper
  convex function `f`, then identifies the source one-sided limit functions `φ_-` and `φ_+`,
  including the scalar-line subdifferential interval corollary.
- `core/canonical`: the relevant owner declarations already exist as the one-sided limit owners
  `Function.leftLim`, `Function.rightLim` and the Chapter 24 one-sided derivative owners
  `Function.leftDerivative`, `Function.rightDerivative`; the subgradient consequence is routed
  through the canonical interval theorem
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative`, not
  through a new
  selector package.
- `bridge/view`: this item is a theorem-level bridge from the order bounds
  `f′- x ≤ φ x ≤ f′+ x` to monotonicity and one-sided-limit identification.

Domain-style sampling used here:
- `Function.leftLim` and `Function.rightLim` from mathlib's canonical one-sided-limit API in
  `Topology/Order/LeftRightLim`;
- `Monotone.tendsto_leftLim` and `Monotone.tendsto_rightLim` from the same file, which are the
  canonical generic one-sided-limit theorems for a monotone profile;
- `Function.leftDerivative` and `Function.rightDerivative` from
  `Items/Chap05/Theorem_5_24_1.lean`;
- `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` from
  `Items/Chap05/Theorem_5_24_2.lean`.

Primitive data vs derived API:
- primitive theorem inputs: `f`, `φ`, the pointwise sandwich assumption
  `f′- x ≤ φ x ≤ f′+ x`, and the minimal convexity data needed by each
  clause (`f.IsConvex 𝕜` for monotonicity, and `f.IsConvex 𝕜` + `f.IsProper` for one-sided-limit
  identification on `interior (dom(f))`; the subdifferential interval clause uses the scalar-line
  pairing owner `∂[𝕜]f(x)` with `⟪u, v⟫ₚ = u * v`);
- derived conclusions: monotonicity of `φ`, identification of its one-sided limits, and the
  resulting interval description of the one-dimensional subdifferential.

Layer target: `bridge/view`.

Scalar/ambient minimization note:
- clauses (1)–(3) use the ordered scalar-line layer already exposed by the upstream one-sided
  derivative owners `leftDerivative` and `rightDerivative`;
- clause (4) now uses the same scalar-line abstraction layer as clauses (1)–(3), via the upstream
  interval-fiber theorem
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` and the scalar-line
  subdifferential owner `∂[𝕜]f(x)`;
- clauses (2)–(4) do not use the stronger bundled owner `IsClosedProperConvex`; they expose only
  the upstream primitive assumptions actually used (`IsConvex _`, `IsProper`, and local point
  data).
-/

namespace Function

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

variable {f : 𝕜 → WithBotTop 𝕜}
variable {φ : 𝕜 → WithBotTop 𝕜}

-- Proof sketch: for `x < y`, use the one-dimensional convex secant-slope order
-- `f′+ x ≤ f′- y`. Insert the bounds `φ x ≤ f′+ x` and `f′- y ≤ φ y` to obtain `φ x ≤ φ y`.
/-- Theorem 5.24.3 (1): any extended-valued function on an ordered scalar line lying pointwise
between the left and right derivatives of a convex function is nondecreasing. -/
theorem monotone_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    : Monotone φ := by
  sorry

section Topological

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

-- Proof sketch: clause (1) gives monotonicity of `φ`, so the canonical one-sided-limit owner
-- theorem `Monotone.tendsto_rightLim` identifies the right-hand asymptotic profile of `φ`.
-- Squeezing `φ z` between `f′- z` and `f′+ z` for `z > x`, and then
-- using the right-hand one-sided continuity of the derivative bounds, forces that limit to be
-- `f′+ x`.
/-- Theorem 5.24.3 (2), pointwise interior-domain form: the right one-sided limit of `φ` agrees with
the source right derivative. -/
theorem rightLim_eq_rightDerivative_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx : x ∈ interior (dom(f)))
    : φ.rightLim x = f′+ x := by
  sorry

-- Proof sketch: clause (1) gives monotonicity of `φ`, so `Monotone.tendsto_leftLim` supplies the
-- canonical left-hand limit of `φ`. Squeezing `φ z` between `f′- z` and `f′+ z` for `z < x`, and
-- using the left-hand one-sided continuity of the derivative bounds, identifies that limit with
-- `f′- x`.
/-- Theorem 5.24.3 (3), pointwise interior-domain form: the left one-sided limit of `φ` agrees with
the source left derivative. -/
theorem leftLim_eq_leftDerivative_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx : x ∈ interior (dom(f)))
    : φ.leftLim x = f′- x := by
  sorry

end Topological

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]

variable {f : 𝕜 → WithBotTop 𝕜}
variable {φ : 𝕜 → WithBotTop 𝕜}

/-- The canonical one-dimensional pairing on a scalar line is ordinary multiplication. -/
local instance instHasPairingScalarLine_5243 : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: start from the one-dimensional interval description by left/right derivatives
-- (Theorem 5.24.2), then rewrite both interval endpoints by identified one-sided limits.
/-- Primitive clause-(4) bridge: if the one-sided limits of `φ` are already identified with the
source one-sided derivatives at `x`, then the subdifferential is the interval between those limits.
-/
theorem subdifferentialAt_eq_setOf_mem_Icc_of_leftLim_eq_and_rightLim_eq
    (hf_convex : f.IsConvex 𝕜)
    {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hleft : φ.leftLim x = f′- x)
    (hright : φ.rightLim x = f′+ x) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 | (xStar : WithBotTop 𝕜) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x)} := by
  simpa [hleft, hright] using
    (subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative hf_convex x hx hx_bot)

variable [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)]

/-- Theorem 5.24.3 (4), source-facing corollary: on `interior (dom(f))`, the subdifferential is
the interval of scalar slopes between the one-sided limits `φ_-` and `φ_+`. -/
theorem subdifferentialAt_eq_setOf_mem_Icc_leftLim_rightLim
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx_int : x ∈ interior (dom(f))) (hx_bot : f x ≠ ⊥) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 | (xStar : WithBotTop 𝕜) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x)} := by
  have hx : x ∈ dom(f) := interior_subset hx_int
  have hright :
      φ.rightLim x = f′+ x :=
    rightLim_eq_rightDerivative_of_leftDerivative_le_rightDerivative hf_convex hf_proper hφ hx_int
  have hleft :
      φ.leftLim x = f′- x :=
    leftLim_eq_leftDerivative_of_leftDerivative_le_rightDerivative hf_convex hf_proper hφ hx_int
  exact subdifferentialAt_eq_setOf_mem_Icc_of_leftLim_eq_and_rightLim_eq
    hf_convex hx hx_bot hleft hright

end

end Function
