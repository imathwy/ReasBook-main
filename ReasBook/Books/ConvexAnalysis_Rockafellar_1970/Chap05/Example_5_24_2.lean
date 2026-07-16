import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_1

-- Declarations for this item will be appended below by the statement pipeline.

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
