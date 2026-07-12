import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_5
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped BigOperators RealInnerProductSpace Rockafellar

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 23.0.7 records explicit subdifferentials for four standard convex
  examples: the Euclidean norm, the coordinate `ℓ∞` norm, the closed-unit-ball square-root
  barrier, and the indicator of a convex set.
- `core/canonical`: the owner abstractions already present in the project are
  `_root_.subdifferentialAt` (dual-valued) and `Function.subdifferentialAt` (Euclidean bridge)
  from `Chap05.Definition_23_0_6`,
  `normalCone` from `Chap01.Definition_2_7_10`, and the coordinate owners
  `linftyNorm` and `coordinateL1Ball` from `Chap01.Text_5_5_0_5`.
- `bridge/view`: for indicator functions, this file states the canonical dual-owner formulas first
  and then keeps the Euclidean vector-valued formulas as Fréchet-Riesz transport bridges, instead
  of introducing any parallel local “subgradient vector” owner.

Domain-style sampling used here:
- `Function.subdifferentialAt` and `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `normalCone` and `mem_normalCone_iff_sub_nonpos` from `Chap01.Definition_2_7_10`;
- `linftyNorm` and `coordinateL1Ball` from `Chap01.Text_5_5_0_5`;
- `Metric.closedBall` as the canonical owner for the Euclidean unit ball.

Primitive data vs derived API:
- primitive concrete data introduced here: the square-root barrier on the closed unit ball;
- derived API: the explicit subdifferential formulas for the norm, coordinate `ℓ∞` norm, and
  indicator examples, with the active-coordinate presentation of the `ℓ∞` case kept inline rather
  than packaged as a second public owner.

Layer target: `source-facing`, stated on the existing canonical owners.
-/

section Norm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

local notation "normGauge" => Function.toWithTopBot (fun x : E ↦ ‖x‖)

-- Proof sketch: combine the Chapter 23 supporting-hyperplane characterization with the sharp
-- Cauchy--Schwarz bound `⟪g, z⟫ ≤ ‖g‖ * ‖z‖`; at the origin this shows that the supporting
-- inequality is equivalent to `‖g‖ ≤ 1`, i.e. membership in the closed unit ball.
/-- Example 23.0.7 (1): in a real inner-product space, the subdifferential of the norm at
the origin is the closed unit ball. -/
theorem subdifferentialAt_norm_zero :
    ∂ᵥnormGauge((0 : E)) =
      Metric.closedBall (0 : E) 1 := sorry

-- Proof sketch: at `x ≠ 0`, differentiability of the norm identifies the unique supporting
-- functional with the Fréchet-Riesz vector `‖x‖⁻¹ • x`, and strict convexity of the Euclidean norm
-- forces the subdifferential to be a singleton.
/-- Example 23.0.7 (2): away from the origin, the subdifferential of the norm is the singleton
containing the normalized base point. -/
theorem subdifferentialAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    ∂ᵥnormGauge(x) = ({‖x‖⁻¹ • x} : Set E) := sorry

end Function

end Norm

section Linfty

variable {ι : Type*} [Fintype ι]

section Generic

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜]
local notation "X" => ι → 𝕜
local notation "linftyGauge" => Function.toWithTopBot (fun x : X ↦ linftyNorm x)
local instance instHasPairingLinfty : HasPairing X X 𝕜 where
  pairing x y := ∑ i, x i * y i

namespace Function

-- Proof sketch: at the origin, the Chapter 23 support inequality for `linftyGauge` is equivalent
-- to the coordinate estimate `∑ j |g j| ≤ 1`, i.e. membership in the canonical coordinate owner
-- `coordinateL1Ball` on the function-space model.
/-- Example 23.0.7 (3): at the origin, the pairing-owner subdifferential of the coordinate `ℓ∞`
norm on `ι → 𝕜` is the coordinate `ℓ¹` unit ball. -/
theorem subdifferentialAt_linftyNorm_zero :
    ∂[X]linftyGauge((0 : X)) = (coordinateL1Ball : Set X) := sorry

end Function

end Generic

section Real

local notation "X" => ι → ℝ
local notation "linftyGauge" => Function.toWithTopBot (fun x : X ↦ linftyNorm x)

namespace Function

-- Proof sketch: for `x ≠ 0`, use the Chapter 23 support characterization together with the
-- coordinate support-function computation for the `ℓ¹` ball. The active supporting points are the
-- signed basis vectors indexed by the coordinates where `|x j| = linftyNorm x`, and the
-- subdifferential is their convex hull.
/-- Example 23.0.7 (4): away from the origin, for real coordinates the pairing-owner
subdifferential of `linftyNorm` is the convex hull of the signed coordinate basis vectors indexed
by the active coordinates. -/
theorem subdifferentialAt_linftyNorm_of_ne_zero [DecidableEq ι] {x : ι → ℝ} (hx : x ≠ 0) :
    ∂[X]linftyGauge(x) =
      convexHull ℝ
        ((fun j : ι ↦ Pi.single j (Real.sign (x j))) ''
          {j : ι | |x j| = linftyNorm x}) := sorry

end Function

end Real

end Linfty

section Barrier

variable {E : Type u} [SeminormedAddCommGroup E]

/-- The closed-unit-ball barrier example `x ↦ -sqrt(1 - ‖x‖^2)` on `‖x‖ ≤ 1`, with value `+∞`
outside the closed unit ball. -/
def unitBallSqrtBarrier : E → WithTopBot ℝ :=
  Function.toWithTopBotOn (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ 2))
    (Metric.closedBall (0 : E) 1)

-- Proof sketch: unfold `unitBallSqrtBarrier` and simplify the `if` branch using `hx`.
/-- On the closed unit ball, `unitBallSqrtBarrier` is given by the negative square-root branch. -/
theorem unitBallSqrtBarrier_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    unitBallSqrtBarrier x = ((-Real.sqrt (1 - ‖x‖ ^ 2) : ℝ) : WithTopBot ℝ) := by
  have hmem : x ∈ Metric.closedBall (0 : E) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  simpa [unitBallSqrtBarrier] using
    Function.toWithTopBotOn_of_mem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      (Metric.closedBall (0 : E) 1)
      hmem

-- Proof sketch: unfold `unitBallSqrtBarrier`; the hypothesis `1 < ‖x‖` forces the outside branch.
/-- Outside the closed unit ball, `unitBallSqrtBarrier` takes the value `+∞`. -/
theorem unitBallSqrtBarrier_of_one_lt_norm {x : E} (hx : 1 < ‖x‖) :
    unitBallSqrtBarrier x = (⊤ : WithTopBot ℝ) := by
  have hnotmem : x ∉ Metric.closedBall (0 : E) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  simpa [unitBallSqrtBarrier] using
    Function.toWithTopBotOn_of_notMem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      (Metric.closedBall (0 : E) 1)
      hnotmem

end Barrier

section BarrierSubdifferential

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

-- Proof sketch: on `‖x‖ < 1`, the barrier example is finite and differentiable, so its
-- subdifferential is nonempty by the Chapter 23 bridge from differentiability to singleton
-- subdifferentials.
/-- Example 23.0.7 (5): inside the open unit ball, the square-root barrier example is
subdifferentiable. -/
theorem subdifferentialAt_unitBallSqrtBarrier_nonempty_of_norm_lt_one {x : E} (hx : ‖x‖ < 1) :
    (∂ᵥunitBallSqrtBarrier(x)).Nonempty := sorry

-- Proof sketch: when `‖x‖ ≥ 1`, either the function is already `+∞` off the closed ball or the
-- boundary supporting inequality has no continuous supporting vector, so the Chapter 23 owner set
-- is empty.
/-- Example 23.0.7 (6): on and outside the unit sphere, the square-root barrier example has empty
subdifferential. -/
theorem subdifferentialAt_unitBallSqrtBarrier_eq_empty_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    ∂ᵥunitBallSqrtBarrier(x) = (∅ : Set E) := sorry

end Function

end BarrierSubdifferential

section IndicatorDual

variable {𝕜 : Type v} [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E]
variable {N : Type (max u v)}

-- Proof sketch: unfold the indicator branches in the dual-valued Chapter 23 owner
-- `∂[N](·)(·)`; on `z ∈ C` the value is `0` and off `C` it is `+∞`, so the support
-- inequality is equivalent to the feasibility condition and nonpositivity on displacements.
/-- Example 23.0.7 (7), canonical dual-owner form: membership in the subdifferential of the
indicator function is exactly the normal-inequality condition on the underlying set. -/
theorem mem_subdifferentialAt_indicatorFunction_iff {C : Set E} {x : E}
    {xStar : N} [AddMonoid 𝕜] [HasPairing E N 𝕜] :
    xStar ∈ (∂[N] (δ[𝕜](· | C))(x)) ↔
      x ∈ C ∧ ∀ z ∈ C, (⟪z - x, xStar⟫ₚ : 𝕜) ≤ 0 := sorry

section NormalCone

variable [CommRing 𝕜] [Module 𝕜 E]
variable [AddLeftMono 𝕜]
variable [AddCommMonoid N] [Module 𝕜 N] [HasLinearPairing E N 𝕜]

-- Proof sketch: extensionality on membership, then combine the previous canonical indicator
-- criterion with `mem_normalCone_iff_sub_nonpos` specialized to the canonical pairing with
-- the chosen dual-side linear pairing codomain `N`.
/-- Example 23.0.7 (8), canonical dual-owner form: the subdifferential of the indicator function
of a set is the normal cone at the base point. -/
theorem subdifferentialAt_indicatorFunction_eq_normalCone (C : Set E) (x : E) :
    ∂[N] (δ[𝕜](· | C))(x) = N[𝕜, N](x | C) := sorry

end NormalCone

end IndicatorDual

section Indicator

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

-- Proof sketch: this is the Euclidean bridge of the canonical dual-owner theorem above along
-- `InnerProductSpace.toDualMap`; it rewrites the dual inequality as an inner-product inequality.
/-- Example 23.0.7 (7), Euclidean bridge form: membership in the subdifferential of the indicator
function is the normal-inequality condition written with inner products. -/
theorem mem_subdifferentialAt_indicatorFunction_iff {C : Set E} {x xStar : E} :
    xStar ∈ ∂ᵥ(δ[ℝ](· | C))(x) ↔
      x ∈ C ∧ ∀ z ∈ C, ⟪xStar, z - x⟫ ≤ 0 := sorry

-- Proof sketch: transport the canonical dual-owner normal-cone identity above through the
-- Fréchet-Riesz bridge to get the vector-valued Euclidean statement.
/-- Example 23.0.7 (8), Euclidean bridge form: the subdifferential of the indicator function of a
set is the normal cone at the base point. -/
theorem subdifferentialAt_indicatorFunction_eq_normalCone (C : Set E) (x : E) :
    ∂ᵥ(δ[ℝ](· | C))(x) = N[ℝ](x | C) := sorry

end Function

end Indicator
