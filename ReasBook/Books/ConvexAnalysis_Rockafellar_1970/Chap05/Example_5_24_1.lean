import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_2

noncomputable section

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 5.24.1 gives one explicit extended-real-valued convex function on `ℝ`
  and records its one-sided derivative and subdifferential profiles pointwise.
- `core/canonical`: the chapter owner abstractions are already
  `Function.toWithBotTopOn`, `Function.IsClosedProperConvex`, `Function.rightDerivative`,
  `Function.leftDerivative`, and `Function.subdifferentialAt`.
- `bridge/view`: the finite branch on `[-3, 1]` is canonically extended by `+∞` through
  `Function.toWithBotTopOn`, and Theorem 5.24.2 is the nearby bridge identifying one-dimensional
  subdifferentials with the interval between the left and right derivatives. So this example should
  stay on those owners instead of introducing a bespoke two-branch extension or a separate wrapper
  for slope intervals.

Domain-style sampling used here:
- `Function.toWithBotTopOn`, `Function.toWithBotTopOn_of_mem`, and
  `Function.toWithBotTopOn_of_notMem` from `Chap01.Remark_4_4_5`;
- `Function.IsClosedProperConvex` from
  `ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6`;
- `Function.rightDerivative` and `Function.leftDerivative` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_1`;
- `Function.subdifferentialAt` and
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_2`.

Primitive data vs derived API:
- primitive concrete data introduced here: the explicit real branch
  `x ↦ |x| - 2 * sqrt (1 - x)` together with its support interval `[-3, 1]`;
- derived owner-level object: the extended-real example function obtained from those primitive data
  by the canonical owner `Function.toWithBotTopOn`;
- derived API: the theorem that the example is closed proper convex and the three explicit
  profile identifications with the Chapter 24 owners.

Layer target: `source-facing`.

The final textbook sentence about the graph of `∂f` looking like a "continuous infinite curve" is
geometric prose rather than a precise new theorem, so this statement file records the explicit
owner-level formulas instead.
-/

/-- The Chapter 24 example function
`x ↦ |x| - 2 * sqrt (1 - x)` on `[-3, 1]`, extended by `+∞` outside that interval. -/
def absMinusTwoSqrtOneSubExtension : ℝ → WithBotTop ℝ :=
  Function.toWithBotTopOn
    (fun x : ℝ ↦ |x| - 2 * Real.sqrt (1 - x))
    (Set.Icc (-3 : ℝ) 1)

-- Proof sketch: this is the canonical pointwise evaluation lemma
-- `Function.toWithBotTopOn_of_mem` for the interval support.
/-- On the interval `[-3, 1]`, the Chapter 24 example is given by its explicit finite formula. -/
@[simp] theorem absMinusTwoSqrtOneSubExtension_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-3 : ℝ) 1) :
    absMinusTwoSqrtOneSubExtension x =
      ((|x| - 2 * Real.sqrt (1 - x) : ℝ) : WithBotTop ℝ) := sorry

-- Proof sketch: this is the canonical pointwise evaluation lemma
-- `Function.toWithBotTopOn_of_notMem` off the interval support.
/-- Outside the interval `[-3, 1]`, the Chapter 24 example takes the value `+∞`. -/
@[simp] theorem absMinusTwoSqrtOneSubExtension_of_not_mem_Icc {x : ℝ}
    (hx : x ∉ Set.Icc (-3 : ℝ) 1) :
    absMinusTwoSqrtOneSubExtension x = (⊤ : WithBotTop ℝ) := sorry

-- Proof sketch: check directly that the finite branch on `[-3, 1]` is convex and lower
-- semicontinuous, that the extension by `+∞` is proper, and then package these three properties
-- into the canonical owner `Function.IsClosedProperConvex`.
/-- The Chapter 24 example is a closed proper convex function on `ℝ`. -/
theorem absMinusTwoSqrtOneSubExtension_isClosedProperConvex :
    absMinusTwoSqrtOneSubExtension.IsClosedProperConvex := sorry

-- Proof sketch: compute the right secant-slope envelope separately on the four source regions
-- `x ≥ 1`, `0 ≤ x < 1`, `-3 ≤ x < 0`, and `x < -3`, using the explicit finite branch on
-- `[-3, 1]` and the `+∞` extension outside.
/-- The Chapter 24 owner `Function.rightDerivative` has the explicit profile stated in the
example. -/
theorem rightDerivative_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    rightDerivative absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ⊤
      else if 0 ≤ x then
        ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else if -3 ≤ x then
        ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else
        ⊥ := sorry

-- Proof sketch: compute the left secant-slope envelope region by region, paying attention to the
-- boundary points `x = 0` and `x = -3`, where the source formula distinguishes left and right
-- behavior.
/-- The Chapter 24 owner `Function.leftDerivative` has the explicit profile stated in the
example. -/
theorem leftDerivative_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    leftDerivative absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ⊤
      else if 0 < x then
        ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else if -3 < x then
        ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else
        ⊥ := sorry

-- Proof sketch: combine the explicit right- and left-derivative formulas above with
-- `subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative`, then simplify the resulting
-- interval description in each source region to the stated set-valued profile.
/-- Example 5.24.1: for the explicit function
`x ↦ |x| - 2 * sqrt (1 - x)` on `[-3, 1]` and `+∞` outside, the one-dimensional
subdifferential has the stated piecewise profile:
empty for `x ≥ 1` and `x < -3`, a singleton on `0 < x < 1` and `-3 < x < 0`, the interval
`[0, 2]` at `x = 0`, and `(-∞, -1 / 2]` at `x = -3`. -/
theorem subdifferentialAt_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    subdifferentialAt absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ∅
      else if 0 < x then
        {1 + (Real.sqrt (1 - x))⁻¹}
      else if x = 0 then
        Set.Icc 0 2
      else if -3 < x then
        {-1 + (Real.sqrt (1 - x))⁻¹}
      else if x = -3 then
        Set.Iic (-((1 : ℝ) / 2))
      else
        ∅ := sorry

end Function
