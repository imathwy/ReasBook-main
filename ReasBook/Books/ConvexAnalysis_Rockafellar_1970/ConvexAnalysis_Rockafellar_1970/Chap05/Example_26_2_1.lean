import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

local notation "R2" => ℝ × ℝ
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance instHasPairingPrimalStrongDual : HasPairing R2 (StrongDual ℝ R2) ℝ where
  pairing x xStar := xStar x

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 26.2.1 is a concrete planar `WithBotTop ℝ`-valued function with three
  source-facing claims: `dom ∂f` is the open positive quadrant, the function is strictly convex
  there but not on all of `dom(f)`, and nevertheless it is essentially strictly convex and
  essentially smooth.
- `core/canonical`: the owner abstractions already present in the chapter are
  `dom∂(f)`, `StrictConvexOn ℝ C g`,
  `Function.IsClosedProperConvex`, `Function.IsEssentiallyStrictlyConvex`, and
  `Function.IsEssentiallySmooth`, together with the upstream concrete owner
  `quadraticOverLinearFunction`.
- `bridge/view`: this item introduces no new owner. It is an explicit example function together
  with companion theorems stated directly on those existing owners, reusing the Chapter 10
  quadratic-over-linear owner rather than reimplementing its branch structure.

Domain-style sampling used here:
- `quadraticOverLinearFunction` from `Chap02.Theorem_10_1_4`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsEssentiallySmooth` from `Chap05.Definition_26_1_1`;
- `Function.IsEssentiallyStrictlyConvex` from `Chap05.Definition_26_2_1`;
- `dom∂(f)` from `Chap05.Definition_5_24_1`;
- pair-coordinate set surfaces `{ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2}` and
  `{ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0}`;
- `StrictConvexOn` from mathlib's convex-function owner layer.

Primitive data vs derived API:
- primitive source-facing data: the explicit function on `R²`, the open positive-quadrant set
  owner, and the nonnegative `ξ₁`-axis set;
- derived API: closed-proper-convexity of the example, the subdifferential-domain identification,
  strict convexity on the open quadrant, constancy on the axis, failure of strict convexity on the
  whole effective domain, and the final Chapter 26 essential-regularity conclusions.

Layer target: `source-facing`.
-/

/-- The open positive quadrant `{(ξ₁, ξ₂) | ξ₁ > 0, ξ₂ > 0}` in `R²`. -/
def quadraticSqrtExamplePositiveQuadrant : Set R2 :=
  {ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2}

/-- The nonnegative `ξ₁`-axis `{(ξ₁, 0) | ξ₁ ≥ 0}` in `R²`. -/
def quadraticSqrtExampleNonnegativeXAxis : Set R2 :=
  {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0}

/-- The quadratic-over-linear minus square-root function:
`f(ξ₁, ξ₂) = ξ₂² / (2 ξ₁) - 2 √ξ₂` for `ξ₁ > 0` and `ξ₂ ≥ 0`,
`f(0, 0) = 0`, and `f = +∞` otherwise. -/
def quadraticSqrtExampleFunction : R2 → WithBotTop ℝ :=
  quadraticOverLinearFunction +
    (fun ξ : R2 ↦ ((-(2 : ℝ) * Real.sqrt ξ.2 : ℝ) : WithBotTop ℝ)) +
    (δ(· | {ξ : R2 | 0 ≤ ξ.2}) : R2 → WithBotTop ℝ)

-- Proof sketch: rewrite the example as the sum of the quadratic-over-linear branch
-- `(ξ₁, ξ₂) ↦ ξ₂² / (2 ξ₁)` on `ξ₁ > 0, ξ₂ ≥ 0`, the convex branch `ξ₂ ↦ -2 √ξ₂`, and the
-- `+∞`-extension outside the half-strip together with the finite value at the origin. Convexity
-- comes from the perspective construction and convexity of `-sqrt`, properness from the explicit
-- finite value at `0`, and lower semicontinuity from the boundary behavior of the branch formula.
/-- The quadratic-over-linear minus square-root example function is closed, proper, and convex. -/
theorem quadraticSqrtExampleFunction_isClosedProperConvex :
    IsClosedProperConvex[ℝ] quadraticSqrtExampleFunction := sorry

-- Proof sketch: identify `interior (dom(f))` with the open positive quadrant. Then use the
-- Example 26.2.1 essential-smoothness theorem together with Theorem 26.1: for a closed proper
-- convex function, the subdifferential is nonempty exactly on `interior (dom(f))`.
/-- The subdifferential domain of the quadratic-over-linear minus square-root example function is
the open positive quadrant. -/
theorem quadraticSqrtExample_domSubdifferential_eq_positiveQuadrant :
    dom∂(quadraticSqrtExampleFunction) = quadraticSqrtExamplePositiveQuadrant := sorry

-- Proof sketch: on the open quadrant the finite real branch is smooth. Compute the Hessian of
-- `ξ₂² / (2 ξ₁) - 2 √ξ₂` and show it is positive definite there, yielding strict convexity of the
-- real branch on that open convex set.
/-- On the open positive quadrant, the finite real branch of the quadratic-over-linear minus
square-root example function is strictly convex. -/
theorem quadraticSqrtExample_strictConvexOn_positiveQuadrant :
    StrictConvexOn ℝ quadraticSqrtExamplePositiveQuadrant
      quadraticSqrtExampleFunction.realBranch := sorry

-- Proof sketch: if `ξ₂ = 0` and `ξ₁ ≥ 0`, then either `ξ = 0` or `ξ₁ > 0` with `ξ₂ = 0`. In
-- both cases the defining formula gives the finite value `0`, so every point of the nonnegative
-- `ξ₁`-axis lies in the effective domain.
/-- The nonnegative `ξ₁`-axis lies in the effective domain of the example function. -/
theorem quadraticSqrtExampleNonnegativeXAxis_subset_dom :
    quadraticSqrtExampleNonnegativeXAxis ⊆ dom(quadraticSqrtExampleFunction) := sorry

-- Proof sketch: evaluate the branch formula at `ξ₂ = 0`. The quadratic-over-linear term and the
-- square-root term both vanish, and the origin clause also gives `0`.
/-- Along the nonnegative `ξ₁`-axis, the quadratic-over-linear minus square-root example function
is identically zero. -/
theorem quadraticSqrtExample_eq_zero_on_nonnegativeXAxis :
    Set.EqOn quadraticSqrtExampleFunction 0
      quadraticSqrtExampleNonnegativeXAxis := sorry

-- Proof sketch: the nonnegative `ξ₁`-axis is contained in `dom(f)` by the previous theorem, and
-- the function is constant there. Taking two distinct axis points and their midpoint shows that
-- the strict-convexity inequality fails on `dom(f)`.
/-- The quadratic-over-linear minus square-root example function is not strictly convex on its
whole effective domain. -/
theorem quadraticSqrtExample_not_strictConvexOn_dom :
    ¬ StrictConvexOn ℝ (dom(quadraticSqrtExampleFunction))
      quadraticSqrtExampleFunction.realBranch := sorry

-- Proof sketch: on the open positive quadrant, Theorem 25.1 identifies the subdifferential with
-- the gradient of the finite branch, and the Hessian computation gives strict convexity there.
-- As `ξ₁ ↓ 0` or `ξ₂ ↓ 0` along the interior, the gradient norm tends to `∞`, giving essential
-- smoothness via Definition 26.1.1.
/-- Example 26.2.1: the quadratic-over-linear minus square-root example function is essentially
smooth. -/
theorem quadraticSqrtExampleFunction_isEssentiallySmooth :
    quadraticSqrtExampleFunction.IsEssentiallySmooth := sorry

-- Proof sketch: combine the closed/proper/convex owner, the identification
-- `dom∂(quadraticSqrtExampleFunction) = quadraticSqrtExamplePositiveQuadrant`, and strict
-- convexity of the real branch on that open quadrant. Any convex subset of `dom∂(f)` is then a
-- convex subset of the positive quadrant, so strict convexity restricts to it.
/-- Example 26.2.1: the quadratic-over-linear minus square-root example function is essentially
strictly convex. -/
theorem quadraticSqrtExampleFunction_isEssentiallyStrictlyConvex :
    Function.IsEssentiallyStrictlyConvex quadraticSqrtExampleFunction := sorry
