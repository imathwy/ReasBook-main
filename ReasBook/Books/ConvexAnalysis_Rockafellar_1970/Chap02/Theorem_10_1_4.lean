import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Rockafellar

section FunctionOwner

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1.4 introduces a specific quadratic-over-linear owner, identifies
  its effective domain and support-set representation, and then records continuity/path behavior at
  the boundary point `0`.
- `core/canonical`: the owner abstractions are the chapter support function `supportFunction`, the
  chapter convexity predicate `Function.IsConvex`, and the effective-domain owner `dom(·)`.
- `bridge/view`: continuity/path-limit consequences reuse Theorem 10.1's real topological owner
  layer, so they remain in the `𝕜 = ℝ` specialization section below.
- `bridge/view`: Rockafellar's coordinate formula is rendered directly as the concrete function
  `quadraticOverLinearFunction`, while the set
  `{(x₁, x₂) | x₁ + x₂² / 2 ≤ 0}` is rendered as `quadraticOverLinearSupportSet`.

Domain-style sampling used here:
- the project owner `supportFunction` from Definition 4.8.2;
- the project predicate `Function.IsConvex` from Theorem 4.2;
- the project theorem `Function.isConvex_supportFunction` sampled in Text 5.5.0.

Primitive data vs derived API:
- primitive source-facing data: the explicit function and its support set;
- auxiliary source-facing syntax: the parabolic approach in part (7) is kept directly in that
  theorem statement rather than packaged as a separate public wrapper;
- derived API: convexity, the effective-domain description, the support-function identity,
  continuity away from the boundary, lower semicontinuity at the origin, and the two contrasting
  path limits.

Layer target:
- core owner/API at the scalar-generic layer `R2 = 𝕜 × 𝕜`, codomain `WithTopBot 𝕜`;
- real topological consequences in the `𝕜 = ℝ` bridge section.
-/

/-- The scalar-generic quadratic-over-linear owner on `R² = 𝕜 × 𝕜`, valued in `WithTopBot 𝕜`,
extended by
the value `0` at the origin
and `+∞` elsewhere outside the open half-space `x₁ > 0`. -/
def quadraticOverLinearFunction : R2 → WithTopBot 𝕜 :=
  fun ξ ↦
    if 0 < ξ.1 then
      ((ξ.2 ^ 2 / (2 * ξ.1) : 𝕜) : WithTopBot 𝕜)
    else if ξ = 0 then
      (0 : WithTopBot 𝕜)
    else
      ⊤

/-- The Chapter 10 quadratic-over-linear owner never takes the value `⊥`; its only nonfinite
value is `⊤`. -/
theorem quadraticOverLinearFunction_neBot (ξ : R2) :
    quadraticOverLinearFunction ξ ≠ ⊥ := by
  unfold quadraticOverLinearFunction
  split_ifs with h0 hξ
  · simp
  · simp
  · simp

/-- Theorem 10.1.4 (2): the effective domain of the quadratic-over-linear example is
`{ξ | ξ₁ > 0} ∪ {(0, 0)}`, rendered canonically as `dom(quadraticOverLinearFunction)`. -/
-- Proof sketch: either `ξ.1 > 0`, in which case the finite quadratic-over-linear branch applies,
-- or `ξ.1 ≤ 0`. In the latter case the only finite point is `ξ = 0`, handled by the middle
-- branch; every other point falls in the `⊤` branch. This gives exactly the displayed union.
theorem quadraticOverLinearFunction_effectiveDomain :
    dom(quadraticOverLinearFunction) = {ξ : R2 | 0 < ξ.1} ∪ ({0} : Set R2) := sorry

end FunctionOwner

section SupportSetOwner

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-- The parabolic sublevel set `{(x₁, x₂) | 2 x₁ + x₂² ≤ 0}` used in Theorem 10.1.4. -/
def quadraticOverLinearSupportSet : Set R2 :=
  {x : R2 | (2 : 𝕜) * x.1 + x.2 ^ 2 ≤ 0}

end SupportSetOwner

section GenericBase

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-- Theorem 10.1.4 (3): the set
`quadraticOverLinearSupportSet = {(x₁, x₂) | 2 x₁ + x₂² ≤ 0}` is convex. -/
-- Proof sketch: write the defining inequality as the sublevel condition
-- `x.1 ≤ -x.2 ^ 2 / 2`. The right-hand side is a concave quadratic in the second coordinate, so
-- the hypograph is convex; equivalently, check the defining inequality directly on convex
-- combinations.
theorem quadraticOverLinearSupportSet_convex :
    Convex 𝕜 (quadraticOverLinearSupportSet : Set R2) := sorry

end GenericBase

section GenericRepresentation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [SupSet (WithTopBot 𝕜)]

local notation "R2" => 𝕜 × 𝕜
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot 𝕜)

local instance instHasPairingScalar : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

/-- Theorem 10.1.4 (4): the quadratic-over-linear example is the support function
`δᵛ(· | quadraticOverLinearSupportSet)` of the convex set
`quadraticOverLinearSupportSet = {(x₁, x₂) | 2 x₁ + x₂² ≤ 0}`. -/
-- Proof sketch: identify the support function of `quadraticOverLinearSupportSet` by maximizing
-- the affine functional `x ↦ ⟪ξ, x⟫` over the parabola boundary `x₁ = -x₂² / 2`. For `ξ₁ > 0`
-- the supremum is attained at `x₂ = ξ₂ / ξ₁` and equals `ξ₂² / (2 ξ₁)`; for `ξ₁ < 0` or
-- `ξ₁ = 0 ≠ ξ₂`, the supremum is `+∞`; at `ξ = 0` it is `0`.
theorem quadraticOverLinearFunction_eq_supportFunction :
    qol =
      (δᵛ(· | quadraticOverLinearSupportSet)) :=
    sorry

end GenericRepresentation

section GenericSupport

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot 𝕜)

/-- Theorem 10.1.4 (1): the quadratic-over-linear example is a convex function on `R²`. -/
-- Proof sketch: combine the support-function identity in part (4) with the chapter fact that the
-- support function of any set is convex.
theorem quadraticOverLinearFunction_isConvex :
    (qol).IsConvex 𝕜 := sorry

end GenericSupport

section RealBridge

local notation "R2" => ℝ × ℝ
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot ℝ)

/-- Theorem 10.1.4 (5), canonical intrinsic form: the quadratic-over-linear example is continuous
on the relative interior `riDom(quadraticOverLinearFunction)` of its effective domain. -/
theorem quadraticOverLinearFunction_continuousOn_riDom :
    ContinuousOn qol riDom(qol) :=
  (quadraticOverLinearFunction_isConvex : (qol).IsConvex ℝ).continuousOn_riDom

/-- Source-facing corollary of Theorem 10.1.4 (5): the quadratic-over-linear example is continuous
on the open half-space `{ξ : R2 | 0 < ξ.1}`. -/
-- Proof sketch: apply Theorem 10.1 on the relatively open convex subset
-- `{ξ : R2 | 0 < ξ.1} ⊆ dom(quadraticOverLinearFunction)` identified in part (2).
theorem quadraticOverLinearFunction_continuousOn_posFirstCoordinate :
    ContinuousOn qol {ξ : R2 | 0 < ξ.1} := by
  have hOpen : IsRelativelyOpen ℝ {ξ : R2 | 0 < ξ.1} :=
    (isOpen_lt continuous_const continuous_fst).isRelativelyOpen
  have hConv : Convex ℝ {ξ : R2 | 0 < ξ.1} := by
    simpa using convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear (0 : ℝ)
  have hDom : {ξ : R2 | 0 < ξ.1} ⊆ dom(qol) := by
    intro ξ hξ
    rw [quadraticOverLinearFunction_effectiveDomain]
    exact Or.inl hξ
  exact
    Function.IsConvex.continuousOn
      (quadraticOverLinearFunction_isConvex : (qol).IsConvex ℝ) hOpen hConv hDom

/-- Theorem 10.1.4 (6): at the relative-boundary point `(0, 0)`, the quadratic-over-linear
example is lower semicontinuous. -/
-- Proof sketch: all function values are nonnegative and the value at the origin is `0`, so every
-- liminf at `0` is at least `0 = quadraticOverLinearFunction 0`. Equivalently, use the
-- support-function representation from part (4) together with lower semicontinuity of support
-- functions.
theorem quadraticOverLinearFunction_lowerSemicontinuousAt_zero :
    LowerSemicontinuousAt qol 0 := sorry

/-- Theorem 10.1.4 (7): along the parabolic approach `ξ₁ = ξ₂² / (2 α)` with `α > 0`, the value
of the quadratic-over-linear example converges to `α` at the origin. -/
-- Proof sketch: along `t ↦ (t² / (2 α), t)` with `t ≠ 0`, for
-- `α > 0` the positive first-coordinate branch applies and simplifies identically to the
-- constant value `α`.
theorem quadraticOverLinearFunction_tendsto_parabolic_path
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun t : ℝ ↦ qol (t ^ 2 / (2 * α), t))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (α : WithTopBot ℝ)) := sorry

/-- Theorem 10.1.4 (8): along every ray `t ↦ t x` with `x₁ > 0`, the quadratic-over-linear
example tends to `0` as `t ↓ 0`. -/
-- Proof sketch: if `x₁ > 0`, then for every `t > 0` the point `t • x` stays in the branch
-- `ξ₁ > 0`, where the formula simplifies to
-- `quadraticOverLinearFunction (t • x) = t * (x₂² / (2 x₁))`. This tends to `0` as `t ↓ 0`.
theorem quadraticOverLinearFunction_tendsto_radial_to_zero
    {x : R2} (hx : 0 < x.1) :
    Tendsto (fun t : ℝ ↦ qol (t • x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (0 : WithTopBot ℝ)) := sorry

/-- Theorem 10.1.4 (9): the quadratic-over-linear example is not continuous at `(0, 0)`; the
limit depends on the path of approach. -/
-- Proof sketch: parts (7) and (8) give two approaches to the origin with different limits: `α`
-- along the parabola for any chosen `α > 0`, and `0` along every ray from a point with positive
-- first coordinate. Therefore the ordinary limit at `0` cannot exist, so the function is not
-- continuous there.
theorem quadraticOverLinearFunction_not_continuousAt_zero :
    ¬ ContinuousAt qol 0 := sorry

end RealBridge
