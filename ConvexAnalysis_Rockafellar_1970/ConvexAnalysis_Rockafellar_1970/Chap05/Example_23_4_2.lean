import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Convex RealInnerProductSpace Rockafellar

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 23.4.2 exhibits a function on `R²` whose subdifferential-domain set is
  not convex.
- `core/canonical`: the relevant chapter owners are `dom(·)`, the relative-interior notation
  `ri[ℝ](·)`, the segment owner `[x -[ℝ] y]`, the Chapter 12 regularity owner
  `Function.IsClosedProperConvex`, and the subgradient-domain owner
  `(Function.subdifferentialGraph f).dom`.
- `bridge/view`: the example-specific half-plane and exceptional segment remain source-facing
  subsets of `R²`, while the “subdifferentiability locus” itself is not kept as a parallel local
  wrapper around the canonical graph-domain owner.

Domain-style sampling used here:
- `dom(·)` from `Chap01.Definition_4_4`;
- `ri[𝕜](·)` from `Chap02.Text_6_8`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- the segment owner `[x -[𝕜] y]` from mathlib / `Chap01.Definition_2_0_2`;
- `Function.subdifferentialGraph` from `Chap05.Definition_5_24_3`.

Primitive data vs derived API:
- primitive owner-level object for the locus: `(Function.subdifferentialGraph f).dom`;
- derived/example-specific data: the explicit half-plane and exceptional segment describing that
  owner in this concrete counterexample, together with the owner-level regularity fact that the
  example itself is a closed proper convex function.

Layer target: `source-facing`, stated directly on the chapter owner surfaces rather than through
one-off local aliases for relation domains or relative interiors of segments.
-/

/-- The one-variable branch `g(ξ₁) = 1 - sqrt ξ₁` on `ξ₁ ≥ 0`, extended by `+∞` to `ξ₁ < 0`. -/
def sqrtBranch (x1 : ℝ) : WithBotTop ℝ :=
  if 0 ≤ x1 then ((1 - Real.sqrt x1 : ℝ) : WithBotTop ℝ) else ⊤

/-- The Example 23.4.2 counterexample function
`f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` on `R²`. -/
def subdifferentiabilityCounterexample (xi : R2) : WithBotTop ℝ :=
  max (sqrtBranch (xi 0)) (((|xi 1|) : ℝ) : WithBotTop ℝ)

-- Proof sketch: `sqrtBranch` is the sum of the indicator of the closed half-line `[0, ∞)` and
-- the continuous convex branch `x₁ ↦ 1 - sqrt x₁` on that half-line, so it is closed proper
-- convex as a one-variable extended-real function. The map `ξ ↦ |ξ₂|` is a finite continuous
-- convex function on `R²`, hence also closed proper convex after the canonical codomain lift.
-- Taking the pointwise maximum preserves convexity and lower semicontinuity, and properness holds
-- because `(0, 0)` is a finite point while neither branch ever attains `⊥`.
/-- Example 23.4.2: the explicit counterexample function itself lies in the canonical convex-
analysis owner layer of closed proper convex functions. -/
theorem subdifferentiabilityCounterexample_isClosedProperConvex :
    subdifferentiabilityCounterexample.IsClosedProperConvex (𝕜 := ℝ) := sorry

/-- The closed right half-plane `ξ₁ ≥ 0` in `R²`. -/
def rightHalfPlane : Set R2 :=
  {xi | 0 ≤ xi 0}

private def upperEndpoint : R2 :=
  EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private def lowerEndpoint : R2 :=
  EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)

/-- The relative interior of the segment joining `(0, 1)` and `(0, -1)`. -/
def exceptionalSegment : Set R2 :=
  ri[ℝ]([upperEndpoint -[ℝ] lowerEndpoint])

-- Proof sketch: the first-coordinate branch is finite exactly on `x1 ≥ 0`, while the second
-- branch `|ξ₂|` is finite everywhere. Therefore the pointwise maximum is finite exactly on the
-- closed right half-plane.
/-- The effective domain of the Example 23.4.2 counterexample is the closed right half-plane. -/
theorem dom_subdifferentiabilityCounterexample :
    dom(subdifferentiabilityCounterexample) = rightHalfPlane := sorry

-- Proof sketch: combine the explicit domain computation above with the Chapter 23
-- subdifferentiability criterion for maxima. On the boundary line `ξ₁ = 0`, the one-variable
-- branch `1 - sqrt ξ₁` has no supporting subgradient for `|ξ₂| < 1`, producing exactly the
-- relative interior of the vertical segment as the exceptional set; elsewhere on the domain a
-- supporting vector exists.
/-- Example 23.4.2: for the function `f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` with
`g(ξ₁) = 1 - sqrt ξ₁` on `ξ₁ ≥ 0` and `g(ξ₁) = +∞` on `ξ₁ < 0`, the subdifferentiability locus is
the effective domain minus the relative interior of the segment joining `(0, 1)` and `(0, -1)`. -/
theorem subdifferentialGraph_dom_eq_dom_diff_exceptionalSegment :
    (Function.subdifferentialGraph subdifferentiabilityCounterexample).dom =
      dom(subdifferentiabilityCounterexample) \ exceptionalSegment := sorry

-- Proof sketch: by the theorem above, both endpoints `(0, 1)` and `(0, -1)` lie in the
-- subdifferentiability locus, while their midpoint `(0, 0)` lies in the exceptional segment and
-- therefore does not. Hence the locus fails the midpoint test for convexity.
/-- The subdifferentiability locus in Example 23.4.2 is not convex. -/
theorem not_convex_subdifferentialGraph_dom :
    ¬ Convex ℝ (Function.subdifferentialGraph subdifferentiabilityCounterexample).dom := sorry
