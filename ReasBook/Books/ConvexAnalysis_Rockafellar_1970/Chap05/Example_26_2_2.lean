import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_2_1

noncomputable section

open scoped Rockafellar

universe u

section

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜]

local notation "R2" => 𝕜 × 𝕜
/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 26.2.2 is a planar `WithBotTop 𝕜`-valued function obtained by adding
  the Chapter 10 quadratic-over-linear owner, the square of the second coordinate, and the
  indicator of the upper half-plane `ξ₂ ≥ 0`. The source-facing conclusions are its explicit
  finite branch formula, owner-level closed/proper/convexity, the relative-interior domain
  identification, strict convexity on that relative interior, the explicit constancy on the
  nonnegative `ξ₁`-axis, the extra subdifferentiability there, and the failure of essential strict
  convexity.
- `core/canonical`: the owner abstractions already present upstream are
  `quadraticOverLinearFunction`, `Function.IsClosedProperConvex`,
  `Function.IsEssentiallyStrictlyConvex`, `riDom[𝕜](·)`, and `dom∂(·)`.
- `bridge/view`: this file keeps the source-facing branch and axis sets directly as canonical
  pair-coordinate `Set` surfaces without adding extra set owners.

Domain-style sampling used here:
- `quadraticOverLinearFunction` from `Chap02.Theorem_10_1_4`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsEssentiallyStrictlyConvex` from `Chap05.Definition_26_2_1`;
- `dom∂(·)` and `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive source-facing data: the explicit example function, together with the source
  pair-coordinate positive-quadrant/nonnegative-axis/upper-half-plane set surfaces;
- derived API: the branch formula on the positive quadrant, owner-level
  `IsClosedProperConvex`, the `riDom[𝕜]` description, strict convexity on `riDom[𝕜]`, the
  pointwise constancy on the nonnegative `ξ₁`-axis, the `dom∂(·)` inclusion there, and the
  final non-essential-strict-convexity conclusion.

Layer target: `source-facing`.

Scalar/ambient minimality note:
- this item is stated on the pair ambient `R2 = 𝕜 × 𝕜`, matching the Chapter 10 owner
  `quadraticOverLinearFunction` directly and avoiding finite-index Euclidean coordinate wrappers;
- the codomain is the chapter-canonical `WithBotTop 𝕜`;
- the public surfaces use the generic chapter owners `riDom[𝕜](·)`, `dom∂(·)`, and
  `Function.IsEssentiallyStrictlyConvex` directly.
-/

/-- The Example 26.2.2 function on `R²`, obtained by adding the squared second coordinate and
the indicator of `ξ₂ ≥ 0` to the Chapter 10 quadratic-over-linear owner. -/
def positiveQuadrantPerspectiveSquare (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] :
    (𝕜 × 𝕜) → WithBotTop 𝕜 :=
  quadraticOverLinearFunction +
    (fun ξ : 𝕜 × 𝕜 ↦ (((ξ.2) ^ 2 : 𝕜) : WithBotTop 𝕜)) +
    (δ[𝕜](· | {ξ : 𝕜 × 𝕜 | 0 ≤ ξ.2}) : (𝕜 × 𝕜) → WithBotTop 𝕜)

-- Proof sketch: on the branch `ξ₁ > 0`, `ξ₂ ≥ 0`, the Chapter 10 owner
-- `quadraticOverLinearFunction` contributes `ξ₂² / (2 ξ₁)`, the added quadratic term contributes
-- `ξ₂²`, and the indicator term vanishes.
/-- On the source branch `ξ₁ > 0`, `ξ₂ ≥ 0`, Example 26.2.2 has the explicit finite-value formula
`ξ₂² / (2 ξ₁) + ξ₂²`. -/
theorem positiveQuadrantPerspectiveSquare_eq_of_pos_first_of_nonneg_second
    {ξ : R2} (hξ₁ : 0 < ξ.1) (hξ₂ : 0 ≤ ξ.2) :
    (positiveQuadrantPerspectiveSquare 𝕜) ξ =
      (((ξ.2) ^ 2 / (2 * ξ.1) + (ξ.2) ^ 2 : 𝕜) : WithBotTop 𝕜) := sorry

end

section

variable {𝕜 : Type u}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

local notation "R2" => 𝕜 × 𝕜
local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local instance instHasPairingPrimalStrongDual : HasPairing R2 (StrongDual 𝕜 R2) 𝕜 where
  pairing x xStar := xStar x

-- Proof sketch: the Chapter 10 quadratic-over-linear owner is convex and lower semicontinuous,
-- the added square term is everywhere finite and convex, and the indicator of the closed convex
-- half-plane `ξ₂ ≥ 0` is closed proper convex. The origin remains finite, so the sum is proper.
/-- The Example 26.2.2 function is closed, proper, and convex. -/
theorem positiveQuadrantPerspectiveSquare_isClosedProperConvex :
    IsClosedProperConvex[𝕜] (positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: the effective domain is `{ξ | 0 < ξ 0 ∧ 0 ≤ ξ 1} ∪ {0}` because the
-- quadratic-over-linear owner is finite exactly on `{ξ | 0 < ξ 0} ∪ {0}`, while the indicator
-- cuts away the half-plane `ξ₂ < 0`. The relative interior of that domain is therefore the open
-- positive quadrant.
/-- The relative interior of the effective domain of the Example 26.2.2 function is the open
positive quadrant. -/
theorem riDom_positiveQuadrantPerspectiveSquare_eq_positiveQuadrant :
    riDom[𝕜](positiveQuadrantPerspectiveSquare 𝕜) =
      {ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2} := sorry

-- Proof sketch: on `ri(dom f)`, namely the open positive quadrant from the previous theorem, the
-- formula is the sum of the strictly convex perspective term `ξ₂² / (2 ξ₁)` and the strictly
-- convex quadratic term `ξ₂²`, so `f` is strictly convex there.
/-- Example 26.2.2 is strictly convex on `ri(dom f)`. -/
theorem strictConvexOn_riDom_positiveQuadrantPerspectiveSquare :
    StrictConvexOn 𝕜 (riDom[𝕜](positiveQuadrantPerspectiveSquare 𝕜))
      (positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: if `ξ₂ = 0` and `ξ₁ ≥ 0`, then either `ξ = 0` or `ξ₁ > 0` with `ξ₂ = 0`. In
-- both cases the defining formula gives the finite value `0`.
/-- Along the nonnegative `ξ₁`-axis, Example 26.2.2 is identically zero. -/
theorem positiveQuadrantPerspectiveSquare_eq_zero_on_nonnegativeXAxis :
    Set.EqOn (positiveQuadrantPerspectiveSquare 𝕜) 0
      {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0} := sorry

-- Proof sketch: at every point of the nonnegative `ξ₁`-axis the function value is `0`, and
-- the affine support with slope `0` is valid there for the canonical primal/dual pairing
-- `HasPairing R2 (StrongDual 𝕜 R2) 𝕜`. Equivalently, one shows
-- `Function.subdifferentialAt positiveQuadrantPerspectiveSquare ξ (StrongDual 𝕜 R2) ≠ ∅`
-- for each such `ξ`, then rewrites this as membership in
-- `dom∂(positiveQuadrantPerspectiveSquare)`.
/-- The canonical subdifferential-domain owner `dom∂(f)` of the Example 26.2.2 function contains
the nonnegative `ξ₁`-axis. -/
theorem positiveQuadrantPerspectiveSquareNonnegativeXAxis_subset_domSubdifferential
    :
    {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0} ⊆
      dom∂(positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: the previous two theorems place the nonnegative `ξ₁`-axis inside `dom ∂f` and
-- show that the function is identically `0` there. Since that axis is convex, the defining
-- strict-convexity condition of `Function.IsEssentiallyStrictlyConvex` fails on a convex subset
-- of the subdifferential domain.
/-- Example 26.2.2: the function
`f(ξ₁, ξ₂) = ξ₂² / (2 ξ₁) + ξ₂²` on `ξ₁ > 0`, `ξ₂ ≥ 0`, with `f(0, 0) = 0` and `f = +∞`
otherwise, is closed proper convex and strictly convex on `ri(dom f)` but is not essentially
strictly convex because `dom ∂f` contains the nonnegative `ξ₁`-axis, where the function is
constant. -/
theorem positiveQuadrantPerspectiveSquare_not_isEssentiallyStrictlyConvex
    :
    ¬ Function.IsEssentiallyStrictlyConvex (f := positiveQuadrantPerspectiveSquare 𝕜) :=
  sorry

end
