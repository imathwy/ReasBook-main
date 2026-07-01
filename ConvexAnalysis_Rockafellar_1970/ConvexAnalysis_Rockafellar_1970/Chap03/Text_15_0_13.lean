import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped GaugePolar
open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]

section CoordinateL1GaugeOwner

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜]

/-- The coordinate `ℓ¹` norm on a finite coordinate space, viewed as a
`WithBotTop 𝕜`-valued gauge. Specializing `𝕜 = ℝ` and `ι = Fin n` recovers the textbook
function on `R^n`. -/
def coordinateL1Gauge (ι : Type*) [Fintype ι] : (ι → 𝕜) → WithBotTop 𝕜 :=
  fun x ↦ ((∑ i, |x i|) : 𝕜)

end CoordinateL1GaugeOwner

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

local instance : HasPairing E E 𝕜 where
  pairing x y := ∑ i, x i * y i
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

local notation "linftyGauge" => Function.toWithBotTop (linftyNorm (ι := ι) (𝕜 := 𝕜))
local notation "l1Gauge" => (coordinateL1Gauge (𝕜 := 𝕜) ι : E → WithBotTop 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text defines the concrete function
  `k(x) = max {|ξ₁|, ..., |ξₙ|}` on a finite coordinate space, identifies its polar gauge with
  the coordinate `ℓ¹` norm, and concludes that these two norms form a polar pair. Specializing
  `ι = Fin n` recovers the textbook `R^n` statement.
- `core/canonical`: the owner abstractions already present in the project are the Chapter 1
  owners `coordinateL1Ball` and `linftyNorm`, the theorem
  `supportFunction_coordinateL1Ball_eq_linftyNorm`, the source-side polar-gauge construction
  `gauge_polar` from `Text_15_0_5`, and the norm-gauge predicate `IsGaugeNorm` from
  `Text_15_0_12`.
- `bridge/view`: `supportFunction_coordinateL1Ball_eq_linftyNorm` keeps the source's explicit
  coordinate `ℓ¹` unit ball as the bridge presentation of that canonical `L^∞` norm, while the
  coordinate `ℓ¹` norm remains the explicit finite sum `∑ i, |x i|`, lifted to
  `WithBotTop 𝕜`.

Domain-style sampling used here:
- the Chapter 1 owner `coordinateL1Ball`;
- the Chapter 1 owner `linftyNorm`;
- the Chapter 1 owner theorem `supportFunction_coordinateL1Ball_eq_linftyNorm`;
- the bridge theorem `supportFunction_coordinateL1Ball_eq_linftyNorm`;
- `gauge_polar` from `Text_15_0_5`;
- `IsGaugeNorm` from `Text_15_0_12`;
- the nearby finite-family owner `lpCoordinatePower` from `Text_15_0_22`;
- the owner function `supportFunction` attached to subsets of a finite coordinate space.

Primitive data vs derived API:
- primitive source-facing data: the concrete coordinate `ℓ¹` gauge;
- owner-level reused data: the concrete max-coordinate norm is expressed through the canonical
  owner `linftyNorm`;
- bridge/source view: `supportFunction_coordinateL1Ball_eq_linftyNorm` relates that owner to the
  `supportFunction` of the explicit coordinate `ℓ¹` unit ball;
- derived API: each is a norm-gauge, and each is the polar gauge of the other.

Layer target: `source-facing`, stated on the chapter's canonical finite-family owner level rather
than the concrete `𝕜 = ℝ`, `ι = Fin n` display specialization, with the `L^∞` owner reused from
Text 5.5.0.5 rather than redefined here.
-/

-- Proof sketch: rewrite the polar-gauge defining inequalities for the coordinate-maximum owner as
-- `⟪x, xStar⟫ ≤ μStar * max_i |x i|`. If `μStar = ∑ i |xStar i|`, Hölder's
-- `ℓ∞`-`ℓ¹` estimate gives an admissible majorant. Conversely, evaluate on the sign vector of
-- `xStar` to show no smaller majorant can work, yielding the exact coordinate `ℓ¹` formula.
/-- The polar gauge of the coordinate-maximum norm is the coordinate `ℓ¹` norm. -/
theorem gauge_polar_linftyNorm_eq_coordinateL1Gauge
    :
    ((linftyGauge)ᵒ : E → WithBotTop 𝕜) = l1Gauge := sorry

-- Proof sketch: the coordinate `ℓ¹` norm is finite, symmetric, positively homogeneous, and
-- subadditive by the corresponding scalar properties of absolute value and finite sums. Strict
-- positivity away from the origin follows because some coordinate of a nonzero vector has
-- nonzero absolute value and therefore contributes positively to the sum.
/-- The coordinate `ℓ¹` norm defines a norm-gauge on a finite coordinate space. -/
theorem coordinateL1Gauge_isGaugeNorm :
    IsGaugeNorm l1Gauge := sorry

-- Proof sketch: express `gauge_polar coordinateL1Gauge x` through the defining admissible-majorant
-- inequalities `⟪y, x⟫ ≤ μ * ∑ i |y i|`. Testing these inequalities on the signed coordinate basis
-- vectors forces `μ` to dominate every `|x i|`, so `μ` must dominate the coordinate supremum.
-- Conversely, taking `μ = max_i |x i|` makes the inequality hold by bounding each term
-- `|y i| |x i|` by `μ |y i|` and summing.
/-- The polar gauge of the coordinate `ℓ¹` norm is the maximum-coordinate norm. -/
theorem gauge_polar_coordinateL1Gauge_eq_linftyNorm
    :
    (l1Gaugeᵒ : E → WithBotTop 𝕜) = linftyGauge := sorry

end
