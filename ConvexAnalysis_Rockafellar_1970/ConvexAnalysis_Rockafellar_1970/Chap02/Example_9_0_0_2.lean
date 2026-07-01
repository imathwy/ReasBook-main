import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar
open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example fixes a specific closed proper convex function `h` on `R²`,
  projects it to the scalar first coordinate, studies the owner image function
  `(Prod.fst : ℝ × ℝ → ℝ) ◁ orthantExponential : ℝ → WithTopBot ℝ`, and concludes both
  that the image of `epi h` under `((x, μ) ↦ (x.1, μ))` need not be
  closed and that the
  projected scalar image is not lower semicontinuous at `0`.
- `core/canonical`: the owner abstractions already present in the project are the chapter
  construction `Function.linearImage` for the image of a `WithTopBot`-valued function under a
  map, the canonical convex-owner `ConvexOn ℝ Set.univ`, the chapter properness predicate
  `Function.IsProper`, and mathlib's
  `LowerSemicontinuous` / `LowerSemicontinuousAt`.
- `bridge/view`: the textbook three-branch formula is a companion pointwise description of the
  owner-side scalar image function `(Prod.fst : ℝ × ℝ → ℝ) ◁ orthantExponential`, and
  the image-set conclusion is stated directly through the corresponding owner bridge
  `linearImageEpigraph`.
- Primitive data vs derived API: the primitive source data are the explicit function `h` and the
  first-coordinate projection; the closedness, convexity, properness, and failure of lower
  semicontinuity are companion properties of these canonical objects.
- Layer target: the explicit function remains `source-facing`; the projected image is used directly
  through the `core/canonical` owner `Function.linearImage`, and the three-branch scalar formula
  is the main `bridge/view` result.

Domain-style sampling used here:
- `Function.linearImage` and `Function.linearImage_eq_sInf_image` from Theorem 5.7;
- `Function.isConvex_linearImage` from the same owner file;
- `Prod.fst` as the canonical first-coordinate projection map;
- `LowerSemicontinuousAt` and `lowerSemicontinuousAt_iff_le_liminf` from the Section 7
  semicontinuity API.
-/

local notation "π₁" => (Prod.fst : ℝ × ℝ → ℝ)

/-- The explicit function from the example, written on `R²` in owner coordinates. It equals
`exp (-sqrt (x₀ x₁))` on the nonnegative orthant and `+∞` elsewhere; the companion theorems below
state its lower semicontinuity, convexity, and properness. -/
def orthantExponential : (ℝ × ℝ) → WithTopBot ℝ :=
  fun x ↦
    if 0 ≤ x.1 ∧ 0 ≤ x.2 then
      Real.exp (-(Real.sqrt (x.1 * x.2)))
    else
      ⊤

-- Proof sketch: on the fiber above `ξ₁ < 0`, the nonnegative-orthant condition fails for every
-- point, so the infimum is `⊤`. On the fiber above `0`, every admissible point has value
-- `exp 0 = 1`. On the fiber above `ξ₁ > 0`, the values are `exp (-sqrt ξ₁ * sqrt ξ₂)` along
-- `ξ₂ ≥ 0`, and these decrease to `0` as `ξ₂ → +∞`, so the infimum is `0`.
/-- The projected image of the example function is the three-branch function described in the
textbook. -/
theorem orthantExponential_linearImage_fst_eq (ξ₁ : ℝ) :
    (π₁ ◁ orthantExponential) ξ₁ =
      if 0 < ξ₁ then
        (0 : WithTopBot ℝ)
      else if ξ₁ = 0 then
        (1 : WithTopBot ℝ)
      else
        ⊤ := sorry

-- Proof sketch: the nonnegative orthant is closed, and on that orthant the map
-- `(x₀, x₁) ↦ exp (-sqrt (x₀ x₁))` is continuous. The explicit piecewise formula therefore gives a
-- closed epigraph, i.e. lower semicontinuity of the source function.
/-- The source function in the example is lower semicontinuous. -/
theorem orthantExponential_lowerSemicontinuous :
    LowerSemicontinuous orthantExponential := sorry

-- Proof sketch: the real epigraph of the source function is the region above the graph of the
-- convex orthant exponential on the nonnegative quadrant, together with the vertical rays over the
-- complement. Check convexity directly from the explicit formula, or identify the defining
-- inequality with a convex epigraph condition on the orthant.
/-- The source function is convex on the whole ambient space, at the canonical owner layer
`ConvexOn ℝ Set.univ`. -/
theorem orthantExponential_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set (ℝ × ℝ)) orthantExponential := sorry

/-- Bridge to the chapter whole-space owner form of convexity. -/
theorem orthantExponential_isConvex :
    orthantExponential.IsConvex ℝ := by
  simpa [Function.IsConvex, Function.IsConvexOn] using orthantExponential_convexOn_univ

-- Proof sketch: `orthantExponential` is not identically `⊤`, because it takes the value
-- `1` at the origin, and it never takes the value `⊥`. These are exactly the chapter properness
-- conditions.
/-- The source function in the example is proper. -/
theorem orthantExponential_isProper :
    orthantExponential.IsProper := sorry

-- Proof sketch: identify
-- `linearImageEpigraph π₁ orthantExponential`
-- with the real
-- epigraph of `π₁ ◁ orthantExponential` using
-- `Function.linearImageEpigraph_eq_epi_linearImage`. If this image set were closed, the
-- corresponding scalar image function would be lower semicontinuous at `0`, contradicting the
-- explicit three-branch formula.
/-- Example 9.0.0.2: although the source function is closed proper convex, the image of its real
epigraph under `((x, μ) ↦ (x.1, μ))` is not closed. -/
theorem orthantExponential_linearImageEpigraph_fst_not_closed :
    ¬ IsClosed (linearImageEpigraph π₁ orthantExponential) :=
  sorry

-- Proof sketch: use the explicit formula from `orthantExponential_linearImage_fst_eq`. Along any
-- sequence `ξ₁ₙ ↓ 0` with `ξ₁ₙ > 0`, the projected image values are constantly `0`, so their
-- liminf is `0`, while the value at `0` is `1`. This violates the sequential criterion
-- `lowerSemicontinuousAt_iff_le_liminf`.
/-- Example 9.0.0.2: for the explicit closed proper convex function on `R²` given by
`exp (-sqrt (ξ₁ ξ₂))` on the nonnegative orthant and `+∞` elsewhere, the projected image under
`(ξ₁, ξ₂) ↦ ξ₁` is not lower semicontinuous at `0`. -/
theorem orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero :
    ¬ LowerSemicontinuousAt (π₁ ◁ orthantExponential) 0 :=
  sorry

end
