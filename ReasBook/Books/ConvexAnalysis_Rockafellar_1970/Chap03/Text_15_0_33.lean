import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_13_5_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open ConvexERealFunction
open scoped Rockafellar

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

local notation "P" => ℝ × E

/-!
Source/core/bridge triage for this item.

- `source-facing`: under the standing Chapter 15 convexity/closedness/nonnegativity
  normalization hypotheses, the item identifies the epigraph of the obverse `g` with the unit
  sublevel set of the closed perspective of `f`.
- `core/canonical`: the owner layer is the existing chapter API `perspective`,
  `ConvexERealFunction.lowerSemicontinuousHull`, the owner formula
  `lowerSemicontinuousHull_perspective_apply`, and the Chapter 15 declarations
  `Function.rightScalarMul` and `obverse` from Text 15.0.31.
- `bridge/view`: the epigraph statement is written directly in the source coordinates
  `(λ, x) ∈ ℝ × E`, so no swapped-coordinate wrapper is introduced.

Domain-style sampling used here:
- `perspective`;
- `lowerSemicontinuousHull_perspective_apply`;
- `rightScalarMul`;
- `obverse`;

Primitive data vs derived API:
- primitive imported owners: `perspective`, `cl(·)`, `rightScalarMul`, and `obverse`;
- derived API in this file: the source-facing epigraph/sublevel-set identification theorem under
  the standing hypotheses from Text 15.0.31.

Layer target: `source-facing`; the main theorem keeps the textbook epigraph statement while
reusing the existing closed-perspective owner instead of introducing a parallel local three-branch
wrapper.
-/

-- Proof sketch: `lowerSemicontinuousHull_perspective_apply` identifies `cl(perspective f)` with
-- the textbook three-branch function whose positive branch is the scaled perspective `f_λ`, whose
-- boundary branch is `f0⁺`, and whose negative branch is `+∞`. Under the Chapter 15 owner
-- hypothesis `f.IsNonnegativeClosedConvexZero`, the admissible set in `obverse f x` is a
-- closed upper ray, so `obverse f x ≤ λ` is equivalent to the condition that this three-branch
-- value at `(λ, x)` is at most `1`. Thus the source-coordinate epigraph of `obverse f` is exactly
-- the unit sublevel set of the closed perspective of `f`.
/-- Text 15.0.33: the epigraph of the obverse `g` of `f`, written in the source coordinates
`(λ, x) ∈ ℝ × E`, is the unit sublevel set of the closed perspective `cl(perspective f)`.
Equivalently, the set `{(λ, x) | g x ≤ λ}` is exactly the set where `cl(perspective f) (λ, x) ≤
1`, under the standing Chapter 15 hypothesis package `f.IsNonnegativeClosedConvexZero`.
The textbook three-branch profile `h(λ, x)` is therefore reused here through the existing owner
`cl(perspective f)` rather than a parallel local wrapper. -/
theorem obverse_epigraph_eq_one_sublevel_closedPerspective
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    {p : P | cl(perspective f) p ≤ (1 : EReal)} =
      {p : P | obverse f p.2 ≤ p.1} := sorry

end
