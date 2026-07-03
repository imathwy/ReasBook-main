import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology WithTopConvexAnalysis

universe u

section Ambient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "S" => Metric.sphere (0 : E) 1
local notation "B" => Metric.closedBall (0 : E) 1

/- Proposition 3.8 lies in the chapter's source-facing unit-disk boundary-extension domain,
generalized from the textbook display model `ℝ²` to the intrinsic owner level of a real normed
space.

Sampled owner-style declarations:
- mathlib `Metric.sphere` and `Metric.closedBall`, the canonical owners of the unit boundary and
  unit closed ball;
- chapter `dom` and `withTopRealPart` from `Definition_3_3`;
- chapter `WithTopConvexAnalysis.effectiveEpigraph` from `Definition_3_3`;
- mathlib `ConvexOn`, the canonical convexity owner on the effective domain;
- mathlib `LowerSemicontinuous`.

Best owner abstraction:
- source-facing: `unitDiskBoundaryExtension`, the textbook unit-disk construction viewed through
  the intrinsic unit-ball owner;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`, `dom f`, and
  `LowerSemicontinuous f`, together with the canonical unit sphere and closed unit ball;
- bridge/view: the effective-epigraph formulation of convexity and the specialization
  `E = EuclideanSpace ℝ (Fin 2)` recovering the textbook unit disk and unit circle.

Primitive data:
- the ambient real normed space `E`;
- the boundary datum `φ : S → ℝ`;
- the source-facing extension `unitDiskBoundaryExtension φ`.

Derived API:
- the open-disk value theorem below;
- the canonical convexity-plus-domain theorem below;
- the lower-semicontinuity criterion below.

The previous theorem surface stated convexity via `constrainedEpigraph Set.univ`, which duplicates
the chapter owner view. This file now uses the canonical `ConvexOn` surface on `dom` directly and
keeps the domain identification as the companion part of the same source-facing proposition. -/

/-- The textbook unit-disk boundary extension, stated at the intrinsic owner level of a real
normed space: it is `0` on the open unit ball, equal to `φ` on the unit sphere, and `⊤` outside
the closed unit ball. Specializing `E = EuclideanSpace ℝ (Fin 2)` recovers the source statement
on the unit disk and unit circle. -/
def unitDiskBoundaryExtension (φ : S → ℝ) : E → WithTop ℝ :=
  let _ : DecidablePred fun x : E ↦ x ∈ S := Classical.decPred _
  fun x ↦
    if _hx : ‖x‖ < 1 then
      (0 : WithTop ℝ)
    else if hs : x ∈ S then
      (φ ⟨x, hs⟩ : WithTop ℝ)
    else
      ⊤

/-- On the open unit ball, `unitDiskBoundaryExtension φ` takes the value `0`. -/
-- Proof sketch: unfold `unitDiskBoundaryExtension` and simplify the first `if` with the strict
-- inequality hypothesis.
theorem unitDiskBoundaryExtension_eq_zero_of_norm_lt_one
    {φ : S → ℝ} {x : E} (hx : ‖x‖ < 1) :
    unitDiskBoundaryExtension φ x = 0 := sorry

/-- Proposition 3.8 at the intrinsic owner level: for a nonnegative function on the unit sphere,
the associated extended-real-valued unit-ball boundary extension is convex in the chapter owner
sense, and its effective domain is exactly the closed unit ball. Specializing to
`EuclideanSpace ℝ (Fin 2)` recovers the textbook unit-disk statement. -/
-- Proof sketch: compute `dom (unitDiskBoundaryExtension φ)` as the closed unit ball. Then verify
-- Jensen's inequality for `withTopRealPart (unitDiskBoundaryExtension φ)` on that domain, using
-- that the interior value is `0` while the boundary datum is nonnegative.
theorem unitDiskBoundaryExtension_convex_and_effectiveDomain
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    ConvexOn ℝ (dom (unitDiskBoundaryExtension φ))
      (withTopRealPart (unitDiskBoundaryExtension φ)) ∧
      dom (unitDiskBoundaryExtension φ) = B := sorry

/-- The unit-ball boundary extension is lower semicontinuous exactly when the boundary datum
vanishes identically on the unit sphere. Specializing to `EuclideanSpace ℝ (Fin 2)` recovers the
textbook unit-disk criterion. -/
-- Proof sketch: if `φ = 0`, the function is the indicator of the closed unit ball. Conversely,
-- approach a boundary point by points from the open unit ball where the function is `0`, and use
-- semicontinuity plus the nonnegativity of `φ`.
theorem unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    LowerSemicontinuous (unitDiskBoundaryExtension φ) ↔ ∀ z : S, φ z = 0 := sorry

end Ambient

end
