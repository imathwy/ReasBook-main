import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage:

- `source-facing`: Text 14.0.15 is a concrete planar polar computation for one explicitly given set
  `C₄` and one explicitly given set `P`.
- `core/canonical`: the owner abstraction already present in the project is the set polar
  `Set.polar`, together with mathlib's convex-hull operator `convexHull ℝ`.
- `bridge/view`: the textbook notation `C₄ᵒ` is rendered directly by `Set.polar`, and the
  displayed formula `conv (P ∪ {0})` is rendered directly by `convexHull ℝ (P ∪ {0})`.

Domain-style sampling used here:
- the chapter owner `Set.polar` from `Text_14_0_5`;
- mathlib's `convexHull` for the convex hull of a subset of `R2`.

Primitive data vs derived API:
- primitive data: the two explicit subsets of `R2` given directly by the textbook formulas;
- derived API: the direct equality identifying the polar of the first set with the convex hull of
  the second set together with the origin.

Layer target: `source-facing`, stated directly through the source-facing set owners and the chapter
polar owner, without adding any surrogate abstraction.
-/

/-- The planar region `C₄ = {(ξ₁, ξ₂) | ξ₁ ≤ 1 - √(1 + ξ₂²)}` from Text 14.0.15. -/
def shiftedLeftHyperbolaRegion : Set R2 :=
  {x : R2 | x 0 ≤ 1 - Real.sqrt (1 + (x 1) ^ 2)}

/-- The planar set `P = {(ξ₁⋆, ξ₂⋆) | ξ₁⋆ ≥ √(1 + (ξ₂⋆)^2)}` from Text 14.0.15. -/
def rightHyperbolaEpigraph : Set R2 :=
  {xStar : R2 | Real.sqrt (1 + (xStar 1) ^ 2) ≤ xStar 0}

-- Proof sketch: compute membership in the polar of the shifted left-hyperbola region from the
-- defining inequality `⟪x, xStar⟫ ≤ 1` for all `x` in the shifted left-hyperbola region. The
-- supporting-line description of that region identifies the admissible dual vectors with the
-- convex hull of the
-- right-hyperbola epigraph and the origin.
/-- Text 14.0.15 (Example): if
`C₄ = {(ξ₁, ξ₂) | ξ₁ ≤ 1 - √(1 + ξ₂²)}` and
`P = {(ξ₁⋆, ξ₂⋆) | ξ₁⋆ ≥ √(1 + (ξ₂⋆)^2)}`,
then the polar of `C₄` is `conv (P ∪ {0})`. -/
theorem polar_shiftedLeftHyperbolaRegion_eq_convexHull_insert_rightHyperbolaEpigraph :
    shiftedLeftHyperbolaRegionᵒ[ℝ] = convexHull ℝ (insert 0 rightHyperbolaEpigraph) := sorry

end
