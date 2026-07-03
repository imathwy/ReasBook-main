import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_14_0_13 (from Chap03) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.13 repeats the simplex example whose set is given by coordinatewise
  nonnegativity together with the mass bound `∑ i, x i ≤ 1`, and whose polar is described by the
  coordinatewise inequalities `xStar i ≤ 1`.
- `core/canonical`: the owner abstractions are already in the immediately preceding file:
  `unitSimplexSet` for the source-facing set and
  `polar_unitSimplexSet_eq_coordinatewise_le_one` for its polar computation.
- `bridge/view`: this file contributes no additional mathematics beyond reusing that exact
  chapter-level theorem, so it should not keep a second local set name or a renamed duplicate
  theorem.

Domain-style sampling used here:
- the chapter owner `Set.polar`;
- the owner-side membership criterion `Set.mem_polar_iff`;
- the source-facing set `unitSimplexSet`;
- the exact theorem
  `polar_unitSimplexSet_eq_coordinatewise_le_one`.

Primitive data vs derived API:
- primitive data: already owned upstream by `unitSimplexSet`;
- derived API: already owned upstream by
  `polar_unitSimplexSet_eq_coordinatewise_le_one`.

Layer target: `bridge/view`; this numbered item is a direct canonical reuse of the preceding
source-facing simplex-polar theorem.
-/

/- Text 14.0.13 repeats the simplex-polar computation already formalized in Text 14.0.12, so the
canonical chapter theorem is recalled directly instead of introducing a duplicate local set and a
parallel theorem name. -/
recall polar_unitSimplexSet_eq_coordinatewise_le_one

/-! ### Text_14_0_14 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "e1" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "D" => (Metric.closedBall e1 1 : Set R2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.14 gives an explicit planar example, identifying the polar of the
  closed unit disk centered at `(1, 0)` by a coordinate inequality.
- `core/canonical`: the owner abstractions are the set polar `Set.polar` and the metric closed
  ball `Metric.closedBall a r`, with `supportFunction_closedBall` giving the owner-side support
  function formula for that disk.
- `bridge/view`: the textbook coordinates `(ξ₁, ξ₂)` and `(ξ₁⋆, ξ₂⋆)` are rendered directly by the
  two coordinates of `R2 = EuclideanSpace ℝ (Fin 2)`, while the phrase “closed unit disk centered
  at `(1, 0)`” is rendered canonically by `Metric.closedBall e1 1`; the displayed coordinate
  parabola is the coordinate form of the owner inequality `xStar 0 + ‖xStar‖ ≤ 1`.

Domain-style sampling used here:
- the source-facing owner `Set.polar`;
- the membership reformulation `Set.mem_polar_iff`;
- the canonical Euclidean-ball owner `Metric.closedBall a r`;
- the nearby chapter support-function owner theorem `supportFunction_closedBall`.

Primitive data vs derived API:
- primitive data: the canonical closed disk `D = Metric.closedBall e1 1`, i.e. the closed unit
  disk centered at `e1`;
- derived API: the owner-side polar equality
  `Dᵒ = {xStar | xStar 0 + ‖xStar‖ ≤ 1}` and its coordinate parabola reformulation.

Layer target: `source-facing`; the main theorem keeps the intrinsic owner inequality for the
polar of the canonical closed ball, while the displayed coordinate parabola appears only as a
derived `bridge/view` reformulation.
-/

-- Proof sketch: unfold `Set.polar`, so the claim becomes the support-function sublevel condition
-- for the closed ball, then evaluate that support function with
-- `supportFunction_closedBall e1 1 (by positivity)`. Since `⟪xStar, e1⟫ = xStar 0`, this yields
-- the
-- owner inequality `xStar 0 + ‖xStar‖ ≤ 1`.
/-- Text 14.0.14, owner form: the polar of the closed unit disk centered at `(1, 0)`,
formalized canonically as `D = Metric.closedBall e1 1`, is the set of `xStar` satisfying the
intrinsic inequality `xStar 0 + ‖xStar‖ ≤ 1`. -/
theorem polar_unit_disk_centered_at_one_zero_eq :
    Dᵒ[ℝ] = {xStar : R2 | xStar 0 + ‖xStar‖ ≤ (1 : ℝ)} := sorry

-- Proof sketch: start from the owner-form theorem above. The inequality `xStar 0 + ‖xStar‖ ≤ 1`
-- is equivalent to `‖xStar‖ ≤ 1 - xStar 0`, which forces `xStar 0 ≤ 1` and can therefore be
-- squared without changing its meaning. Expanding `‖xStar‖ ^ 2 = (xStar 0) ^ 2 + (xStar 1) ^ 2`
-- then simplifies the owner inequality to the displayed coordinate parabola.
/-- Text 14.0.14, coordinate reformulation: the owner inequality
`xStar 0 + ‖xStar‖ ≤ 1` for the polar of the shifted unit disk is equivalent to the parabola
equation `xStar 0 ≤ (1 - (xStar 1)^2) / 2`. -/
theorem polar_unit_disk_centered_at_one_zero_eq_parabola :
    Dᵒ[ℝ] = {xStar : R2 | xStar 0 ≤ (1 - (xStar 1) ^ 2) / 2} := sorry

end

/-! ### Text_14_0_15 (from Chap03) -/
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
