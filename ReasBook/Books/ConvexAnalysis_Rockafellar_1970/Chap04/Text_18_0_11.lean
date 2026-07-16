import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

section

local notation "R3" => ℝ × ℝ × ℝ

/-!
Source/core/bridge triage:
- `source-facing`: the item gives a concrete counterexample, namely the convex hull of a torus in
  `ℝ³` together with the flat top disk whose rim consists of extreme but non-exposed points.
- `core/canonical`: mathlib's owner abstractions for pointwise extremality and exposedness are
  `Set.extremePoints` and `Set.exposedPoints`, while the relative boundary of the disk is written
  on the chapter surface as `rb(standardTorusTopDisk)`.
- `bridge/view`: the torus and its top disk are given as explicit sets in `R3 = ℝ × ℝ × ℝ`, and
  the source sentence is stated directly as a membership theorem for the canonical owner sets.

Domain-style sampling used here:
- `Set.extremePoints`;
- `mem_extremePoints`;
- `mem_exposedPoints_iff_exposed_singleton`;
- `rb`.

Primitive data vs derived API:
- primitive data: the concrete torus surface and the concrete top disk;
- derived API: the ambient convex body is the canonical owner
  `standardTorusHull = conv[ℝ] standardTorusSurface`, while extremality and exposedness of rim
  points are theorem-level properties expressed through `Set.extremePoints` and
  `Set.exposedPoints`.
-/

/-- The standard torus of major radius `2` and minor radius `1` in `ℝ³`, written in implicit
coordinates. -/
def standardTorusSurface : Set R3 :=
  {x | (Real.sqrt (x.1 ^ 2 + x.2.1 ^ 2) - 2) ^ 2 + x.2.2 ^ 2 = 1}

/-- Membership in `standardTorusSurface` is exactly the usual implicit torus equation. -/
@[simp] theorem mem_standardTorusSurface_iff {x : R3} :
    x ∈ standardTorusSurface ↔ (Real.sqrt (x.1 ^ 2 + x.2.1 ^ 2) - 2) ^ 2 + x.2.2 ^ 2 = 1 :=
  Iff.rfl

/-- The flat top disk of the convex hull of the standard torus, lying in the plane `z = 1`. -/
def standardTorusTopDisk : Set R3 :=
  {x | x.2.2 = 1 ∧ x.1 ^ 2 + x.2.1 ^ 2 ≤ 4}

/-- Membership in `standardTorusTopDisk` means lying in the horizontal disk of radius `2` at
height `1`. -/
@[simp] theorem mem_standardTorusTopDisk_iff {x : R3} :
    x ∈ standardTorusTopDisk ↔ x.2.2 = 1 ∧ x.1 ^ 2 + x.2.1 ^ 2 ≤ 4 :=
  Iff.rfl

/-- The convex hull of the standard torus surface. This is the ambient convex body in
Text 18.0.11. -/
def standardTorusHull : Set R3 :=
  conv[ℝ] standardTorusSurface

/-- Text 18.0.11 in primitive owner form: every point on the top rim of the torus cap is extreme
and not exposed in the torus hull. -/
theorem standardTorusTopRim_subset_extremePoints_and_not_exposedPoints :
    rb(standardTorusTopDisk) ⊆
      {x : R3 | x ∈ standardTorusHull.extremePoints ℝ ∧
        x ∉ standardTorusHull.exposedPoints ℝ} := by
  sorry

/-- Text 18.0.11 in set-difference bridge form. -/
theorem standardTorusTopRim_subset_extremePoints_diff_exposedPoints :
    rb(standardTorusTopDisk) ⊆
      standardTorusHull.extremePoints ℝ \ standardTorusHull.exposedPoints ℝ := by
  intro x hx
  simpa [Set.mem_diff] using
    (standardTorusTopRim_subset_extremePoints_and_not_exposedPoints hx)

/-- Pointwise primitive-owner form of Text 18.0.11. -/
theorem mem_extremePoints_and_not_mem_exposedPoints_of_mem_standardTorusTopRim
    {x : R3}
    (hx : x ∈ rb(standardTorusTopDisk)) :
    x ∈ standardTorusHull.extremePoints ℝ ∧
      x ∉ standardTorusHull.exposedPoints ℝ := by
  exact standardTorusTopRim_subset_extremePoints_and_not_exposedPoints hx

/-- Pointwise set-difference bridge form of Text 18.0.11. -/
theorem mem_extremePoints_diff_exposedPoints_of_mem_standardTorusTopRim
    {x : R3}
    (hx : x ∈ rb(standardTorusTopDisk)) :
    x ∈ standardTorusHull.extremePoints ℝ \ standardTorusHull.exposedPoints ℝ := by
  simpa [Set.mem_diff] using
    (mem_extremePoints_and_not_mem_exposedPoints_of_mem_standardTorusTopRim hx)

end
