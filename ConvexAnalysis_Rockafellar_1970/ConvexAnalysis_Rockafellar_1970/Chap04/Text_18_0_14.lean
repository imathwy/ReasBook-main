import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.ParaboloidEpigraph
import ConvexAnalysis_Rockafellar_1970.Chap02.RecessionConeConeBridge
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Convex

/-!
Source/core/bridge triage:

- `source-facing`: this item says that every extreme direction and every exposed direction of a
  closed convex set in an ordered topological vector space over `𝕜` yields an extreme,
  respectively exposed, ray of its recession cone.
- `core/canonical`: the chapter owners for this geometry are `Set.extremeDirections`,
  `Set.exposedDirections`, `affineHalfLine`, `originRay`, the recession-cone owner
  `recessionCone`, and the canonical exposed/extreme-face owners `IsExposed` / `IsExtreme` on
  `0⁺[𝕜] C`.
- `bridge/view`: `ConvexCone.IsExtremeRay` and `ConvexCone.IsExposedRay` on the bundled view
  `Set.recessionConeCone C 𝕜` are retained as downstream interoperability bridges.
- `bridge/view`: a source half-line face of `C` is rendered canonically as `affineHalfLine x r`;
  the Chapter 8 recession owner is compared to mathlib's `asymptoticCone 𝕜 C` by
  `Convex.recessionCone_eq_asymptoticCone`, and the textbook nonnegative scalar ray is only the
  view `originRay_eq_nonnegative_smul_singleton r.someVector_ne_zero`.

Domain-style sampling used here:
- `Set.extremeDirections`;
- `Set.exposedDirections`;
- `Convex.mem_recessionCone_of_nonneg_ray`;
- `Convex.recessionCone_eq_asymptoticCone`.

Primitive data vs derived API:
- primitive data: a direction ray `r : Module.Ray 𝕜 E` and, for the source-facing half-line, a
  base point `x`;
- derived API: extremality and exposedness stay theorem-level properties of the canonical owner
  directions as `IsExtreme` / `IsExposed` on `0⁺[𝕜] C`; the bundled ray owners
  `ConvexCone.IsExtremeRay` / `ConvexCone.IsExposedRay` are exposed only as bridge lemmas through
  `Set.recessionConeCone`. The step from a
  half-line contained in `C` to a recession direction uses the owner-side
  theorem `Convex.mem_recessionCone_of_nonneg_ray`, and closedness of `0⁺[𝕜] C` is controlled by
  the Chapter 8 asymptotic-cone bridge `Convex.recessionCone_eq_asymptoticCone`, so the ambient
  space must already be an ordered topological vector space over `𝕜` with compatible addition and
  scalar multiplication.
- Layer target: `source-facing`, with the recession-cone step routed through the existing Chapter 8
  owner API rather than a parallel local cone wrapper.
-/

/-- Text 18.0.14: in an ordered topological vector space over `𝕜`, every extreme direction of a
closed convex set `C` determines an extreme origin half-line of its recession cone `0⁺[𝕜] C`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
-- Proof sketch: if `r ∈ C.extremeDirections`, choose `x` with `affineHalfLine x r` an
-- extreme face of `C`. The whole forward half-line from `x` in direction `r` lies in `C`, so
-- Theorem 8.3 puts the direction into `0⁺[𝕜] C`. To prove extremality of the origin ray,
-- translate a segment in `0⁺[𝕜] C` whose interior point lies on that ray back to a
-- segment in `C`; extremality of `affineHalfLine x r` forces both endpoints onto the same
-- half-line, hence onto the same origin ray.
theorem isExtreme_originRay_recessionCone_of_mem_extremeDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.extremeDirections 𝕜) :
    IsExtreme 𝕜 (0⁺[𝕜] C) (originRay r) := sorry

/-- Bridge to the direction-owner surface: every extreme direction of a closed convex set induces
an extreme ray direction of the bundled recession cone view. -/
theorem isExtremeRay_recessionCone_of_mem_extremeDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.extremeDirections 𝕜) :
    (Set.recessionConeCone C 𝕜).IsExtremeRay r := by
  simpa [ConvexCone.IsExtremeRay, Set.coe_recessionConeCone] using
    (hC_convex.isExtreme_originRay_recessionCone_of_mem_extremeDirections
      (hC_closed := hC_closed) (hr := hr))

/-- Text 18.0.14: in an ordered topological vector space over `𝕜`, every exposed direction of a
closed convex set `C` determines an exposed origin half-line of its recession cone `0⁺[𝕜] C`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
-- Proof sketch: if `r ∈ C.exposedDirections 𝕜`, choose `x` with `affineHalfLine x r` exposed
-- in `C`. As above, the supporting half-line gives a recession direction. Translate the exposing
-- functional so that the base point becomes the origin; the same functional then cuts out
-- `originRay r` inside `0⁺[𝕜] C`.
theorem isExposed_originRay_recessionCone_of_mem_exposedDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    IsExposed 𝕜 (0⁺[𝕜] C) (originRay r) := sorry

/-- Bridge to the direction-owner surface: every exposed direction of a closed convex set induces
an exposed ray direction of the bundled recession cone view. -/
theorem isExposedRay_recessionCone_of_mem_exposedDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    (Set.recessionConeCone C 𝕜).IsExposedRay r := by
  simpa [ConvexCone.IsExposedRay, Set.coe_recessionConeCone] using
    (hC_convex.isExposed_originRay_recessionCone_of_mem_exposedDirections
      (hC_closed := hC_closed) (hr := hr))

end Convex

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The upward vertical direction ray in `𝕜²`, used in the paraboloid counterexample. -/
noncomputable def paraboloidVerticalRay : Module.Ray 𝕜 (𝕜 × 𝕜) :=
  rayOfNeZero 𝕜 ((0 : 𝕜), (1 : 𝕜)) (by simp)

end

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsTopologicalRing 𝕜]

/-!
The following declarations formalize the standard paraboloid epigraph counterexample witnessing
that the converse in Text 18.0.14 fails.
-/

/-- The vertical origin half-line is an extreme ray of the recession cone of the paraboloid
epigraph. -/
-- Proof sketch: the recession cone of `paraboloidEpigraph` is the nonnegative vertical axis, so
-- its only nontrivial direction ray is extreme.
theorem paraboloidVerticalRay_isExtreme_recessionCone :
    IsExtreme 𝕜 (0⁺[𝕜] (paraboloidEpigraph : Set (𝕜 × 𝕜)))
      (originRay paraboloidVerticalRay) := sorry

/-- The vertical origin half-line is an extreme ray direction of the bundled recession-cone view
of the paraboloid epigraph. -/
theorem paraboloidVerticalRay_isExtremeRay_recessionCone :
    (Set.recessionConeCone (paraboloidEpigraph : Set (𝕜 × 𝕜)) 𝕜).IsExtremeRay
      paraboloidVerticalRay := by
  simpa [ConvexCone.IsExtremeRay, Set.coe_recessionConeCone] using
    (paraboloidVerticalRay_isExtreme_recessionCone (𝕜 := 𝕜))

/-- The vertical origin half-line is an exposed ray of the recession cone of the paraboloid
epigraph. -/
-- Proof sketch: once the recession cone is identified with the nonnegative vertical axis, the
-- functional projecting to the second coordinate exposes `originRay paraboloidVerticalRay`.
theorem paraboloidVerticalRay_isExposed_recessionCone :
    IsExposed 𝕜 (0⁺[𝕜] (paraboloidEpigraph : Set (𝕜 × 𝕜)))
      (originRay paraboloidVerticalRay) := sorry

/-- The vertical origin half-line is an exposed ray direction of the bundled recession-cone view
of the paraboloid epigraph. -/
theorem paraboloidVerticalRay_isExposedRay_recessionCone :
    (Set.recessionConeCone (paraboloidEpigraph : Set (𝕜 × 𝕜)) 𝕜).IsExposedRay
      paraboloidVerticalRay := by
  simpa [ConvexCone.IsExposedRay, Set.coe_recessionConeCone] using
    (paraboloidVerticalRay_isExposed_recessionCone (𝕜 := 𝕜))

/-- The vertical direction is not an extreme direction of the paraboloid epigraph. -/
-- Proof sketch: every supporting line to the parabola meets it in at most one boundary point, so
-- no affine half-line of vertical direction can be an extreme face of `paraboloidEpigraph`.
theorem paraboloidVerticalRay_notMem_extremeDirections :
    paraboloidVerticalRay ∉
      paraboloidEpigraph.extremeDirections 𝕜 := sorry

/-- The vertical direction is not an exposed direction of the paraboloid epigraph. -/
-- Proof sketch: an exposed affine half-line would be cut out by a supporting functional, but the
-- paraboloid epigraph has only point contacts with its supporting lines, never a vertical
-- half-line.
theorem paraboloidVerticalRay_notMem_exposedDirections :
    paraboloidVerticalRay ∉
      paraboloidEpigraph.exposedDirections 𝕜 := sorry

end
