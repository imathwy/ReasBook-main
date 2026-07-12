import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [BoundarylessManifold I M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I' : ModelWithCorners 𝕜 E' H'}

/-- Problem 4-2: a map that is smooth at `p` from a boundaryless smooth manifold cannot send a
point with surjective manifold derivative to a boundary point of the target manifold. -/
theorem mdifferentiableAt_map_mem_interior_of_surjective_mfderiv
    {F : M → N} {p : M} (hF : MDifferentiableAt I I' F p)
    (hFp : Function.Surjective (mfderiv I I' F p)) :
    I'.IsInteriorPoint (F p) := by
  exact hF.isInteriorPoint_of_surjective_mfderiv hFp BoundarylessManifold.isInteriorPoint

/-- Problem 4-2 in the source phrasing: a map that is smooth at `p` from a boundaryless smooth
manifold cannot send a point with nonsingular differential to a boundary point of the target
manifold. -/
theorem contMDiffAt_map_mem_interior_of_nonsingular_mfderiv
    {F : M → N} {p : M} (hF : ContMDiffAt I I' ∞ F p)
    (hFp : (mfderiv I I' F p).IsInvertible) :
    I'.IsInteriorPoint (F p) :=
  mdifferentiableAt_map_mem_interior_of_surjective_mfderiv
    (hF.mdifferentiableAt (by simp)) hFp.surjective
