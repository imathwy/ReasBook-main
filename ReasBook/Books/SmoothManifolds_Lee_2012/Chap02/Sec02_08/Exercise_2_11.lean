import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {c : N} {U : Opens M}

/- Exercise 2.11 (1): part (a) of the preceding proposition is the canonical smoothness theorem
for constant maps between smooth manifolds. -/
recall contMDiff_const

/- Exercise 2.11 (2): part (b) of the preceding proposition is the canonical smoothness theorem
for the identity map of a smooth manifold. -/
recall contMDiff_id

/- Exercise 2.11 (3): part (c) of the preceding proposition is the canonical smoothness theorem
for the inclusion of an open submanifold `U : Opens M` into `M`. -/
recall contMDiff_subtype_val
