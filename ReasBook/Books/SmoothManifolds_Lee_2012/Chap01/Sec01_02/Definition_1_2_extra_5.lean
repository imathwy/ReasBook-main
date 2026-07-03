import Mathlib.Geometry.Manifold.IsManifold.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}

/- Definition 1.2-extra-5: in mathlib, a smooth manifold modeled on `I` is expressed by the
typeclass `IsManifold I ∞ M`; the corresponding smooth structure is the maximal
smooth atlas `IsManifold.maximalAtlas I ∞ M`, so one usually suppresses the atlas from the
notation once it is fixed. -/
#check (IsManifold I ∞ M)

-- Proof sketch: unfold `IsManifold.maximalAtlas`; for regularity `∞` it is definitionally the
-- maximal atlas of the smooth structure groupoid `contDiffGroupoid ∞ I`.
/-- Definition 1.2-extra-5: a smooth manifold carries the maximal smooth atlas determined by its
smooth structure. -/
theorem smooth_manifold_smooth_structure [IsManifold I ∞ M] :
    IsManifold.maximalAtlas I ∞ M = (contDiffGroupoid ∞ I).maximalAtlas M := sorry
