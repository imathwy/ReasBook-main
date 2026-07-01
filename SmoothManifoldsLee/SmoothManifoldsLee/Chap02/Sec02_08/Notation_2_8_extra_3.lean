import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- Notation 2.8-extra-3: the textbook space `C^\infty(M)` of smooth real-valued functions on a
smooth manifold `M` is formalized by the bundled smooth-map type `C^∞⟮I, M; ℝ⟯`, with the smooth
structure recorded by the model with corners `I`. -/
#check (C^∞⟮I, M; ℝ⟯)

/- Smooth real-valued functions carry the canonical pointwise `ℝ`-module structure, so this Lean
type is the vector space of smooth real-valued functions on `M`. -/
#check (inferInstance : Module ℝ C^∞⟮I, M; ℝ⟯)
