import Mathlib.Geometry.Manifold.IsManifold.Basic

open TopologicalSpace
open scoped ContDiff

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {n : ℕ∞ω}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
variable (U : Opens M)

/- Example 1.26: any open subset of a `C^n` manifold inherits a natural `C^n` manifold
structure. In particular, every open subset of `ℝ^n` is a smooth `n`-manifold, and for an open
subset of the model space this agrees with the induced smooth structure coming from restricting the
ambient charts. -/
#check (inferInstance : IsManifold I n U)
