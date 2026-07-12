import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff

universe uE uH uM uE' uH' uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N]
variable {F : M → N}

/- Definition 2.8-extra-5: a smooth map between smooth manifolds, including manifolds with
boundary via the models with corners `I` and `I'`, is formalized by the canonical manifold
smoothness predicate `ContMDiff I I' ∞ F`. -/
recall ContMDiff
