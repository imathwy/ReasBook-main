import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)}

/- Definition 2.8-extra-2: a smooth function from a smooth manifold, with or without boundary, to
`ℝ^k` is formalized by the canonical manifold smoothness predicate
`ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ f`, written on the public surface as `CMDiff ∞ f`;
the boundary case is encoded by the model with corners `I`. -/
#check (CMDiff ∞ f)
