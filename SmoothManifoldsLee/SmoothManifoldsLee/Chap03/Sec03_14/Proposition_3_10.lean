import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic

noncomputable section

open scoped Manifold

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Proposition 3.10 (Dimension of the Tangent Space). If `M` is an `n`-dimensional smooth
manifold, then for each `p ∈ M`, the tangent space `TangentSpace I p` is an `n`-dimensional real
vector space. -/
theorem tangentSpace_finrank_eq_of_n_dimensional_manifold (p : M) :
    Module.finrank ℝ (TangentSpace I p) = n := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
  exact finrank_euclideanSpace_fin
