import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uH uH' uM uN

variable {m n : ℕ} {r : ℕ∞ω}
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
variable {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

namespace Diffeomorph

/-- A `C^r` diffeomorphism with `r ≠ 0` between nonempty manifolds modeled on `ℝ^m` and `ℝ^n`
forces the model dimensions to agree. The smooth case is the specialization `r = ∞`. -/
theorem dimension_eq (Φ : M ≃ₘ^r⟮I, J⟯ N) (hr : r ≠ 0) (hM : Nonempty M) : m = n := by
  rcases hM with ⟨p⟩
  have hm : Module.finrank ℝ (TangentSpace I p) = m := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
    exact finrank_euclideanSpace_fin
  have hn : Module.finrank ℝ (TangentSpace J (Φ p)) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  have hfin :
      Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ (TangentSpace J (Φ p)) :=
    (Φ.mfderivToContinuousLinearEquiv hr p).toLinearEquiv.finrank_eq
  calc
    m = Module.finrank ℝ (TangentSpace I p) := hm.symm
    _ = Module.finrank ℝ (TangentSpace J (Φ p)) := hfin
    _ = n := hn

end Diffeomorph

/-- Theorem 2.17 (Diffeomorphism Invariance of Dimension). A nonempty smooth manifold of dimension
`m` cannot be diffeomorphic to an `n`-dimensional smooth manifold unless `m = n`. More generally,
the same conclusion holds for any `C^r` diffeomorphism with `r ≠ 0`. -/
theorem diffeomorphic_dimension_eq (hr : r ≠ 0) (hM : Nonempty M)
    (h : Nonempty (M ≃ₘ^r⟮I, J⟯ N)) : m = n :=
  Diffeomorph.dimension_eq h.some hr hM
