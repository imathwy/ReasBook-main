import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch` tool was available in this run, so the coordinate
-- API was verified directly against mathlib's `LinearMap.toMatrix` and `LinearMap.toMatrix_apply`.

noncomputable section

open scoped Manifold

universe u v

variable {V : Type u} {W : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The real dimension of the space of continuous linear maps from `V` to `W` is the product of
the dimensions of `V` and `W`. -/
theorem finrank_continuousLinearMap_eq_mul
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] :
    Module.finrank ℝ (V →L[ℝ] W) = Module.finrank ℝ V * Module.finrank ℝ W := by
  calc
    Module.finrank ℝ (V →L[ℝ] W) = Module.finrank ℝ (V →ₗ[ℝ] W) :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] W) ≃ₗ[ℝ] V →L[ℝ] W).symm.finrank_eq
    _ = Module.finrank ℝ V * Module.finrank ℝ W := by
      simpa using Module.finrank_linearMap ℝ ℝ V W

/- Example 1.29 (1): because every linear map from the finite-dimensional real vector space `V`
to `W` is continuous, the space of linear maps is identified with the finite-dimensional real
vector space `V →L[ℝ] W`, which therefore carries its canonical smooth manifold structure. -/
#check (inferInstance : IsManifold 𝓘(ℝ, V →L[ℝ] W) ⊤ (V →L[ℝ] W))

variable
    (bV : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (bW : Module.Basis (Fin (Module.finrank ℝ W)) ℝ W)

variable [FiniteDimensional ℝ V] in
/- Example 1.29 (2): choosing ordered bases of `V` and `W` gives global coordinates on the space
of continuous linear maps by composing the canonical finite-dimensional identification
`(V →L[ℝ] W) ≃ₗ[ℝ] (V →ₗ[ℝ] W)` with `LinearMap.toMatrix`. -/
#check
  ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] W) ≃ₗ[ℝ] V →L[ℝ] W).symm.trans
    (LinearMap.toMatrix bV bW) :
      (V →L[ℝ] W) ≃ₗ[ℝ]
        Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ V)) ℝ)

/-- In the bases `bV` and `bW`, the coordinates of a continuous linear map are the entries of its
matrix. -/
theorem continuousLinearMap_toMatrix_apply
    (T : V →L[ℝ] W) (i : Fin (Module.finrank ℝ W)) (j : Fin (Module.finrank ℝ V)) :
    LinearMap.toMatrix bV bW T.toLinearMap i j = bW.repr (T (bV j)) i := by
  simpa using LinearMap.toMatrix_apply bV bW T.toLinearMap i j
