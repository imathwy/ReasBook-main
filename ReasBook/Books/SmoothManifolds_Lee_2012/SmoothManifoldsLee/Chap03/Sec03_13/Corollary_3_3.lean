import Mathlib.LinearAlgebra.Basis.Defs
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_13.Proposition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold

-- Domain sampling pass: this item lies in the point-derivation/tangent-space API on `ℝ^n`.
-- Layer triage:
-- `source-facing`: the coordinate derivations and the resulting basis/dimension statement.
-- `core/canonical`: `directional_point_derivation` and
-- `geometric_to_point_derivation_linear_equiv` from Proposition 3.2.
-- `bridge/view`: the standard basis of `ℝ^n`, mapped across that linear equivalence.
-- Relevant declarations checked before refinement:
-- `directional_point_derivation`,
-- `geometric_to_point_derivation_linear_equiv`,
-- `Module.Basis.map`,
-- `LinearEquiv.finrank_eq`.
-- Primitive data is only the standard basis of `ℝ^n`; the coordinate-direction point derivations
-- are derived by applying the chapter owner equivalence to those basis vectors, so this file
-- should not keep a parallel local owner for that specialization.

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- Corollary 3.3 (1): for any `a ∈ ℝ^n`, the coordinate derivations
`∂/∂x¹|ₐ, …, ∂/∂xⁿ|ₐ` form a basis of `T_aℝ^n`. -/
noncomputable def coordinate_point_derivation_basis (a : R^n) :
    Module.Basis (Fin n) ℝ (PointDerivation I a) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
    (geometric_to_point_derivation_linear_equiv a)

/-- The `i`-th vector of `coordinate_point_derivation_basis a` is the derivation
`∂/∂xⁱ|ₐ`. -/
theorem coordinate_point_derivation_basis_apply (a : R^n) (i : Fin n) :
    coordinate_point_derivation_basis a i =
      directional_point_derivation a (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [coordinate_point_derivation_basis, Module.Basis.map_apply]
  exact geometric_to_point_derivation_linear_equiv_apply a _

/-- Corollary 3.3 (2): for any `a ∈ ℝ^n`, the tangent space `T_aℝ^n` has dimension `n`. -/
theorem point_derivation_finrank_eq (a : R^n) :
    Module.finrank ℝ (PointDerivation I a) = n := by
  calc
    Module.finrank ℝ (PointDerivation I a)
        = Module.finrank ℝ (geometric_tangent_space a) := by
            simpa using LinearEquiv.finrank_eq (geometric_to_point_derivation_linear_equiv a).symm
    _ = n := by
      simp [geometric_tangent_space]
