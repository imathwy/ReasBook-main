import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 2.3: the canonical finite-dimensional model `ℝ^N` is `EuclideanSpace ℝ (Fin N)`. -/
recall EuclideanSpace

/- Example 2.3: for a finite index set, the canonical mathlib identification of `ℓ²` with the
finite-coordinate `L²` space is `lpPiLpₗᵢ`; for `Fin N` over `ℝ`, its target is
`EuclideanSpace ℝ (Fin N)`. -/
recall lpPiLpₗᵢ

/-- Example 2.3: under the canonical identification
`ℓ²(Fin N, ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)`, an `ℓ²` vector and its Euclidean coordinate
function have the same entries. -/
theorem lpPiLpₗᵢ_fin_real_apply (N : ℕ) (x : ℓ²(Fin N, ℝ)) :
    ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ x : EuclideanSpace ℝ (Fin N)) : Fin N → ℝ) = x :=
  rfl

/-- The inverse of the canonical identification `ℓ²(Fin N, ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` is
also coordinatewise the identity. -/
theorem lpPiLpₗᵢ_fin_real_symm_apply (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    ((((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x : ℓ²(Fin N, ℝ)) : Fin N → ℝ)) = x :=
  rfl
