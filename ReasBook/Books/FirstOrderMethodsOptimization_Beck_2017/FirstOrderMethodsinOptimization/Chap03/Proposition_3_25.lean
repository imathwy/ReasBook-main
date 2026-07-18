import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_23

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

section

variable {m n : ℕ}

/- Proposition 3.25 is `source-facing` in the Chapter 3 finite-max extendedRealSubdifferential calculus. Its
core owners are already upstream: Proposition 3.23 supplies the max/active-face data
`coordinatewiseMax` and `activeCoordinateFace`, and the canonical dual bridge
`(dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap`. The only primitive data here
are the affine slopes `a` and offsets `b`, so the proposition is stated directly for the
max-affine objective instead of introducing a parallel wrapper for that function. -/

-- Proof sketch: apply the finite max rule for subdifferentials to the affine family
-- `x ↦ a i ⬝ᵥ x + b i`. Each affine function has singleton owner extendedRealSubdifferential given,
-- under `(dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap`, by the slope vector
-- `a i`.
-- The owner extendedRealSubdifferential of the maximum is therefore the image of the chapter-owned active face
-- `activeCoordinateFace (fun i ↦ a i ⬝ᵥ x + b i)` under the barycentric slope map
-- `λ ↦ ∑ i, λ i • a i`, transported to the continuous dual.
/-- Proposition 3.25: for the piecewise linear function
`x ↦ max_i (a_i^T x + b_i)` on `ℝ^n`, the owner extendedRealSubdifferential `subdifferentialAt` at `x`
is the image of the active face of the standard simplex under the map sending a simplex coefficient
vector to the corresponding convex combination of the active slope vectors `a_i`, viewed in the
continuous dual through the canonical bridge
`(dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap`. -/
theorem subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace
    (hm : 0 < m) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    subdifferentialAt (fun y ↦ coordinatewiseMax (fun i ↦ a i ⬝ᵥ y + b i)) x =
      (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) ∘
        fun coeff : Fin m → ℝ ↦ ∑ i, coeff i • a i) ''
        activeCoordinateFace (fun i ↦ a i ⬝ᵥ x + b i) := sorry

end
