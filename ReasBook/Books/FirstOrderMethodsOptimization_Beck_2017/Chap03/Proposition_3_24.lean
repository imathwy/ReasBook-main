import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp ofLp)

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 3.24 is a `bridge/view` item for the Chapter 3 owner `subdifferentialAt`, and its
public vector-side owner is `euclideanSubdifferentialAt`. Proposition 3.23 already identifies the
coordinatewise-max Euclidean extendedRealSubdifferential with `activeCoordinateFace`; the only additional
source-facing content here is the signed active-coordinate description of the `ℓ∞`
extendedRealSubdifferential. The zero case is stated directly using the canonical `WithLp 1` unit ball on
`ℝ^n`, so no extra wrapper is introduced. -/

-- Proof sketch: on `Fin n → ℝ`, the ambient norm is the `ℓ∞` norm, so the objective is
-- `x ↦ ‖x‖ = max_i |x i|`. Apply the max rule to the family `x ↦ |x i|` and use Proposition 3.23
-- for the resulting active simplex face. At `x = 0`, every coordinate is active and the convex hull
-- of the signed coordinate vectors is exactly the canonical `WithLp 1` unit ball
-- `{z | ‖toLp 1 z‖ ≤ 1}`.
/-- Proposition 3.24: for `f(x) = ‖x‖∞ = ‖x‖` on `ℝ^n = Fin n → ℝ`, the Euclidean/vector-side
extendedRealSubdifferential is the `ℓ₁` unit ball `{z | ‖toLp 1 z‖ ≤ 1}` at the origin, and away from the
origin it is the set of convex
combinations `∑_{i ∈ I(x)} λ_i sign (x_i) e_i` supported on the active coordinates
`I(x) = {i | |x i| = ‖x‖∞}`. -/
theorem euclidean_subdifferentialAt_linf_eq_piecewise
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x =
      if x = 0 then
        {z : E | ‖toLp 1 (ofLp z)‖ ≤ 1}
      else
        (fun coeff : ι → ℝ ↦ toLp 2 fun i ↦ coeff i * Real.sign (x i)) ''
          activeCoordinateFace (fun i ↦ |x i|) := sorry

end
