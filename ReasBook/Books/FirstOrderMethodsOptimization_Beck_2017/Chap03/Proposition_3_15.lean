import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open Metric

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 3.15 is `source-facing`: the book states the Euclidean subdifferential as a subset of
`ℝ^n`, so the main declaration should use the chapter Euclidean bridge/view owner
`euclideanSubdifferentialAt`. The continuous-dual owner `subdifferentialAt` remains upstream in
Theorem 3.4 and should only appear through derived bridge lemmas, not as the main public surface
of this proposition.
-/

-- Proof sketch: for `x = 0`, this is Proposition 3.1 specialized to Euclidean space. For
-- `x ≠ 0`, the Euclidean norm is differentiable at `x`, so Theorem 3.13 identifies the owner
-- dual subdifferential with the Riesz functional of the normalized vector, and transporting back
-- along `toDualMap` gives the vector-side singleton `{(‖x‖⁻¹) • x}`.
/-- Proposition 3.15: for the Euclidean norm on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing the normalized vector `(1 / ‖x‖) • x` away from the
origin, and it is the closed Euclidean unit ball at the origin. -/
theorem euclidean_subdifferentialAt_l2_norm_eq_piecewise (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) x =
      if x = 0 then
        closedBall (0 : E) 1
      else
        {((‖x‖⁻¹ : ℝ) • x)} := sorry

end
