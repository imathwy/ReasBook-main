import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap01.Definition_1_27
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_17

-- Declarations for this item will be appended below by the statement pipeline.

section

open WithLp (toLp)

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.18 is a `bridge/view` corollary in the chapter Euclidean extendedRealSubdifferential API.
Its source-facing coordinate description is already owned upstream by
`l1CoordinateSubgradientVectors`, together with the derived API
`sign_vector_mem_l1CoordinateSubgradientVectors`. The present item only transports that canonical
member through Proposition 3.17's owner-set identification
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. -/

-- Proof sketch: rewrite the target extendedRealSubdifferential through Proposition 3.17 and then use the
-- upstream owner-view lemma `sign_vector_mem_l1CoordinateSubgradientVectors`.
/-- Proposition 3.18: for `f(x) = ∑ i, |x i|` on `ℝ^n`, the coordinatewise sign vector `sgn(x)`
viewed in the dual via the Euclidean identification belongs to the extendedRealSubdifferential `∂ f(x)`. -/
theorem sign_vector_mem_subdifferentialAt_l1_norm
    (x : E) :
    toLp 2 (sgn x) ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖) x := by
  simpa [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints] using
    sign_vector_mem_l1CoordinateSubgradientVectors x

end
