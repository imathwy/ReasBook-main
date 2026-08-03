import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: fixed-dimension integer feasibility for rational polyhedra
-- * sampled owner declarations: Chapter 9.1.2 `rational_linear_system_encoding_size`,
--   `rational_matrix_polyhedron`, and `IntegralPointCertificate`, together with Chapter 9.1.3's
--   box-reduction owner `PolynomiallyBoundedBoxReduction`
-- * owner abstraction: a witness-producing run map returning an `IntegralPointCertificate` for the
--   canonical polyhedron owner `rational_matrix_polyhedron A b`
-- * primitive data: run map, running-time function, completeness on integral-point inputs
-- * derived API: soundness of returned outputs from the certificate type itself

section Exercise910

variable {m n : ℕ}

/-- A witness-producing algorithm for fixed-dimension integral feasibility returns an explicit
integral-point certificate for the rational polyhedron `rational_matrix_polyhedron A b` whenever
that polyhedron contains an integral point, and it runs in time polynomial in the encoding size of
the input system. -/
structure IntegralFeasibilityAlgorithm (n : ℕ) where
  run {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      Option (IntegralPointCertificate (rational_matrix_polyhedron A b))
  runTime {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      ℕ
  complete {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (hP : _root_.contains_integral_point (rational_matrix_polyhedron A b)) :
      ∃ point : IntegralPointCertificate (rational_matrix_polyhedron A b),
        run A b = some point
  polynomial_time :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        runTime A b ≤ p.eval (rational_linear_system_encoding_size A b)

namespace IntegralFeasibilityAlgorithm

/-- A witness-producing integral-feasibility algorithm satisfies its explicit polynomial
running-time bound, uniformly in the number of inequalities. -/
theorem runTime_le
    (algorithm : IntegralFeasibilityAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ p.eval (rational_linear_system_encoding_size A b) :=
  algorithm.polynomial_time

/-- If the input rational polyhedron contains an integral point, then a witness-producing
integral-feasibility algorithm returns an explicit integral-point certificate. -/
theorem output_spec
    (algorithm : IntegralFeasibilityAlgorithm n)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hP : _root_.contains_integral_point (rational_matrix_polyhedron A b)) :
    ∃ point : IntegralPointCertificate (rational_matrix_polyhedron A b),
      algorithm.run A b = some point :=
  algorithm.complete A b hP

/-- An explicit integral-point certificate witnesses that the input rational polyhedron contains
an integral point. -/
theorem certificate_spec
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (point : IntegralPointCertificate (rational_matrix_polyhedron A b)) :
    _root_.contains_integral_point (rational_matrix_polyhedron A b) := by
  exact point.contains_integral_point

end IntegralFeasibilityAlgorithm

/-- Exercise 9.10. For each fixed dimension `n`, Lenstra's algorithm can be modified so that,
given a rational system `A x ≤ b`, it computes an integral solution whenever one exists; the
modified algorithm still runs in time polynomial in the encoding size of `(A, b)`. -/
theorem lenstra_algorithm_computes_integral_solution
    (n : ℕ) :
    Nonempty (IntegralFeasibilityAlgorithm n) := sorry

end Exercise910
