import Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_26
import Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9
import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_1
import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_4

open scoped BigOperators Matrix

-- Semantic recall note: `lean_leansearch` did not surface a project-specific existing owner for
-- Lovasz basis reduction, so this file uses the local fixed-dimension owner
-- `LovaszBasisReductionAlgorithm` together with the Chapter 7 global-query solver abstraction
-- `LovaszBasisReductionSolver` for the source-facing theorem surface.

noncomputable section Theorem96

open InnerProductSpace Module

/-- A rational basis input for `ℝ^n`, encoded by the nonsingular square matrix whose columns are
the basis vectors in the standard coordinates. -/
structure RationalBasis (n : ℕ) where
  basisMatrix : Matrix (Fin n) (Fin n) ℚ
  nonsingular : IsUnit basisMatrix.det

namespace RationalBasis

/-- The Euclidean basis whose columns are the rational basis matrix encoded by `B`. -/
noncomputable def basis {n : ℕ} (B : RationalBasis n) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  euclideanBasisOfMatrix (B.basisMatrix.map (Rat.castHom ℝ)) <| by
    refine isUnit_iff_ne_zero.mpr ?_
    intro hzero
    apply B.nonsingular.ne_zero
    have hcast : (B.basisMatrix.det : ℝ) = 0 := by
      calc
        (B.basisMatrix.det : ℝ) = (B.basisMatrix.map (Rat.castHom ℝ)).det := by
          simpa using (Rat.cast_det B.basisMatrix)
        _ = 0 := hzero
    exact_mod_cast hcast

/-- The encoding size of a rational basis is the canonical matrix encoding size of its coordinate
matrix. -/
def encodingSize {n : ℕ} (B : RationalBasis n) : ℕ :=
  rational_matrix_encoding_size B.basisMatrix

/-- `B.encodingSize` is the canonical matrix encoding size of `B.basisMatrix`. -/
theorem encodingSize_eq {n : ℕ} (B : RationalBasis n) :
    B.encodingSize = rational_matrix_encoding_size B.basisMatrix :=
  rfl

/-- Expanding `B.encodingSize` gives the coordinatewise encoding-size sum. -/
theorem encodingSize_eq_sum {n : ℕ} (B : RationalBasis n) :
    B.encodingSize = ∑ i, ∑ j, rational_encoding_size (B.basisMatrix i j) := by
  simp [encodingSize, rational_matrix_encoding_size, rational_vector_encoding_size]

end RationalBasis

/-- A Lovász basis reduction algorithm on rational bases of `ℝ^n` produces a run of the basis
reduction procedure on successive bases, together with an explicit termination index and a
polynomial bit-operation bound in the encoding size of the original basis. -/
structure LovaszBasisReductionAlgorithm (n : ℕ) where
  basisAt : RationalBasis n → ℕ → Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))
  terminationIndex : (B : RationalBasis n) → ℕ
  bitOperationCount : (B : RationalBasis n) → ℕ
  starts_from_input :
    ∀ B : RationalBasis n, basisAt B 0 = B.basis
  size_reduction :
    ∀ (B : RationalBasis n) (t : ℕ), 0 < t → basis_reduction_condition_i (basisAt B t)
  termination_condition_i :
    ∀ B : RationalBasis n, basis_reduction_condition_i (basisAt B (terminationIndex B))
  termination_condition_ii :
    ∀ B : RationalBasis n, basis_reduction_condition_ii (basisAt B (terminationIndex B))
  polynomial_iteration_bound :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        terminationIndex B ≤ p.eval B.encodingSize
  polynomial_bit_bound :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        bitOperationCount B ≤ p.eval B.encodingSize

/-- A Lovász basis reduction algorithm terminates on every rational input basis. -/
theorem LovaszBasisReductionAlgorithm.terminates_on
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) (B : RationalBasis n) :
    ∃ t : ℕ, IsReducedBasis (A.basisAt B t) :=
  ⟨A.terminationIndex B,
    basis_reduction_algorithm_terminates_with_reduced_basis
      (A.termination_condition_i B) (A.termination_condition_ii B)⟩

/-- A Lovász basis reduction algorithm has a polynomial bound on its number of iterations in the
encoding size of the original basis. -/
theorem LovaszBasisReductionAlgorithm.iteration_count_polynomially_bounded
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        A.terminationIndex B ≤ p.eval B.encodingSize := sorry

/-- A Lovász basis reduction algorithm has a polynomial bound on its bit-operation count in the
encoding size of the original basis. -/
theorem LovaszBasisReductionAlgorithm.bit_operation_count_polynomially_bounded
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        A.bitOperationCount B ≤ p.eval B.encodingSize := sorry

/-- The basis output by a Lovász basis reduction algorithm at its termination index is reduced. -/
theorem LovaszBasisReductionAlgorithm.reducedBasisAtTermination
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) (B : RationalBasis n) :
    IsReducedBasis (A.basisAt B (A.terminationIndex B)) :=
  basis_reduction_algorithm_terminates_with_reduced_basis
    (A.termination_condition_i B) (A.termination_condition_ii B)

/-- A uniform Lovász-reduction query consists of the original rational basis together with its
dimension. -/
abbrev LovaszBasisReductionQuery := Σ n : ℕ, RationalBasis n

namespace LovaszBasisReductionQuery

/-- The input size of a Lovász-reduction query is the encoding size of the original rational
basis. -/
def encodingSize (query : LovaszBasisReductionQuery) : ℕ :=
  query.2.encodingSize

end LovaszBasisReductionQuery

/-- A Lovász basis reduction certificate for an input basis consists of a reduced output basis for
the same lattice in the corresponding Euclidean space. -/
structure LovaszBasisReductionCertificate
    (query : LovaszBasisReductionQuery) where
  outputBasis : Basis (Fin query.1) ℝ (EuclideanSpace ℝ (Fin query.1))
  sameLattice :
    (EuclideanSpace.equiv (Fin query.1) ℝ).symm ''
        matrix_generated_lattice (query.2.basisMatrix.map (Rat.castHom ℝ)) =
      Submodule.span ℤ (Set.range outputBasis)
  isReduced : IsReducedBasis outputBasis

/-- A polynomial-time Lovász basis reduction solver is a Chapter 7 query solver on the global
input type of rational bases. -/
abbrev LovaszBasisReductionSolver :=
  PolynomialTimeQuerySolver
    LovaszBasisReductionQuery
    LovaszBasisReductionCertificate
    LovaszBasisReductionQuery.encodingSize

/-- Theorem 9.6. Lovász' basis reduction algorithm terminates, and it runs in polynomial time in
the input size of the original basis. -/
theorem lovasz_basis_reduction_has_polynomial_time_algorithm :
    Nonempty LovaszBasisReductionSolver := sorry

end Theorem96
