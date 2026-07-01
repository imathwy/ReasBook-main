import Nesterov.Chap05.Definition_5_4_4_4
import Nesterov.Chap07.Definition_7_70
import Nesterov.Chap07.Definition_7_71

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.33 lies in Chapter 7's Boolean quadratic / semidefinite-relaxation domain.

Sampled owner-style declarations:
- `booleanQuadraticOptimalValue` in `Definition_7_70`, the chapter owner for the Boolean
  quadratic optimum;
- `diagonalSemidefiniteRelaxationOptimalValue` in `Definition_7_71`, the chapter owner for the
  semidefinite-relaxation value `ψ⋆` on the intrinsic symmetric carrier `𝕊^n`;
- `SemidefiniteOptimizationProblem` and `SemidefiniteOptimizationProblem.feasibleSet` in
  `Chap05/Definition_5_4_4_4`, the project owner for SDP data, the intrinsic feasible set in
  `𝕊^n`, and the trace/Frobenius objective;
- `𝕊^n` and `𝕊^n₊` in `Chap05/Definition_5_4_4_1` and `Chap05/Definition_5_4_4_3`, the
  intrinsic symmetric-matrix and positive-semidefinite cone owners.

Best owner abstraction:
- source-facing: Proposition 7.33's comparison between the Boolean quadratic optimum and the
  chapter semidefinite-relaxation value `ψ⋆`;
- core/canonical: `booleanQuadraticOptimalValue` and
  `diagonalSemidefiniteRelaxationOptimalValue`, both specialized to the intrinsic symmetric
  carrier `𝕊^n`;
- bridge/view: the unit-diagonal SDP representation of
  `diagonalSemidefiniteRelaxationOptimalValue`.

Primitive data:
- `A : 𝕊^n`.

Derived API:
- the chapter owner `diagonalSemidefiniteRelaxationOptimalValue A`;
- the private SDP view used to express its primal trace-maximization representation;
- the bridge theorem recovering the textbook `sSup` formula over unit-diagonal
  positive-semidefinite matrices.

Source/core/bridge triage:
- source-facing: the approximation theorem below;
- core/canonical: `booleanQuadraticOptimalValue` and
  `diagonalSemidefiniteRelaxationOptimalValue`;
- bridge/view: the unit-diagonal feasible-set characterization, the trace-form objective theorem,
  and the `sSup` expansion of `diagonalSemidefiniteRelaxationOptimalValue`.

This refinement deletes the duplicate public semidefinite-relaxation owners
`booleanQuadraticSemidefiniteProblem` and `booleanQuadraticSemidefiniteOptimalValue`. The public
surface now reuses the chapter owner `diagonalSemidefiniteRelaxationOptimalValue` on `𝕊^n`,
while any explicit SDP packaging remains private bridge data. The main approximation theorem is
therefore stated directly on the intrinsic cone owner `𝕊^n₊`, with only the Boolean quadratic
objective viewed through the ambient matrix coercion.
-/

private def diagonalSemidefiniteRelaxationConstraint
    (i : Fin n) : 𝕊^n :=
  ⟨Matrix.diagonal fun j : Fin n ↦ if j = i then (1 : ℝ) else 0, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simp [Matrix.IsSymm]
  ⟩

private def diagonalSemidefiniteRelaxationProblem
    (A : 𝕊^n) : SemidefiniteOptimizationProblem n n where
  costMatrix := A
  constraintMatrices := diagonalSemidefiniteRelaxationConstraint
  rhs := (EuclideanSpace.equiv (Fin n) ℝ).symm fun _ ↦ (1 : ℝ)

-- Proof sketch: unfold `diagonalSemidefiniteRelaxationProblem` and
-- `SemidefiniteOptimizationProblem.mem_feasibleSet_iff`; the constraint matrices are the
-- diagonal matrix units, so the Frobenius equations are exactly the unit-diagonal conditions on
-- `X`.
private theorem mem_diagonalSemidefiniteRelaxationProblem_feasibleSet_iff
    (A : 𝕊^n) (X : 𝕊^n) :
    X ∈ (diagonalSemidefiniteRelaxationProblem A).feasibleSet ↔
      X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1) := by
  sorry

-- Proof sketch: the SDP owner objective is the Frobenius pairing with the symmetric cost matrix
-- `A`; on `𝕊^n` this is exactly the textbook trace formula `trace (A X)`.
private theorem diagonalSemidefiniteRelaxationProblem_objective_eq_trace
    (A : 𝕊^n) (X : 𝕊^n) :
    (diagonalSemidefiniteRelaxationProblem A).objective X = trace ((A : Mₙ) * (X : Mₙ)) := by
  sorry

/-- The chapter semidefinite-relaxation value `ψ⋆` from Definition 7.71 admits the standard
unit-diagonal SDP representation as a trace supremum over positive-semidefinite symmetric
matrices. -/
theorem diagonalSemidefiniteRelaxationOptimalValue_eq_sSup_trace
    (A : 𝕊^n) :
    diagonalSemidefiniteRelaxationOptimalValue A =
      sSup ((fun X : 𝕊^n ↦ trace ((A : Mₙ) * (X : Mₙ))) ''
        {X : 𝕊^n | X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)}) := by
  sorry

-- Proof sketch: the upper bound comes from sending a sign vector `x ∈ {±1}ⁿ` to the feasible
-- rank-one symmetric matrix `x xᵀ`. The lower bound depends only on the intrinsic symmetric
-- positive-semidefinite coefficient matrix, so the source-facing proposition is stated directly
-- on the Chapter 7 relaxation owner `diagonalSemidefiniteRelaxationOptimalValue`.
/-- Proposition 7.33: for a positive-semidefinite symmetric matrix `A`, the Boolean quadratic
optimum `f⋆` from Definition 7.70 and the chapter semidefinite-relaxation value `ψ⋆` from
Definition 7.71 satisfy `(2 / π) ψ⋆ ≤ f⋆ ≤ ψ⋆`. -/
theorem booleanQuadraticOptimalValue_two_div_pi_mul_diagonalSemidefiniteRelaxation_le_and_le
    (A : 𝕊^n₊) :
    (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
        booleanQuadraticOptimalValue (A : Mₙ) ∧
      booleanQuadraticOptimalValue (A : Mₙ) ≤
        diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) := by
  sorry

end
