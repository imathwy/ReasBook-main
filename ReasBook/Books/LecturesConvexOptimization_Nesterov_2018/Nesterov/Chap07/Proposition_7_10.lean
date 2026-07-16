import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_23
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Proposition_7_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators PositiveDefMatrixNorm WeightedGramMatrix

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.10 lies in the finite-family weighted-Gram / positive-definite dual-norm domain.

Relevant owners sampled before drafting:
- `weightedGramMatrix` and the notation `B[a](w)` in `Chap07/Proposition_7_9`;
- `positiveDefMatrixNorm` and the dual notation `‖·‖[G,*]` in `Chap07/Definition_7_23`;
- mathlib `Matrix.trace`, `Matrix.trace_mul_comm`, and `Matrix.trace_vecMulVec`.

The source-facing item is therefore stated directly on the existing weighted-Gram owner and the
existing Chapter 7 dual norm surface, with the displayed consequence split into atomic clauses.
-/

section WeightedTraceIdentity

variable (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m))
variable (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})

-- Proof sketch: substitute the weighted Gram representation
-- `(G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)` from Proposition 7.9 and multiply on
-- the left by `G⁻¹`; the left-hand side reduces to the identity matrix.
/-- Proposition 7.10 [Chapter7_1.json:56] (1): if the positive-definite matrix `G` is represented
as the weighted Gram matrix `B[a](weights.weights) = ∑ᵢ λᵢ aᵢ aᵢᵀ`, then the equivalent canonical
matrix identity `G⁻¹ B[a](weights.weights) = Iₙ` holds. -/
theorem inv_mul_weightedGramMatrix_eq_one
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * B[a](weights.weights) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

-- Proof sketch: take traces in `inv_mul_weightedGramMatrix_eq_one`, use `Matrix.trace_one`, expand
-- `B[a](weights.weights)`, commute traces cyclically, and identify each rank-one trace with
-- `‖a i‖[G,*]^2` via `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv`.
/-- Proposition 7.10 [Chapter7_1.json:56] (2): tracing the weighted Gram identity gives the exact
formula `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`. -/
theorem dim_eq_sum_weights_mul_dualNorm_sq
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    (n : ℝ) =
      ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ) := sorry

-- Proof sketch: start from the exact identity
-- `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`, bound every squared dual norm by `r^2`, and use the simplex
-- relation `∑ᵢ λᵢ = 1`.
/-- Proposition 7.10 [Chapter7_1.json:56] (3): if every generator satisfies `‖aᵢ‖[G,*] ≤ r`, then
the previous identity implies the estimate `(n : ℝ) ≤ r^2`. -/
theorem dim_le_sq_of_dualNorm_le
    (htrace :
      (n : ℝ) =
        ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ))
    {r : ℝ} (hr : ∀ i : Fin m, ‖a i‖[G,*] ≤ r) :
    (n : ℝ) ≤ r ^ (2 : ℕ) := sorry

end WeightedTraceIdentity

end
