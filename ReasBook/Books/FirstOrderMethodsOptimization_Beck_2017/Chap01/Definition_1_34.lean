import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp

section

variable {m n : ℕ}
variable (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
variable (A : Matrix (Fin m) (Fin n) ℝ)

/- Definition 1.34 is recall-only: the induced `(a,b)`-norm of a real matrix is the canonical
operator norm of the continuous linear map associated to the owner object `Matrix.toLpLin a b`. -/
#check (‖(A.toLpLin a b).toContinuousLinearMap‖ : ℝ)

/-- The induced matrix norm bounds `‖A *ᵥ x‖_b` for every vector in the closed unit ball of the
domain `a`-norm. -/
theorem norm_mulVec_le_opNorm_toLpLin (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    (A : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : ‖toLp a x‖ ≤ 1) :
    ‖toLp b (Matrix.mulVec A x)‖ ≤ ‖(A.toLpLin a b).toContinuousLinearMap‖ := by
  simpa [Matrix.toLpLin_toLp] using (A.toLpLin a b).toContinuousLinearMap.unit_le_opNorm (toLp a x) hx

-- Proof sketch: the closed unit ball in `WithLp a (Fin n → ℝ)` is compact, the map induced by
-- `A.toLpLin a b` is continuous, and a continuous real-valued function on a compact set attains
-- its maximum. Translating through `WithLp.toLp` gives the coordinate-vector statement below.
/-- A vector in the closed unit ball realizes the induced matrix norm, matching the textbook
maximum formula for the `(a,b)`-norm. -/
theorem exists_norm_le_one_eq_opNorm_toLpLin (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ x : Fin n → ℝ, ‖toLp a x‖ ≤ 1 ∧ ‖(A.toLpLin a b).toContinuousLinearMap‖ = ‖toLp b (Matrix.mulVec A x)‖ :=
  sorry

end
