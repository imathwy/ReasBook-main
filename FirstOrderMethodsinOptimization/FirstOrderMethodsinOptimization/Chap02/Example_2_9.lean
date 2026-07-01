import FirstOrderMethodsinOptimization.Chap01.Proposition_1_9
import FirstOrderMethodsinOptimization.Chap01.Proposition_1_10
import FirstOrderMethodsinOptimization.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (toLp)

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: unfold `support_function` on the closed unit ball `{x | ‖x‖ ≤ 1}`. The chapter
-- owner dual norm `dualNorm` gives the upper bound via the dual-pairing inequality, and
-- `exists_dualNorm_eq_apply` provides a unit-ball point where the supremum is attained.
/-- Example 2.9 (1): the support function of the closed unit ball of a normed space is the dual
norm. -/
theorem support_function_unit_ball_eq_dualNorm (y : Module.Dual ℝ E) :
    support_function {x : E | ‖x‖ ≤ 1} y = (dualNorm y : EReal) := sorry

end

section

variable {n : ℕ} {p q : ENNReal}

-- Proof sketch: rewrite `support_function` by its defining `sSup` formula and identify it with the
-- upstream unit-ball supremum formula `unit_lp_pairing_sSup_eq_conjugate_lp_norm`.
/-- Example 2.9 (2): in `ℝ^n` with the `l_p` norm, the support function of the closed unit ball is
the conjugate `l_q` norm. -/
theorem support_function_lp_unit_ball_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : Fin n → ℝ) :
    support_function {x : Fin n → ℝ | ‖toLp p x‖ ≤ 1} (dotProductBilin ℝ ℝ y) =
      (‖toLp q y‖ : EReal) := sorry

-- Proof sketch: equip `ℝ^n` with the norm induced by the positive definite matrix `Q`, apply the
-- unit-ball support-function formula from part (1), and then identify the resulting owner dual norm
-- using `dual_qNorm_eq_sqrt_dotProduct_inv_mulVec`.
/-- Example 2.9 (3): for the norm induced by a positive definite matrix `Q`, the support function
of the closed unit ball is the `Q⁻¹`-norm, written here as `√(yᵀ Q⁻¹ y)`. -/
theorem support_function_posDef_unit_ball_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (y : Fin n → ℝ) :
    letI := Q.toNormedAddCommGroup hQ
    support_function {x : Fin n → ℝ | ‖x‖ ≤ 1} (dotProductBilin ℝ ℝ y) =
      (Real.sqrt (dotProduct y (Q⁻¹.mulVec y)) : EReal) := sorry

end
