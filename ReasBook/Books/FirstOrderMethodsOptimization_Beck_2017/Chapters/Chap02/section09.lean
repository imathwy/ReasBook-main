import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_9 (from Chap02) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 2.9: the support function of a set `C ⊆ E` is the extended-real-valued function on
the dual space `E* = Module.Dual ℝ E` sending `y` to the supremum of the pairings `y x` for
`x ∈ C`. For nonempty `C`, this realizes the textbook codomain `(-∞, ∞]`. -/
noncomputable def support_function (C : Set E) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup ((fun x : E ↦ (y x : EReal)) '' C)

-- Proof sketch: unfold `support_function`; the statement is exactly the defining supremum formula
-- for the image of `C` under the pairing map `x ↦ y x`.
/-- Evaluating the support function at `y` gives the supremum of the dual pairings `y x` over
`x ∈ C`. -/
lemma support_function_apply (C : Set E) (y : Module.Dual ℝ E) :
    support_function C y = sSup ((fun x : E ↦ (y x : EReal)) '' C) :=
  rfl

-- Proof sketch: choose `x ∈ C`; then `(y x : EReal)` belongs to the image set whose supremum
-- defines `support_function C y`, so `⊥ < (y x : EReal) ≤ support_function C y`, ruling out
-- the value `⊥`.
/-- For a nonempty set `C`, the support function never takes the value `-∞`. -/
theorem support_function_ne_bot (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) :
    support_function C y ≠ ⊥ := sorry

-- Proof sketch: unfold `support_function`; the hypothesis says that the defining image set has
-- greatest element `a`, so its supremum is exactly `a`.
/-- If the pairing image `y '' C` has greatest element `a`, then the support function of `C` at
`y` is exactly `a`. -/
theorem support_function_eq_of_isGreatest_image (C : Set E) (y : Module.Dual ℝ E) {a : EReal}
    (hmax : IsGreatest ((fun x : E ↦ (y x : EReal)) '' C) a) :
    support_function C y = a := by
  rw [support_function_apply]
  exact hmax.csSup_eq

end

/-! ### Example_2_9 (from Chap02) -/
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

/-! ### Theorem_2_9 (from Chap02) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use the interior assumption to choose a closed ball contained in
-- `effective_domain f`. The hypothesis `h_ne_bot` supplies the exact codomain restriction needed
-- for the chapter bridge `convexOn_toReal_of_is_convex_function`, so that `x ↦ (f x).toReal` is a
-- genuine real-valued convex function on `effective_domain f`. Apply the finite-dimensional theorem
-- that convex functions are locally Lipschitz on the interior of their domain, then shrink to a
-- closed ball and rewrite the resulting Lipschitz estimate as the displayed bound at `x0`.
/-- Theorem 2.9: a convex extended-real-valued function is locally Lipschitz at every point of the
interior of its effective domain, in the sense that some closed ball around the point is contained
in the domain and satisfies the estimate `|(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖`. -/
theorem convex_function_exists_closedBall_lipschitz_bound_at_interior_point
    {f : E → EReal} (hf : is_convex_function f)
    (h_ne_bot : ∀ x, f x ≠ ⊥) {x0 : E} (hx0 : x0 ∈ interior (effective_domain f)) :
    ∃ ε > 0, ∃ L > 0,
      Metric.closedBall x0 ε ⊆ effective_domain f ∧
        ∀ x ∈ Metric.closedBall x0 ε,
          |(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖ := sorry

end
