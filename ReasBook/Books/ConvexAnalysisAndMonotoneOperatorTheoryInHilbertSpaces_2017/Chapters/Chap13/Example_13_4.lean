import Mathlib
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 13 4: completing the square rewrites the affine-quadratic defect into the
Moreau-envelope quadratic centered at `γ • u`. -/
private theorem scaled_quadratic_sub_shifted_kernel
    (γ : Set.Ioi (0 : ℝ)) (u x : H) :
    ⟪x, u⟫_ℝ - ((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) =
      (((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) -
        ((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ) := by
  -- Expand the shifted square and simplify the scalar and inner-product terms.
  have hnorm :
      ‖((γ : ℝ) • u - x)‖ ^ 2 =
        ‖((γ : ℝ) • u)‖ ^ 2 - 2 * ⟪((γ : ℝ) • u), x⟫_ℝ + ‖x‖ ^ 2 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_sub_sq_real ((γ : ℝ) • u) x
  have hsmul_norm :
      ‖((γ : ℝ) • u)‖ ^ 2 = ((γ : ℝ) ^ 2) * ‖u‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg γ.2.le]
    ring
  have hinner :
      ⟪((γ : ℝ) • u), x⟫_ℝ = (γ : ℝ) * ⟪x, u⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_comm]
  have hshift :
      ((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ) =
        (((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) - ⟪x, u⟫_ℝ +
          ((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) := by
    have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    rw [hnorm, hsmul_norm, hinner]
    field_simp [hγ0]
  linarith

/-- Helper for Example 13 4: subtracting the same finite scalar from the completed-square
identity preserves the affine-quadratic rewrite. -/
private theorem scaled_quadratic_sub_shifted_kernel_sub_real
    (γ : Set.Ioi (0 : ℝ)) (u x : H) (a : ℝ) :
    ⟪x, u⟫_ℝ - (a + ((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ)) =
      (((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) -
        (a + ((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ)) := by
  linarith [scaled_quadratic_sub_shifted_kernel γ u x]

/-- Helper for Example 13 4: the pointwise affine defects in the conjugate formula agree after
completing the square in the quadratic regularization term. -/
private theorem regularized_conjugate_integrand_eq_completed_square
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) (u x : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) -
        ((φ x : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal))) =
      ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) -
        ((φ x : EReal) +
          ((((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ) : EReal)))) := by
  by_cases hφ_top : (φ x : EReal) = ⊤
  · -- If `φ x = ⊤`, both affine defects are `⊥`.
    have hleft_top :
        (φ x : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal)) = ⊤ := by
      rw [hφ_top]
      exact EReal.top_add_coe (((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ))
    have hright_top :
        (φ x : EReal) +
            ((((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ) : EReal)) = ⊤ := by
      rw [hφ_top]
      exact EReal.top_add_coe
        (((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ))
    rw [hleft_top, hright_top]
    simp
  · -- Otherwise `φ x` is finite, so convert the whole identity to a real equality.
    have hφ_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (φ x).2
    have hreal :
        ⟪x, u⟫_ℝ - (((φ x : EReal)).toReal + ((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ)) =
          (((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) -
            (((φ x : EReal)).toReal +
              ((1 / (2 * (γ : ℝ))) * ‖((γ : ℝ) • u - x)‖ ^ 2 : ℝ)) :=
      scaled_quadratic_sub_shifted_kernel_sub_real γ u x ((φ x : EReal).toReal)
    rw [← EReal.coe_toReal hφ_top hφ_bot, ← EReal.coe_add, ← EReal.coe_add,
      ← EReal.coe_sub, ← EReal.coe_sub]
    -- Transport the real-valued completed-square identity through the `EReal` coercion.
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

-- Proof sketch: expand the Fenchel-conjugate value of
-- `x ↦ φ x + ‖x‖² / (2γ)` at `u`, complete the square in the quadratic term, and recognize the
-- remaining infimum as the `γ`-Moreau envelope of `φ` evaluated at `γ • u`.
/-- Example 13 4: for `φ : H → ]-∞,+∞]` and `γ ∈ ℝ_{++}`, the Fenchel conjugate of the
regularized function `x ↦ φ x + ‖x‖² / (2γ)` is
`u ↦ γ‖u‖² / 2 - {}^γφ(γu)`. -/
theorem conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) :
    ((φ + moreauQuadraticKernel γ).asEReal)∗ =
      fun u : H ↦ ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - ({}^[γ] φ) ((γ : ℝ) • u) := by
  funext u
  -- Rewrite both sides as extremal formulas over the same index set.
  rw [conjugate_apply, moreauEnvelope_apply]
  simp only [Function.asEReal_apply, add_apply, moreauQuadraticKernel_apply]
  -- Rewrite the Moreau-envelope infimum into a supremum of the completed-square defects.
  rw [ereal_realCast_sub_iInf_eq_iSup_sub]
  -- Match the two indexed families pointwise by the completed-square identity.
  refine iSup_congr fun x ↦ ?_
  exact regularized_conjugate_integrand_eq_completed_square φ γ u x

/-- Evaluating the Example 13.4 function identity at `u` yields the textbook pointwise formula
`(φ + ‖·‖² / (2γ))^*(u) = γ‖u‖² / 2 - {}^γφ(γu)`. -/
theorem conjugate_regularized_value_eq_scaledQuadratic_sub_moreauEnvelope
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    (((φ + moreauQuadraticKernel γ).asEReal)∗) u =
      ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - ({}^[γ] φ) ((γ : ℝ) • u) := by
  simpa using congrFun
    (conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope φ γ) u

end ERealFunction
