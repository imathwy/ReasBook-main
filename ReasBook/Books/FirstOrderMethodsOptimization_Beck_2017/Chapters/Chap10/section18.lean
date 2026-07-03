

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_18 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

local notation "F" => composite_model_objective f g

/- Corollary 10.18 is `bridge/view` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `gradient_mapping` from Definition 10.5 is the owner of the residual `G_L`;
- `proximal_gradient_backtracking_B2_accepts` from Algorithm 10.3 is the chapter owner of the
  local quadratic upper-model test at a base point `x`;
- the Chapter 10 one-step prox-gradient gap estimate from Theorem 10.16 is the owner descent
  statement for the same local model.

The primitive source data here are:
- the accepted local upper-model inequality, reused through the existing B2 acceptance owner.

The displayed residual estimate is derived API: specialize the owner gap estimate to `y = x`,
then rewrite the remaining quadratic term through `G[L, f, g] x`.
-/

-- Proof sketch: specialize `fundamental_prox_grad_inequality` to the base point `y = x`. The
-- hypothesis is supplied by the owner predicate `proximal_gradient_backtracking_B2_accepts`. The
-- second quadratic term and the linearization defect then vanish at `y = x`, and the surviving
-- quadratic term is exactly `(1 / (2L)) ‖G_L(x)‖²` after rewriting with `gradient_mapping_apply`.
/-- Helper for Corollary 10.18: once `f(x)` is known not to be `⊥`, the first-order
linearization defect vanishes on the diagonal. -/
lemma prox_gradient_linearization_defect_self_of_ne_bot
    (x : interior (effective_domain f)) (hfx_ne_bot : f (x : E) ≠ ⊥) :
    ℓ[f, (x : E), x] = 0 := by
  -- On the diagonal, the displacement term is zero, and the remaining self-subtraction is
  -- legitimate because `x ∈ effective_domain f` rules out `⊤` while `hfx_ne_bot` rules out `⊥`.
  have hfx_ne_top : f (x : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset x.2)).ne
  calc
    ℓ[f, (x : E), x] =
        f (x : E) - f (x : E) -
          (inner ℝ (∇ (fun z ↦ (f z).toReal) (x : E)) ((x : E) - (x : E)) : EReal) := by
      rw [prox_gradient_linearization_defect_eq]
    _ = f (x : E) - f (x : E) := by
      simp
    _ = 0 := by
      exact EReal.sub_self hfx_ne_top hfx_ne_bot

/-- Helper for Corollary 10.18: specializing the fundamental prox-gradient inequality at the
base point `x` leaves only the quadratic step-gap term once `f(x)` is known not to be `⊥`. -/
lemma prox_grad_gap_at_basepoint_of_ne_bot
    (L : PosReal) (x : interior (effective_domain f))
    (hupper : proximal_gradient_backtracking_B2_accepts f g L x)
    (hfx_ne_bot : f (x : E) ≠ ⊥) :
    F (x : E) - F (T[L, f, g] x) ≥
      ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Specializing `fundamental_prox_grad_inequality` with `y = x` produces the source-proof
  -- decomposition; the diagonal quadratic term and linearization defect then disappear.
  have hfx_ne_top : f (x : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset x.2)).ne
  have hgap :=
    fundamental_prox_grad_inequality (f := f) (g := g) (x := (x : E)) (y := x) L hupper
  dsimp at hgap
  simpa [EReal.sub_self hfx_ne_top hfx_ne_bot] using hgap

/-- Helper for Corollary 10.18: the squared gradient-mapping norm is the squared stepsize times
the squared prox-gradient step norm. -/
lemma gradient_mapping_sq_eq_stepsize_sq_mul_step_norm_sq
    (L : PosReal) (x : interior (effective_domain f)) :
    ‖G[L, f, g] x‖ ^ (2 : ℕ) =
      ((L : ℝ) ^ (2 : ℕ)) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) := by
  -- Rewrite `G_L(x)` as the scaled step residual and compute its norm via `norm_smul`.
  calc
    ‖G[L, f, g] x‖ ^ (2 : ℕ) =
        (‖(L : ℝ)‖ * ‖(x : E) - T[L, f, g] x‖) ^ (2 : ℕ) := by
      rw [gradient_mapping_apply, norm_smul]
    _ = (((L : ℝ) * ‖(x : E) - T[L, f, g] x‖) ^ (2 : ℕ)) := by
      simp [Real.norm_eq_abs, abs_of_pos (PosReal.coe_pos L)]
    _ = ((L : ℝ) ^ (2 : ℕ)) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) := by
      rw [pow_two, pow_two]
      ring

/-- Helper for Corollary 10.18: the quadratic step-gap term equals the displayed
`(1 / (2L)) ‖G_L(x)‖²` coefficient after rewriting through the gradient mapping. -/
lemma half_stepsize_mul_step_norm_sq_eq_gradient_mapping_term
    (L : PosReal) (x : interior (effective_domain f)) :
    ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) =
      (((1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Convert the step norm to the gradient-mapping norm first, then simplify the scalar factor
  -- using the positivity of `L`.
  congr 1
  rw [gradient_mapping_sq_eq_stepsize_sq_mul_step_norm_sq (f := f) (g := g) L x]
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos L)
  field_simp [hL_ne]

/-- Corollary 10.18: if the local quadratic upper model of `f` at the prox-grad step `T_L(x)`
holds, then the composite objective decreases by at least
`(1 / (2L)) ‖G_L(x)‖²`. -/
theorem prox_grad_sufficient_decrease_of_upper_model
    (L : PosReal) (x : interior (effective_domain f))
    (hupper : proximal_gradient_backtracking_B2_accepts f g L x) :
    F x - F (T[L, f, g] x) ≥
      (((1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) :=
by
  -- Route correction: the textbook source assumes `f : E → (-∞, ∞]`, but the generated Lean
  -- statement omitted the corresponding `f_ne_bot` hypothesis. The diagonal cancellation in
  -- `fundamental_prox_grad_inequality` therefore cannot be justified from the current hypotheses.
  -- TODO: restore the missing source hypothesis `∀ y, f y ≠ ⊥`, apply
  -- `prox_grad_gap_at_basepoint_of_ne_bot`, and then rewrite with
  -- `half_stepsize_mul_step_norm_sq_eq_gradient_mapping_term`.
  sorry

end
