

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_8 (from Chap05) -/
open scoped BigOperators

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.8 is `source-facing`: it records the Chapter 5 smoothness statement for the
concrete log-sum-exp function on Euclidean `ℝ^n`. The smoothness owner is already
`is_l_smooth_on` from Definition 5.1, while the function owner is already Chapter 4's
`log_sum_exp_function : (Fin n → ℝ) → EReal`. This file therefore keeps only the Euclidean
smoothness statement as a `bridge/view` to that earlier owner. -/

recall log_sum_exp_function

-- Proof sketch: compute the Hessian of `fun x ↦ (log_sum_exp_function x).toReal` as
-- `diag(w) - w * wᵀ`, where `w_i = exp (x i) / ∑ k, exp (x k)`. This Hessian is positive
-- semidefinite and bounded above by the identity, so every maximal eigenvalue is at most `1`.
-- Apply the Euclidean Hessian characterization of smoothness for convex functions to conclude
-- global `1`-smoothness.
/-- Proposition 5.8: the log-sum-exp function
`x ↦ log (e^{x_1} + e^{x_2} + ⋯ + e^{x_n})` on Euclidean `ℝ^n` is globally `1`-smooth with
respect to the `l_2` norm. -/
theorem log_sum_exp_l2_function_is_one_smooth (n : ℕ) :
    is_l_smooth_on
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function x).toReal)
      Set.univ 1 := sorry

/-! ### Theorem_5_8 (from Chap05) -/
universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.8 is `source-facing`. Domain sampling:
- mathlib owners: `DifferentiableAt`, `LipschitzOnWith`, the canonical ambient gradient `∇`,
  and `List.TFAE` for equivalence lists;
- chapter owner: Definition 5.1's `is_l_smooth_on`, specialized here to `Set.univ`;
- derived bridge: Lemma 5.7's `is_l_smooth_on_descent_lemma`, which gives clause (ii).

The primitive data are only the convex differentiable function `f` and the smoothness parameter
`L`; the quadratic upper model is derived from the owner predicate, while the lower-gradient
bound, cocoercivity inequality, and convex-combination inequality are source-facing companion
views of the same owner-level smoothness notion. The correct public shape is therefore one
`List.TFAE` theorem and not a new wrapper predicate or package. -/

-- Proof sketch: use Definition 5.1 to identify clause (i) with global Lipschitz control of the
-- derivative/gradient. Then combine the descent lemma with the standard Baillon-Haddad style
-- implications for convex differentiable functions to prove `(i) → (ii) → (iii) → (iv) → (i)`,
-- and show `(ii) ↔ (v)` by applying the upper quadratic model at the convex combination point and
-- passing to the endpoint limit in the reverse direction.
/-- Theorem 5.8: for a convex differentiable real-valued function and a positive smoothness
parameter `L`, the following are equivalent: (i) `f` is globally `L`-smooth, (ii) `f` satisfies
the quadratic upper model, (iii) `f` satisfies the quadratic lower bound in terms of gradient
differences, (iv) the gradient is `1 / L`-cocoercive, and (v) the convex-combination inequality is
relaxed by the quadratic error term `L / 2 * λ * (1 - λ) * ‖x - y‖²`. The ambient
differentiability hypothesis ensures that `∇ f` agrees everywhere with the actual derivative,
rather than with mathlib's default zero value at nondifferentiable points. -/
theorem convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
    (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    (L : NNReal) (hL : 0 < L) :
    List.TFAE
      [is_l_smooth_on f Set.univ L,
        ∀ x y : E,
          f y ≤
            f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ),
        ∀ x y : E,
          f y ≥
            f x + inner ℝ (∇ f x) (y - x) +
              (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ),
        ∀ x y : E,
          inner ℝ (∇ f x - ∇ f y) (x - y) ≥
            (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ),
        ∀ x y : E, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          f (t • x + (1 - t) • y) ≥
            t * f x + (1 - t) * f y -
              ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)] := sorry

end
