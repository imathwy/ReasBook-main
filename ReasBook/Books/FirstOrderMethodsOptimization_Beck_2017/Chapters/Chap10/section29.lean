import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_29 (from Chap10) -/
noncomputable section

universe u

/- Definition 10.29 is a `bridge/view` item in the Chapter 10 Moreau-smoothing API.
Domain sampling identifies the owner abstraction and the primitive/derived split:

- `moreau_envelope` from Definition 6.7 is the `core/canonical` owner `M[μ, f]`;
- `moreau_envelope_apply` is the owner's canonical pointwise infimum formula;
- `Function.toEReal` from Definition 9.2 is the canonical bridge from a real-valued function `h`
  to the extended-real input expected by `M[μ, f]`.

The primitive data are only the smoothing parameter `μ` and the real-valued function `h`. The
numbered item adds no new owner-level construction beyond the specialization `M[μ, h.toEReal]`,
so this file should present that specialized chapter object directly rather than recalling only the
generic ingredients or reintroducing a parallel wrapper. -/

section

variable {E : Type u} [NormedAddCommGroup E]
variable (μ : PosReal) (h : E → ℝ)

/- Definition 10.29: for a real-valued function `h`, the Chapter 10 Moreau smoothing is exactly
the specialized Chapter 6 owner `M[μ, h.toEReal]`. -/
#check M[μ, h.toEReal]

end

section

variable {E : Type u} [NormedAddCommGroup E]
variable (μ : PosReal) (h : E → ℝ) (x : E)

/- Its pointwise formula is the corresponding specialization of
`moreau_envelope_apply` to `h.toEReal`. -/
#check
  (by
    simpa using (moreau_envelope_apply μ h.toEReal x) :
      M[μ, h.toEReal] x =
        ⨅ u : E, (h u : EReal) + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal))

end

/-! ### Theorem_10_29 (from Chap10) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

/- Theorem 10.29 is `source-facing` in the strongly-convex proximal-gradient API.

Domain sampling in the existing Chapter 10 development identifies:
- `IsCompositeSmoothMinimizationProblem` as the owner of Assumption 10.1;
- `is_proximal_gradient_trajectory` as the owner of the iterate sequence `x^k`;
- `hproblem.SublinearRateStepsizeRule x L htraj α` from Remark 10.19 as the chapter owner of the
  admissible constant/B2 stepsize regime together with its rate factor `α`;
- `condition_number` from Definition 10.21, with notation `κ(L_f, σ)`, as the chapter owner of
  the ratio `L_f / σ`.

Primitive data are the problem instance, trajectory, stepsize rule, strong-convexity modulus, and
optimal point. Definition 10.3 already canonically supplies the properness, lower-semicontinuity,
and convexity data for `g`, so those assumptions should not be duplicated on the theorem surface.
The stepsize hypothesis should therefore use the existing owner-level bridge from Remark 10.19,
rather than repeating its internal disjunction and local instance plumbing. The geometric
contraction factor is derived API, so the statements below reuse `κ(Lf, σ)` instead of restating
`L_f / σ` through parallel local arithmetic. -/

section

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {σ : PosReal} {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

local notation "F" => composite_model_objective f g
local notation "κ" => κ(Lf, σ)

/-- Helper for Theorem 10.29: any optimizer `xStar ∈ XStar` attains the optimal composite value
`FOpt`. -/
lemma objective_eq_optimal_value_of_mem_optimal_set
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {x : E} (hx : x ∈ XStar) :
    F x = (FOpt : EReal) := by
  -- The optimizer-set field identifies `x` as a global minimizer of the composite objective.
  apply le_antisymm
  · exact h.optimal_value_isGLB.2 <| by
      rintro _ ⟨y, rfl⟩
      have hx_opt : x ∈ unconstrained_problem_solutions F := by
        change x ∈ unconstrained_problem_solutions (composite_model_objective f g)
        simpa [h.optimal_set_eq] using hx
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hx_opt) y
  · exact h.optimal_value_isGLB.1 ⟨x, rfl⟩

-- Proof sketch: apply the fundamental prox-grad inequality with `x = xStar`, `y = x^k`, and
-- `L = L_k`; use strong convexity of `f` to bound the linearization error from below by
-- `(σ / 2) ‖x^k - xStar‖²`, use that `xStar` is optimal to make the objective gap nonpositive,
-- and then use the constant/B2 stepsize rule to replace `L_k` by the uniform factor `α L_f`.
/-- Theorem 10.29 (1): clause (a). Under Assumption 10.1, if `f` is `σ`-strongly convex and the
proximal-gradient trajectory uses either the constant rule `L_k = L_f` or backtracking procedure
B2 with the corresponding value of `α`, then with `κ = L_f / σ`,
`‖x^(k+1) - x*‖² ≤ (1 - 1 / (α κ)) ‖x^k - x*‖²`. -/
theorem proximal_gradient_strongly_convex_step_distance_sq_le
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      (1 - 1 / (α * κ)) * ‖x k - xStar‖ ^ (2 : ℕ) := by
  -- TODO: follow the source proof via the raw inequality
  -- `F xStar - F (x (k + 1)) ≥ (L_k / 2) ‖xStar - x^(k+1)‖² - ((L_k - σ) / 2) ‖xStar - x^k‖²`.
  -- The remaining blocker is the missing textbook bound `L_k ≤ α L_f` from the current
  -- hypothesis `hproblem.SublinearRateStepsizeRule x L htraj α`: its B2 branch stores only an
  -- accepted geometric trial plus the upper-model inequality, not the minimal accepted trial
  -- index needed by Remark 10.19(2), so the source coefficient reduction to `1 - σ / (α L_f)`
  -- cannot be derived from the available assumptions.
  sorry

-- Proof sketch: iterate clause (a) from `0` through `k - 1`; each step multiplies the squared
-- distance by the same factor `1 - 1 / (α * κ(Lf, σ))`, so induction yields the
-- geometric estimate.
/-- Theorem 10.29 (2): clause (b). Under the same hypotheses as clause (a), the iterates satisfy
the geometric distance estimate
`‖x^k - x*‖² ≤ (1 - 1 / (α κ))^k ‖x^0 - x*‖²`, where `κ = L_f / σ`. -/
theorem proximal_gradient_strongly_convex_distance_sq_le_geometric
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (1 - 1 / (α * κ)) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
  -- TODO: once clause (a) is available, iterate it inductively along the trajectory.
  sorry

-- Proof sketch: start from the one-step inequality underlying clause (a), rearrange it into an
-- objective-gap estimate, bound `L_k` above by `α L_f`, and then substitute the geometric
-- distance estimate from clause (b).
/-- Theorem 10.29 (3): clause (c). Under the same hypotheses as clause (a), the composite
objective gap satisfies
`F(x^(k+1)) - F_opt ≤ (α L_f / 2) (1 - 1 / (α κ))^(k+1) ‖x^0 - x*‖²`, where
`κ = L_f / σ`. -/
theorem proximal_gradient_strongly_convex_objective_gap_le
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    F (x (k + 1)) - (FOpt : EReal) ≤
      ((((α * (Lf : ℝ)) / 2) *
          (1 - 1 / (α * κ)) ^ (k + 1) *
          ‖x 0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- TODO: once clause (a) and clause (b) are proved, rewrite `F xStar = FOpt` using
  -- `objective_eq_optimal_value_of_mem_optimal_set hxStar` and combine the raw one-step inequality
  -- with the geometric distance estimate.
  sorry

end

end
