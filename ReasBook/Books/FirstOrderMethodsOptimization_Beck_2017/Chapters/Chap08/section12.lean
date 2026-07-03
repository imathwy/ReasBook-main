import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_8_12 (from Chap08) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 8.12 is `source-facing`: the textbook assumes one uniform constant controlling the
norms of all subgradients on the feasible set `C`. Domain sampling against Chapter 3 shows that
the canonical owner for norm-bounded subgradients is the continuous-dual bridge
`strongDualSubdifferential f x`, not a separate wrapper around chosen Euclidean selections. The
public API therefore packages one chosen bound together with its positivity and the pointwise norm
estimate on that owner set. -/

/-- Assumption 8.12: a subgradient norm bound on `f` over `C` consists of a constant `L_f > 0`
such that every continuous-dual subgradient of `f` at every point of `C` has norm at most
`L_f`. -/
structure SubgradientNormBoundOn (f : E → EReal) (C : Set E) where
  L_f : ℝ
  L_f_pos : 0 < L_f
  norm_le {x : E} {g : StrongDual ℝ E}
      (hx : x ∈ C) (hg : g ∈ strongDualSubdifferential f x) : ‖g‖ ≤ L_f

/-- A subgradient norm bound is canonically used as its underlying bound constant `L_f`. -/
instance {f : E → EReal} {C : Set E} : CoeOut (SubgradientNormBoundOn f C) ℝ where
  coe h := h.L_f

end

/-! ### Definition_8_12 (from Chap08) -/
universe u

section

variable {E : Type u}

/- Definition 8.12 is `source-facing`: the textbook introduces the pointwise notion of an
`ε`-optimal feasible point for a constrained minimization problem. In this chapter the canonical
owner data for that notion is the feasible real sublevel set `C ∩ f ⁻¹' Set.Iic (fOpt + ε)`, so
the public API records the point predicate directly as membership in that set, with no extra
problem wrapper. -/

/-- Definition 8.12: a vector `x` is an `ε`-optimal solution of `min {f(x) : x ∈ C}` when `x`
lies in `C` and its objective value is at most `fOpt + ε`. -/
def is_epsilon_optimal_solution
    (f : E → EReal) (C : Set E) (fOpt ε : ℝ) (x : E) : Prop :=
  x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal)

-- Proof sketch: unfold `is_epsilon_optimal_solution`; the predicate was defined to be membership
-- in the feasible sublevel set `C ∩ f ⁻¹' Set.Iic (fOpt + ε)`.
/-- Unfolding `is_epsilon_optimal_solution` identifies it with membership in the feasible
`(fOpt + ε)`-sublevel set. -/
theorem is_epsilon_optimal_solution_def
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_solution f C fOpt ε x ↔
      x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal) := by
  -- The theorem is just the defining equation of the point predicate.
  simp [is_epsilon_optimal_solution]

/-- Helper for Definition 8.12: membership in the feasible sublevel set is equivalent to
feasibility together with the objective-value bound. -/
lemma mem_feasible_sublevel_iff
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal) ↔
      x ∈ C ∧ f x ≤ (fOpt + ε : EReal) := by
  -- Normalize the intersection, preimage, and interval membership into a conjunction.
  simp [Set.mem_preimage]

-- Proof sketch: unfold `is_epsilon_optimal_solution`; membership in the intersection is exactly
-- feasibility together with membership in the real sublevel set `Set.Iic (fOpt + ε)`.
/-- A point is `ε`-optimal exactly when it is feasible and its objective value is at most
`fOpt + ε`. -/
@[simp] theorem is_epsilon_optimal_solution_iff
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_solution f C fOpt ε x ↔ x ∈ C ∧ f x ≤ (fOpt + ε : EReal) := by
  -- Rewrite the predicate into feasible-sublevel membership and then flatten that membership.
  rw [is_epsilon_optimal_solution_def, mem_feasible_sublevel_iff]

end

/-! ### Proposition_8_12 (from Chap08) -/
universe u v

open scoped BigOperators

section

variable {E : Type u} {G : Type v}
variable [AddCommMonoid E] [Module ℝ E] [Norm G]
variable {m : ℕ}
variable (x : ℕ → E) (γ : ℕ → ℝ) (h : ℕ → G)

/- Proposition 8.12 is `source-facing`: the textbook claims the `O(ε⁻²)` iteration complexity of
the partial averaging scheme. In this standalone item file, the clean public surface is the
explicit partial-average iterate together with the textbook feasible set and objective sublevel
condition, avoiding any new asymptotic wrapper. -/

local notation "x̄[" k "]" =>
  Finset.sum (Finset.Icc (k / 2) k) fun n ↦
    ((γ n / ‖h n‖) /
      Finset.sum (Finset.Icc (k / 2) k) (fun j ↦ γ j / ‖h j‖)) • x n

/-- The feasible set determined by the ambient constraint set `X` and inequality family `g`. -/
def partialAveragingFeasibleSet {m : ℕ} (X : Set E) (g : Fin m → E → ℝ) : Set E :=
  {y | y ∈ X ∧ ∀ i : Fin m, g i y ≤ 0}

-- Proof sketch: square the inequality `M / √(k + 1) ≤ ε` and rearrange it exactly as in the usual
-- `O(ε⁻²)` iteration-count estimate.
/-- The standard iteration threshold `M² / ε² - 1 ≤ k` implies the corresponding rate bound
`M / √(k + 1) ≤ ε`. -/
theorem rate_bound_le_epsilon_of_iteration_count
    (M ε : ℝ) (k : ℕ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hk : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ)) :
    M / Real.sqrt ((k : ℝ) + 1) ≤ ε := by
  -- First rewrite the iteration threshold as a bound on `M²`.
  have hεsq : 0 < ε ^ (2 : ℕ) := by positivity
  have hk' : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
    linarith
  have hsq_bound : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
    exact (div_le_iff₀ hεsq).mp hk'
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  -- Then compare squares to recover the unsquared estimate `M ≤ ε * √(k + 1)`.
  have hsq_sqrt : (Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) = (k : ℝ) + 1 := by
    simpa using Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity)
  have hsq_bound' : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
    calc
      M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := hsq_bound
      _ = ε ^ (2 : ℕ) * (Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
        rw [hsq_sqrt]
        ring
      _ = (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by ring
  have h_linear : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
    simpa [abs_of_nonneg hM, abs_of_nonneg (mul_nonneg (le_of_lt hε) hsqrt_nonneg)] using
      (sq_le_sq.mp hsq_bound')
  -- Finally divide by the positive square root to recover the desired rate bound.
  exact (div_le_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using h_linear)

-- Proof sketch: use `rate_bound_le_epsilon_of_iteration_count` to turn the assumed
-- `O((k + 1)⁻¹ᐟ²)` objective-gap estimate into `f(x̄ᵏ) ≤ fOpt + ε`, then combine this with the
-- exact feasibility hypothesis.
/-- Proposition 8.12: if the partial-averaging iterate
`x̄^k = ∑_{n=[k/2]}^k η_n^k x^n` is feasible and its objective gap is bounded by
`M / √(k + 1)`, then the usual threshold `M² / ε² - 1 ≤ k` guarantees that `x̄^k` lies in the
feasible `(fOpt + ε)`-sublevel set. In particular, the required number of iterations is of order
`1 / ε²`. -/
theorem partial_averaging_iterate_mem_feasible_sublevel_set_of_iteration_count
    {X : Set E} {f : E → ℝ} {g : Fin m → E → ℝ}
    (fOpt M ε : ℝ) (k : ℕ)
    (hM : 0 ≤ M) (hε : 0 < ε)
    (h_rate : f x̄[k] - fOpt ≤ M / Real.sqrt ((k : ℝ) + 1))
    (h_feasible : x̄[k] ∈ partialAveragingFeasibleSet X g)
    (hk : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ)) :
    x̄[k] ∈
      partialAveragingFeasibleSet X g ∩
        (fun y ↦ (f y : EReal)) ⁻¹' Set.Iic (fOpt + ε : EReal) := by
  constructor
  · -- The feasibility component is already assumed as an invariant of the iterate.
    exact h_feasible
  · -- Convert the `O((k + 1)⁻¹ᐟ²)` objective-gap estimate into an `ε`-sublevel bound.
    have h_rate_to_epsilon : M / Real.sqrt ((k : ℝ) + 1) ≤ ε :=
      rate_bound_le_epsilon_of_iteration_count M ε k hM hε hk
    have h_gap : f x̄[k] - fOpt ≤ ε := le_trans h_rate h_rate_to_epsilon
    have h_sublevel : f x̄[k] ≤ fOpt + ε := by
      linarith
    change ((f x̄[k] : EReal) ≤ (fOpt + ε : EReal))
    exact_mod_cast h_sublevel

end
