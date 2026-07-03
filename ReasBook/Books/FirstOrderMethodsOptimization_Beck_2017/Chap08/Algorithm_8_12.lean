import FirstOrderMethodsinOptimization.Chap08.Algorithm_8_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators

noncomputable section

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Source-facing note: the textbook specializes the stochastic projected subgradient method to a
finite-sum objective by sampling one component index `i_k` and then using one subgradient of the
sampled summand in the projected update. The canonical owner remains the stochastic iterate
sequence `stochastic_projected_subgradient_method` from Algorithm 8.10, while the new data are
the finite-sum bound constant `L̃_f`, the corresponding textbook stepsize, and the sampled
component-subgradient rule. The public API therefore keeps the sampled index process explicit and
realizes the algorithm as a thin specialization of that existing owner. -/

/-- The finite-sum stochastic subgradient bound constant
`L̃_f = √m * √(∑ i, L_i^2)` from Algorithm 8.12. -/
def finite_sum_stochastic_subgradient_bound_constant {m : ℕ} (L : Fin m → ℝ) : ℝ :=
  Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ))

/-- The textbook stepsize `√(2 Θ m) / (L̃_f √(k + 1))` used in Algorithm 8.12. -/
def finite_sum_stochastic_projected_subgradient_stepsize {m : ℕ}
    (Θ : ℝ) (L : Fin m → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (2 * Θ * (m : ℝ)) /
    (finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (k + 1 : ℝ))

/-- Algorithm 8.12: for a nonempty closed convex feasible set `C`, a feasible initial point `x0`,
componentwise subgradient choices `g k x j`, and a sampled index rule `i_k`, the stochastic
projected subgradient method for a finite-sum objective is the Algorithm 8.10 iteration
specialized to the sampled direction `g k x (i_k ω)` and the stepsize
`√(2 Θ m) / (L̃_f √(k + 1))`, where `L̃_f = √m * √(∑ i, L_i^2)`. -/
abbrev finite_sum_stochastic_projected_subgradient_method {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (Θ : ℝ) (L : Fin m → ℝ) (i : ℕ → Ω → Fin m) (g : ℕ → C → Fin m → E) (x0 : C) :
    ℕ → Ω → C :=
  stochastic_projected_subgradient_method C hC_nonempty hC_closed hC_convex
    (fun k x ω ↦ g k x (i k ω))
    (finite_sum_stochastic_projected_subgradient_stepsize Θ L)
    x0

section

variable {m : ℕ}
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (Θ : ℝ) (L : Fin m → ℝ) (i : ℕ → Ω → Fin m) (g : ℕ → C → Fin m → E) (x0 : C)

local notation "x[" k "]" =>
  finite_sum_stochastic_projected_subgradient_method
    C hC_nonempty hC_closed hC_convex Θ L i g x0 k

-- Proof sketch: unfold
-- `finite_sum_stochastic_projected_subgradient_method`; the resulting Algorithm 8.10 iterate at
-- `0` is the constant path with value `x0`.
/-- The finite-sum stochastic projected-subgradient sequence starts from the prescribed feasible
initial point at every sample `ω`. -/
theorem finite_sum_stochastic_projected_subgradient_method_zero (ω : Ω) :
    x[0] ω = x0 := sorry

-- Proof sketch: unfold `finite_sum_stochastic_projected_subgradient_method` and then apply the
-- one-step expansion `stochastic_projected_subgradient_method_succ` from Algorithm 8.10 to the
-- specialized sampled direction `fun k x ω ↦ g k x (i k ω)` and the textbook stepsize
-- `finite_sum_stochastic_projected_subgradient_stepsize Θ L`.
/-- One step of Algorithm 8.12 applies the metric projection onto `C` to the current sample
iterate minus the sampled component subgradient scaled by
`√(2 Θ m) / (L̃_f √(k + 1))`. -/
theorem finite_sum_stochastic_projected_subgradient_method_succ (k : ℕ) (ω : Ω) :
    x[k + 1] ω =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((x[k] ω : E) -
          (Real.sqrt (2 * Θ * (m : ℝ)) /
              (finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (k + 1 : ℝ))) •
            g k (x[k] ω) (i k ω)) := sorry

end

end
