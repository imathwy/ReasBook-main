import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_24 (from Chap08) -/
open Matrix

section

variable {m n : ℕ}

/- Definition 8.24 is `source-facing`: the new data in the textbook item is the feasible region
cut out by the linear inequalities `A x ≤ b` together with the simplex constraint `x ∈ Δ_n`.
The owner abstraction for optimality itself is mathlib's `IsMinOn`, so the file introduces only
the source-facing feasible set and a thin bridge theorem for the minimization statement. -/

/-- Definition 8.24: the feasible set of the linear program `(LP)` consists of the vectors
`x ∈ Δ_n = stdSimplex ℝ (Fin n)` satisfying the coordinatewise linear inequality `A x ≤ b`. -/
def simplex_linear_program_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b ∧ x ∈ stdSimplex ℝ (Fin n)}

-- Proof sketch: unfold `simplex_linear_program_feasible_set`; membership is exactly the
-- conjunction of the coordinatewise inequality `A *ᵥ x ≤ b` and the simplex constraint
-- `x ∈ stdSimplex ℝ (Fin n)`.
/-- Membership in `simplex_linear_program_feasible_set A b` means satisfying `A x ≤ b` and
belonging to the standard simplex `Δ_n`. -/
@[simp] theorem mem_simplex_linear_program_feasible_set
    {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ} :
    x ∈ simplex_linear_program_feasible_set A b ↔
      A *ᵥ x ≤ b ∧ x ∈ stdSimplex ℝ (Fin n) := by
  -- Unfolding the feasible-set definition exposes exactly the two textbook constraints.
  rfl

-- Proof sketch: unfold `IsMinOn` and rewrite membership in
-- `simplex_linear_program_feasible_set A b` using
-- `mem_simplex_linear_program_feasible_set`. This turns the owner minimizer predicate into the
-- textbook statement that `x` is feasible and has no larger linear cost than any other feasible
-- point.
/-- Helper for Definition 8.24: feasibility of `x` together with minimizing `cᵀ x` on
`simplex_linear_program_feasible_set A b` is equivalent to the textbook linear-programming
optimality condition. -/
theorem isMinOn_simplex_linear_program_feasible_set_iff
    {c : Fin n → ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ} :
    x ∈ simplex_linear_program_feasible_set A b ∧
      IsMinOn (fun y ↦ c ⬝ᵥ y) (simplex_linear_program_feasible_set A b) x ↔
      A *ᵥ x ≤ b ∧
        x ∈ stdSimplex ℝ (Fin n) ∧
        ∀ y, A *ᵥ y ≤ b → y ∈ stdSimplex ℝ (Fin n) → c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  -- Route correction: `IsMinOn` does not assert membership in the feasible set, so the bridge
  -- theorem must carry feasibility of `x` explicitly on the left.
  rw [isMinOn_iff]
  -- Rewriting feasible-set membership reduces both sides to the textbook constraints and the
  -- universal comparison against every feasible point.
  simp [mem_simplex_linear_program_feasible_set, and_assoc]

end

/-! ### Lemma_8_24 (from Chap08) -/
universe u

open InnerProductSpace (toDualMap)
noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ)
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

-- Proof sketch: apply `projected_subgradient_method_fundamental_inequality` for each
-- `n ∈ Finset.range (k + 1)`, sum the resulting inequalities, and use telescoping on the squared
-- distance terms. Then drop the nonnegative final term `‖x[k + 1] - xStar‖^2 / 2`.
/-- Lemma 8.24: under Assumption 8.7, the stepsize-weighted cumulative objective gap along the
projected subgradient iterates up to step `k` is bounded by one half of the initial squared
distance to an optimal point plus one half of the accumulated squared subgradient norms. -/
theorem projected_subgradient_method_weighted_objective_gap_sum_le
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f (x[n] : E)).toReal - fOpt)) ≤
      (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) := sorry

end
