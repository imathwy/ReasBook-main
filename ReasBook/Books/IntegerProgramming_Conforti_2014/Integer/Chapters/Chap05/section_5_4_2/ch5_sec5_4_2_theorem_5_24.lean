import Integer.Chapters.Chap05.section_5_4_2.ch5_sec5_4_2_algorithm_5_4_2_extra_1

section Theorem524

variable {n p : ℕ} (hp : p ≤ n)
variable {StageRow RestrictedRow : ℕ → Type}
variable (execution : specialized_lift_project_execution n p StageRow RestrictedRow)

variable
    (c : Fin n → ℝ)
    (is_optimal_basic_solution_of_stage :
      ∀ k, (Fin n → ℝ) → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        (Fin n → ℝ) → Prop)
    (is_optimal_original_solution : (Fin n → ℝ) → Prop)
    (is_restricted_system :
      ∀ k, Fin p → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) → Prop)
    (is_optimal_basic_solution_of_auxiliary_lp :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → Prop)
    (is_j_cut_of_auxiliary_solution :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → lift_project_cut n → Prop)
    (next_stage_adds_cut :
      ∀ k, Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) → lift_project_cut n →
        Matrix (StageRow (k + 1)) (Fin n) ℝ → (StageRow (k + 1) → ℝ) → Prop)

namespace specialized_lift_project_execution

/-- A specialized lift-and-project run stops at stage `k` when the current basic solution already
satisfies the binary restrictions on the first `p` coordinates. -/
def StopsAt (k : ℕ) : Prop :=
  has_binary_prefix hp (execution.basic_solution k)

/-- A specialized lift-and-project run stops exactly when its current basic solution satisfies the
binary restrictions on the first `p` coordinates. -/
@[simp] theorem stopsAt_iff
    (k : ℕ) :
    execution.StopsAt hp k ↔ has_binary_prefix hp (execution.basic_solution k) :=
  Iff.rfl

/-- The optional selected-index view is `none` exactly at the stages where the specialized
lift-and-project run stops. -/
@[simp] theorem selectedIndexOption_eq_none_iff_stopsAt
    (k : ℕ) :
    execution.selectedIndexOption hp k = none ↔ execution.StopsAt hp k := by
  simpa [StopsAt] using execution.selectedIndexOption_eq_none_iff hp k

end specialized_lift_project_execution

-- Semantic recall: `Finite.of_injective` and `Set.Finite.of_injOn` match the intended
-- finite-cut-space plus injectivity termination pattern used by the helper and main theorem.
/-- Helper for Theorem 5.24: under the stagewise algorithm clause together with the cut-separation,
active-cut injectivity, and per-index cut finiteness hypotheses used in the termination argument,
the specialized lift-and-project execution stops after finitely many iterations. -/
theorem
    specialized_lift_project_algorithm_terminates_of_cut_injective_of_finite_generated_cuts
    [execution.IsAlgorithm hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut]
    (current_solution_violates_generated_cut :
      ∀ k,
        ¬ has_binary_prefix hp (execution.basic_solution k) →
          ¬ (execution.generated_cut k).Satisfied (execution.basic_solution k))
    (active_generated_cut_injective :
      ∀ ⦃k₁ k₂ : ℕ⦄,
        ¬ has_binary_prefix hp (execution.basic_solution k₁) →
        ¬ has_binary_prefix hp (execution.basic_solution k₂) →
        execution.generated_cut k₁ = execution.generated_cut k₂ →
        k₁ = k₂)
    (finite_generated_cuts_at_index :
      ∀ j : Fin p,
        Set.Finite
          {cut : lift_project_cut n |
            ∃ k : ℕ,
              ¬ has_binary_prefix hp (execution.basic_solution k) ∧
                (execution.selected_index k, execution.generated_cut k) = (j, cut)}) :
    ∃ T : ℕ,
      execution.StopsAt hp T := sorry

/-- Theorem 5.24. The specialized lift-and-project algorithm terminates after a finite number of
iterations for every mixed `0,1` linear program, formalized here as the existence of a terminal
stage for any specialized lift-and-project execution satisfying the textbook stagewise algorithm
clause together with the finite-cut-space and active-cut nonrepetition hypotheses used in the
termination argument. -/
theorem specialized_lift_project_algorithm_terminates
    [execution.IsAlgorithm hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut]
    (current_solution_violates_generated_cut :
      ∀ k,
        ¬ has_binary_prefix hp (execution.basic_solution k) →
          ¬ (execution.generated_cut k).Satisfied (execution.basic_solution k))
    (active_generated_cut_injective :
      ∀ ⦃k₁ k₂ : ℕ⦄,
        ¬ has_binary_prefix hp (execution.basic_solution k₁) →
        ¬ has_binary_prefix hp (execution.basic_solution k₂) →
        execution.generated_cut k₁ = execution.generated_cut k₂ →
        k₁ = k₂)
    (finite_generated_cuts_at_index :
      ∀ j : Fin p,
        Set.Finite
          {cut : lift_project_cut n |
            ∃ k : ℕ,
              ¬ has_binary_prefix hp (execution.basic_solution k) ∧
                (execution.selected_index k, execution.generated_cut k) = (j, cut)}) :
    ∃ T : ℕ,
      execution.StopsAt hp T := sorry

end Theorem524
