import Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1

-- Semantic recall note: the source-faithful owner here takes lexicographic optimality relative
-- to the full feasible region of `(5.27)`. Since the repo has no existing simplex-run owner on
-- feasible bases, part (2) introduces a local source-facing lexicographic simplex run structure.

open scoped Matrix

section Exercise511

variable {m n : ℕ}

namespace standard_form_basis

/-- A basis of `(5.27)` is lexicographically optimal when it is primal feasible and its associated
basic solution, viewed in `ℝⁿ`, is lexicographically greatest among all feasible solutions of
`(5.27)`. -/
def IsLexicographicallyOptimal
    {A : Matrix (Fin m) (Fin n) ℚ}
    (B : standard_form_basis A)
    (b : Fin m → ℚ) : Prop :=
  B.is_primal_feasible b ∧
    IsGreatest
      (toLex '' standard_equality_form (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)))
      (toLex (fun i ↦ (B.basic_solution b i : ℝ)))

theorem IsLexicographicallyOptimal.basic_feasible
    {A : Matrix (Fin m) (Fin n) ℚ}
    {B : standard_form_basis A}
    {b : Fin m → ℚ}
    (h : B.IsLexicographicallyOptimal b) :
    is_basic_feasible_solution A b (B.basic_solution b) := by
  constructor
  · intro j
    by_cases hj : j ∈ B.columns
    · have hj_range : j ∈ Set.range B.cols := by
        simpa [B.mem_columns_iff_mem_range j] using hj
      rcases hj_range with ⟨i, rfl⟩
      simpa [basic_solution_apply_cols] using h.1 i
    · simp [B.basic_solution_eq_zero_of_not_mem_columns b hj]
  · exact ⟨B, rfl⟩

theorem IsLexicographicallyOptimal.is_primal_feasible
    {A : Matrix (Fin m) (Fin n) ℚ}
    {B : standard_form_basis A}
    {b : Fin m → ℚ}
    (h : B.IsLexicographicallyOptimal b) :
    B.is_primal_feasible b := by
  exact h.1

/-- A simplex pivot exchanges one basis column for one previously nonbasic column. -/
def IsBasisExchange
    {A : Matrix (Fin m) (Fin n) ℚ}
    (B B' : standard_form_basis A) : Prop :=
  ∃ leaving : Fin m, ∃ entering : Fin n,
    entering ∉ B.columns ∧
      ∀ j : Fin n, j ∈ B'.columns ↔ j = entering ∨ (j ∈ B.columns ∧ j ≠ B.cols leaving)

/-- A lexicographic simplex pivot is a feasible basis exchange that strictly increases the
lexicographic basic solution. -/
def IsLexicographicSimplexPivot
    {A : Matrix (Fin m) (Fin n) ℚ}
    (B : standard_form_basis A)
    (b : Fin m → ℚ)
    (B' : standard_form_basis A) : Prop :=
  B.IsBasisExchange B' ∧
    B.is_primal_feasible b ∧
    B'.is_primal_feasible b ∧
    toLex (fun i ↦ (B.basic_solution b i : ℝ)) <
      toLex (fun i ↦ (B'.basic_solution b i : ℝ))

end standard_form_basis

/-- Exercise 5.11 (1). Let `B` be a feasible basis of `(5.27)`. If `B` is lexicographically
optimal, then the associated basic solution is the lexicographically largest feasible solution
of `(5.27)`. -/
theorem lexicographically_optimal_basis_basic_solution_is_lexicographically_largest
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {B : standard_form_basis A}
    (hB : B.IsLexicographicallyOptimal b) :
    IsGreatest
      (toLex '' standard_equality_form (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)))
      (toLex (fun i ↦ (B.basic_solution b i : ℝ))) := sorry

/-- A finite lexicographic simplex run through feasible bases from `B₀` to a terminal
lexicographically optimal basis of `(5.27)`. Each nonterminal step is an actual basis exchange
that strictly improves the lexicographic basic solution. -/
structure LexicographicSimplexRun
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (B₀ : standard_form_basis A) where
  T : ℕ
  bases : Fin (T + 1) → standard_form_basis A
  start_eq : bases 0 = B₀
  feasible : ∀ t : Fin (T + 1), (bases t).is_primal_feasible b
  simplex_step :
    ∀ t : Fin T, (bases t.castSucc).IsLexicographicSimplexPivot b (bases t.succ)
  optimal_terminal : (bases ⟨T, Nat.lt_succ_self T⟩).IsLexicographicallyOptimal b

/-- Exercise 5.11 (2). Starting from a feasible basis of `(5.27)`, if a lexicographically
optimal basis exists, then the simplex algorithm can compute one by a finite sequence of simplex
pivots through feasible bases. -/
theorem lexicographic_simplex_method_computes_lexicographically_optimal_terminal_basis
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {B₀ : standard_form_basis A}
    (hB₀ : B₀.is_primal_feasible b)
    (hExists : ∃ B : standard_form_basis A, B.IsLexicographicallyOptimal b) :
    Nonempty (LexicographicSimplexRun A b B₀) := sorry

end Exercise511
