import Mathlib.Data.Real.Archimedean
import Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: the domain-sampling pass identified Example 8.14 as the owner of the
-- generalized-assignment LP-feasibility predicate and the machine-wise `0,1` knapsack block
-- family. This file therefore keeps only the Exercise 8.6 Lagrangian-relaxation layer local and
-- reuses those upstream generalized-assignment declarations directly.

noncomputable section

section Exercise86

/-- The Example 8.14 block-coefficient family specialized to the Exercise 8.6 item sizes `a_i`,
constant in the machine index. -/
def generalized_assignment_capacity_coeffs {m n : ℕ}
    (a : Fin m → ℝ) : Fin m → Fin n → ℝ :=
  fun i _ ↦ a i

/-- `generalized_assignment_capacity_coeffs a` is constant in the machine index. -/
@[simp] theorem generalized_assignment_capacity_coeffs_apply {m n : ℕ}
    (a : Fin m → ℝ) (i : Fin m) (j : Fin n) :
    generalized_assignment_capacity_coeffs a i j = a i :=
  rfl

/-- The objective value `∑_i ∑_j c_ij x_ij` of a binary generalized-assignment pattern. -/
def generalized_assignment_objective {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (x : Fin m → Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, c i j * bool_entry (x i j)

/-- `generalized_assignment_objective c x` unfolds to `∑_i ∑_j c_ij x_ij`. -/
theorem generalized_assignment_objective_eq_sum {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (x : Fin m → Fin n → Bool) :
    generalized_assignment_objective c x = ∑ i, ∑ j, c i j * bool_entry (x i j) :=
  rfl

/-- The base set obtained by keeping only the assignment constraints `∑_j x_ij ≤ 1`
and the binary restrictions. This is the easy set used when the capacity constraints are
dualized. -/
def generalized_assignment_assignment_base_set {m n : ℕ} : Set (Fin m → Fin n → Bool) :=
  {x | ∀ i, ∑ j, bool_entry (x i j) ≤ 1}

/-- Membership in `generalized_assignment_assignment_base_set` means exactly that every item is
assigned to at most one machine. -/
theorem mem_generalized_assignment_assignment_base_set_iff {m n : ℕ}
    {x : Fin m → Fin n → Bool} :
    x ∈ generalized_assignment_assignment_base_set ↔
      ∀ i, ∑ j, bool_entry (x i j) ≤ 1 :=
  Iff.rfl

/-- The base set obtained by keeping only the capacity constraints
`∑_i a_i x_ij ≤ b_j` and the binary restrictions. This is the easy set used when the
assignment constraints are dualized. -/
def generalized_assignment_capacity_base_set {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) : Set (Fin m → Fin n → Bool) :=
  {x |
    ∀ j, (fun i ↦ x i j) ∈ generalized_assignment_block_patterns
      (generalized_assignment_capacity_coeffs a) b j
  }

/-- Membership in `generalized_assignment_capacity_base_set a b` is exactly the family of
machine-wise knapsack inequalities `∑_i a_i x_ij ≤ b_j`. -/
theorem mem_generalized_assignment_capacity_base_set_iff {m n : ℕ}
    {a : Fin m → ℝ} {b : Fin n → ℝ} {x : Fin m → Fin n → Bool} :
    x ∈ generalized_assignment_capacity_base_set a b ↔
      ∀ j, ∑ i, a i * bool_entry (x i j) ≤ b j := by
  simp [generalized_assignment_capacity_base_set, mem_generalized_assignment_block_patterns_iff]

/-- The LP-relaxation value of the generalized assignment problem. -/
def generalized_assignment_lp_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * x i j) ''
      {x | generalized_assignment_lp_feasible (generalized_assignment_capacity_coeffs a) b x})

/-- `generalized_assignment_lp_value a b c` unfolds to the supremum of the linear objective over
the LP-feasible set. -/
theorem generalized_assignment_lp_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_lp_value a b c =
      sSup
        ((fun x : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * x i j) ''
          {x |
            generalized_assignment_lp_feasible
              (generalized_assignment_capacity_coeffs a) b x}) :=
  rfl

/-- The Lagrangian relaxation value obtained by dualizing the capacity constraints
`∑_i a_i x_ij ≤ b_j` with nonnegative multipliers `μ_j` and keeping the assignment constraints
and the binary restrictions in the base set. -/
def generalized_assignment_capacity_relaxed_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → Bool ↦
        generalized_assignment_objective c x +
          ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))) ''
      generalized_assignment_assignment_base_set)

/-- `generalized_assignment_capacity_relaxed_value a b c μ` unfolds to the supremum of the
capacity-relaxed Lagrangian objective over `generalized_assignment_assignment_base_set`. -/
theorem generalized_assignment_capacity_relaxed_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_value a b c μ =
      sSup
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))) ''
          generalized_assignment_assignment_base_set) :=
  rfl

/-- The Lagrangian dual obtained by dualizing the capacity constraints. -/
def generalized_assignment_capacity_relaxed_dual_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf
    ((fun μ : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c μ) ''
      Set.Ici (0 : Fin n → ℝ))

/-- `generalized_assignment_capacity_relaxed_dual_value a b c` unfolds to the infimum of the
capacity-relaxed values over all nonnegative multiplier vectors `μ`. -/
theorem generalized_assignment_capacity_relaxed_dual_value_eq_sInf {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_dual_value a b c =
      sInf
        ((fun μ : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c μ) ''
          Set.Ici (0 : Fin n → ℝ)) :=
  rfl

/-- The Lagrangian relaxation value obtained by dualizing the assignment constraints
`∑_j x_ij ≤ 1` with nonnegative multipliers `λ_i` and keeping the capacity constraints and the
binary restrictions in the base set. -/
def generalized_assignment_assignment_relaxed_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → Bool ↦
        generalized_assignment_objective c x +
          ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
      generalized_assignment_capacity_base_set a b)

/-- `generalized_assignment_assignment_relaxed_value a b c λ` unfolds to the supremum of the
assignment-relaxed Lagrangian objective over `generalized_assignment_capacity_base_set a b`. -/
theorem generalized_assignment_assignment_relaxed_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) :
    generalized_assignment_assignment_relaxed_value a b c lam =
      sSup
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
          generalized_assignment_capacity_base_set a b) :=
  rfl

/-- The Lagrangian dual obtained by dualizing the assignment constraints. -/
def generalized_assignment_assignment_relaxed_dual_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf
    ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
      Set.Ici (0 : Fin m → ℝ))

/-- `generalized_assignment_assignment_relaxed_dual_value a b c` unfolds to the infimum of the
assignment-relaxed values over all nonnegative multiplier vectors `λ`. -/
theorem generalized_assignment_assignment_relaxed_dual_value_eq_sInf {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_assignment_relaxed_dual_value a b c =
      sInf
        ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
          Set.Ici (0 : Fin m → ℝ)) :=
  rfl

/-- The reduced-profit objective of the `j`th knapsack subproblem after dualizing the assignment
constraints. -/
def generalized_assignment_column_reduced_profit {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (j : Fin n) (z : Fin m → Bool) : ℝ :=
  ∑ i, (c i j - lam i) * bool_entry (z i)

/-- The reduced-profit contribution of item `i` under the capacity-relaxed Lagrangian:
choosing `none` gives value `0`, while choosing `some j` gives `c_ij - μ_j a_i`. -/
def generalized_assignment_item_choice_value {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) :
    Option (Fin n) → ℝ
  | none => 0
  | some j => c i j - μ j * a i

/-- Leaving item `i` unassigned contributes `0` to the capacity-relaxed objective. -/
@[simp] theorem generalized_assignment_item_choice_value_none {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) :
    generalized_assignment_item_choice_value a c μ i none = 0 :=
  rfl

/-- Assigning item `i` to machine `j` contributes the reduced profit `c_ij - μ_j a_i`. -/
@[simp] theorem generalized_assignment_item_choice_value_some {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    generalized_assignment_item_choice_value a c μ i (.some j) = c i j - μ j * a i :=
  rfl

-- Semantic recall note: `Real.sSup_empty` makes a bare `ℝ`-valued knapsack-value owner collapse
-- to `0` on empty block families, so only the knapsack-decomposition statement below keeps the
-- standing nonnegative-capacity hypothesis explicit.

/-- Exercise 8.6 (1). If one dualizes the capacity constraints of the generalized assignment
problem, then the resulting Lagrangian dual gives no better bound than the usual
linear-programming relaxation. -/
theorem exercise_8_6_capacity_relaxed_dual_eq_lp_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_dual_value a b c =
      generalized_assignment_lp_value a b c := sorry

/-- Exercise 8.6 (2). The dual obtained by dualizing the assignment constraints is at least as
strong as the dual obtained by dualizing the capacity constraints; as an upper bound for the
maximization problem, it is therefore smaller. -/
theorem exercise_8_6_assignment_relaxed_dual_le_capacity_relaxed_dual {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_assignment_relaxed_dual_value a b c ≤
      generalized_assignment_capacity_relaxed_dual_value a b c := sorry

/-- Exercise 8.6 (3). For fixed multipliers `λ`, assuming the machine capacities are
nonnegative so that each machine knapsack family contains the zero pattern, dualizing the
assignment constraints decomposes the relaxation into `n` independent `0`-`1` knapsack
subproblems, one for each machine `j`. -/
theorem exercise_8_6_assignment_relaxed_subproblems_are_knapsack {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ)
    (hb_nonneg : ∀ j, 0 ≤ b j) :
    generalized_assignment_assignment_relaxed_value a b c lam =
      (∑ i, lam i) +
        ∑ j,
          sSup
            ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
              generalized_assignment_block_patterns
                (generalized_assignment_capacity_coeffs a) b j) := sorry

/-- Exercise 8.6 (4). For fixed multipliers `μ`, dualizing the capacity constraints decomposes
the relaxation into `m` independent single-item choice problems: each item is either left
unassigned or sent to one machine with reduced profit `c_ij - μ_j a_i`. -/
theorem exercise_8_6_capacity_relaxed_subproblems_are_single_choice {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_value a b c μ =
      (∑ j, μ j * b j) +
        ∑ i,
          sSup
            ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
              Set.univ) := sorry

end Exercise86
