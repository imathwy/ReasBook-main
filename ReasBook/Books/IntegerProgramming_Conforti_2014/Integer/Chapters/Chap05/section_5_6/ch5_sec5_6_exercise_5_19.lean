import Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped BigOperators Matrix

-- Primary domain: Chapter 5 Chvatal closures and Chvatal rank in `Fin n → ℝ`.
-- Core/canonical owners sampled upstream: `is_valid_inequality`,
-- `pure_integer_chvatal_closure`, `(pure_integer_chvatal_closure^[t]) P`, and
-- `is_iterate_rank_of_inequality`.
-- Primitive source-facing data kept here: the explicit Exercise 5.19 polyhedron.
-- Derived API kept here: the subset-sum relaxation, the iterate comparison theorem, and the
-- source-facing rank bounds.
-- The all-ones coefficient vector is expressed directly as `(1 : Fin n → ℝ)`, rather than by a
-- parallel local alias.
-- Semantic recall note: `lean_leansearch` returned no relevant Chvatal-rank API for this
-- exercise, so this file uses the local Chapter 5 owners directly.

section Exercise519

variable {n : ℕ}

/-- The polyhedron
`P = {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}`
from Exercise 5.19. -/
def exercise_5_19_polyhedron (n : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ ⦃i j : Fin n⦄, i < j → x i + x j ≤ 1}

/-- Membership in `exercise_5_19_polyhedron n` is exactly nonnegativity together with the
pairwise inequalities `x_i + x_j ≤ 1` for `i < j`. -/
theorem mem_exercise_5_19_polyhedron_iff
    {x : Fin n → ℝ} :
    x ∈ exercise_5_19_polyhedron n ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ ⦃i j : Fin n⦄, i < j → x i + x j ≤ 1 :=
  Iff.rfl

/-- The source-facing threshold subset-sum relaxation appearing in the positive Chvátal iterates
of Exercise 5.19. At stage `t`, the active subset size is `min(n, 2^t + 1)`. -/
def exercise_5_19_subset_sum_relaxation (n t : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ I : Finset (Fin n),
        I.card = Nat.min n (2 ^ t + 1) → I.sum x ≤ 1}

/-- Membership in `exercise_5_19_subset_sum_relaxation n t` is exactly nonnegativity together
with the threshold subset-sum bounds `∑_{i ∈ I} x_i ≤ 1` for all subsets of cardinality
`min(n, 2^t + 1)`. -/
theorem mem_exercise_5_19_subset_sum_relaxation_iff
    {t : ℕ}
    {x : Fin n → ℝ} :
    x ∈ exercise_5_19_subset_sum_relaxation n t ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ I : Finset (Fin n),
          I.card = Nat.min n (2 ^ t + 1) → I.sum x ≤ 1 :=
  Iff.rfl

/-- Validity of the all-ones coefficient vector with right-hand side `1` is exactly the textbook
inequality `∑_{j=1}^n x_j ≤ 1`. -/
theorem exercise_5_19_sum_le_one_valid_iff
    {Q : Set (Fin n → ℝ)} :
    is_valid_inequality Q (1 : Fin n → ℝ) 1 ↔
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ Q → ∑ j : Fin n, x j ≤ 1 := by
  simp [is_valid_inequality, one_dotProduct]

/-- For Exercise 5.19, when `n ≥ 3`, the positive Chvátal iterates of `P` are exactly the
corresponding threshold subset-sum relaxations. -/
theorem exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation
    (hn : 3 ≤ n) (t : ℕ) :
    (pure_integer_chvatal_closure^[t + 1]) (exercise_5_19_polyhedron n) =
      exercise_5_19_subset_sum_relaxation n (t + 1) := sorry

/-- When `n ≥ 3`, membership in the positive Chvátal iterates of `P` is described by
nonnegativity together with the threshold subset-sum bounds
`∑_{i ∈ I} x_i ≤ 1` for all subsets `I` of cardinality `min(n, 2^(t + 1) + 1)`. -/
theorem mem_exercise_5_19_chvatal_iterate_succ_iff
    (hn : 3 ≤ n)
    {t : ℕ}
    {x : Fin n → ℝ} :
    x ∈ (pure_integer_chvatal_closure^[t + 1]) (exercise_5_19_polyhedron n) ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ I : Finset (Fin n),
          I.card = Nat.min n (2 ^ (t + 1) + 1) → I.sum x ≤ 1 := by
  rw [exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation hn t]
  rfl

/-- Helper for Exercise 5.19: on every positive stage, the constant witness with denominator
`2^(t + 1) - 1` survives in the `t`-th subset-sum relaxation. -/
lemma exercise_5_19_uniformWitness_mem_subset_sum_relaxation
    {t : ℕ} (ht : 1 ≤ t) :
    (fun _ : Fin n ↦ (1 : ℝ) / ((2 ^ (t + 1) - 1 : ℕ) : ℝ)) ∈
      exercise_5_19_subset_sum_relaxation n t := sorry

/-- Helper for Exercise 5.19: on the source branch `n ≥ 3`, the all-ones inequality is already
valid on the `(Nat.log 2 n + 1)`-st Chvátal iterate. -/
theorem exercise_5_19_sum_le_one_valid_on_logIterate
    (hn : 3 ≤ n) :
    is_valid_inequality
      ((pure_integer_chvatal_closure^[Nat.log 2 n + 1]) (exercise_5_19_polyhedron n))
      (1 : Fin n → ℝ) 1 := sorry

/-- Exercise 5.19 (1). For
`P := {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` and
`S = P ∩ {0,1}^n`, if the inequality `∑_{j=1}^n x_j ≤ 1` has Chvatal rank `k`, then
`⌊log₂ n⌋ ≤ k` for `n ≥ 3`. -/
theorem exercise_5_19_sum_le_one_chvatal_rank_lower_bound
    (hn : 3 ≤ n)
    {k : ℕ}
    (hk : is_iterate_rank_of_inequality pure_integer_chvatal_closure
      (exercise_5_19_polyhedron n) (1 : Fin n → ℝ) 1 k) :
    Nat.log 2 n ≤ k := sorry

/-- Exercise 5.19 (2). For
`P := {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` and
`S = P ∩ {0,1}^n`, if the inequality `∑_{j=1}^n x_j ≤ 1` has Chvatal rank `k`, then
`k ≤ ⌊log₂ n⌋ + 1`. -/
theorem exercise_5_19_sum_le_one_chvatal_rank_upper_bound
    {k : ℕ}
    (hk : is_iterate_rank_of_inequality pure_integer_chvatal_closure
      (exercise_5_19_polyhedron n) (1 : Fin n → ℝ) 1 k) :
    k ≤ Nat.log 2 n + 1 := sorry

end Exercise519
