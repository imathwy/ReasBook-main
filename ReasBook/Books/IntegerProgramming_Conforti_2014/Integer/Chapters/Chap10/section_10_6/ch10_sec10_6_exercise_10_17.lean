import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped BigOperators

-- Primary domain: Lovasz-Schrijver `N₊` iterates for the Exercise 10.17 polytope.
-- Owner abstractions reused here:
-- * `lovasz_schrijver_N_plus` from Section 10.3 for the one-step PSD lift-and-project operator
-- * `zero_one_points` from Chapter 5 for the canonical `P ∩ {0,1}ⁿ` owner
-- * `Function.iterate` for the textbook iterates `N₊^k`

section Exercise1017

variable {n : ℕ}

/-- The polytope
`P = {x ∈ ℝ^n | ∑_{j ∈ J} x_j + ∑_{j ∉ J} (1 - x_j) ≥ 1 for all J ⊆ {1, …, n}}`
from Exercise 10.17, encoded by finite index sets `J : Finset (Fin n)`. -/
def exercise_10_17_polytope
    (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ J : Finset (Fin n),
      1 ≤
        Finset.sum J (fun j ↦ x j) +
          Finset.sum (Finset.univ \ J) (fun j ↦ (1 - x j))}

/-- Membership in `exercise_10_17_polytope n` means satisfying the subset inequality for every
`J : Finset (Fin n)`. -/
theorem mem_exercise_10_17_polytope_iff
    (n : ℕ)
    (x : Fin n → ℝ) :
    x ∈ exercise_10_17_polytope n ↔
      ∀ J : Finset (Fin n),
        1 ≤
          Finset.sum J (fun j ↦ x j) +
            Finset.sum (Finset.univ \ J) (fun j ↦ (1 - x j)) :=
  Iff.rfl

/-- The point `(1 / 2, …, 1 / 2)` in `ℝ^n`. -/
noncomputable def exercise_10_17_half_point
    (n : ℕ) : Fin n → ℝ :=
  fun _ ↦ 1 / 2

/-- Every coordinate of `exercise_10_17_half_point n` is `1 / 2`. -/
theorem exercise_10_17_half_point_apply
    (n : ℕ)
    (i : Fin n) :
    exercise_10_17_half_point n i = 1 / 2 :=
  rfl

/-- The zeroth positive-semidefinite Lovasz-Schrijver iterate of the Exercise 10.17 polytope is
the polytope itself. -/
theorem exercise_10_17_positive_semidefinite_iterate_zero
    (n : ℕ) :
    (lovasz_schrijver_N_plus^[0]) (exercise_10_17_polytope n) = exercise_10_17_polytope n := by
  simp

/-- The successor positive-semidefinite Lovasz-Schrijver iterate is obtained by applying one more
`N₊` step. -/
theorem exercise_10_17_positive_semidefinite_iterate_succ
    (n k : ℕ) :
    (lovasz_schrijver_N_plus^[k + 1]) (exercise_10_17_polytope n) =
      lovasz_schrijver_N_plus ((lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n)) := by
  simp [Function.iterate_succ_apply']

/-- Exercise 10.17 (1). For `n ≥ 2`, the point `(1 / 2, …, 1 / 2)` belongs to the
`(n - 1)`st positive-semidefinite Lovasz-Schrijver iterate `N₊^(n - 1)` of the Exercise 10.17
polytope. -/
theorem exercise_10_17_half_point_mem_positive_semidefinite_iterate
    (n : ℕ)
    (hn : 2 ≤ n) :
    exercise_10_17_half_point n ∈
      (lovasz_schrijver_N_plus^[n - 1]) (exercise_10_17_polytope n) := sorry

/-- Exercise 10.17 (2). For `n ≥ 2` and every `k < n`, the `k`th positive-semidefinite
Lovasz-Schrijver iterate `N₊^k` of the Exercise 10.17 polytope is not the convex hull of
`S = P ∩ {0,1}^n`. -/
theorem exercise_10_17_positive_semidefinite_iterate_ne_convexHull_zero_one_points
    (n k : ℕ)
    (hn : 2 ≤ n)
    (hk : k < n) :
    (lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n) ≠
      convexHull ℝ (zero_one_points (Nat.le_refl n) (exercise_10_17_polytope n)) := sorry

end Exercise1017
