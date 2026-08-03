import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_2

open scoped BigOperators Matrix

-- This exercise reuses the Chapter 6.1 tableau-relaxation owner and keeps only the extra
-- exercise-specific data: integrality of the nonbasic block and the reduced-cost objective.
-- Semantic search note: no existing project/mathlib owner packages the Chapter 6.5 integer
-- tableau data, so this file keeps the tableau-level API and adds only a basis-attached Prop.
-- Domain sampling for this file:
-- * primary domain: tableau relaxations and attained objective-value sets
-- * core/canonical owners reused directly:
--   `rationalTableauCornerRelaxation`, `tableau_mixed_integer_lattice`, `IsGreatest`
-- * objective-value owner precedent inspected:
--   `primal_objective_values`, `sdp_primal_objective_values`

section Exercise65

variable {B N : Type} [Fintype N]

/-- The feasible region of the pure Gomory relaxation: the Chapter 6.1 tableau relaxation together
with integrality of the nonbasic block. -/
def pure_gomory_relaxation_feasible_region
    (abar : B → N → ℚ)
    (bbar : B → ℚ) : Set (Sum B N → ℝ) :=
  {x |
    x ∈ rationalTableauCornerRelaxation abar bbar ∧
      ∀ j : N, ∃ z : ℤ, x (Sum.inr j) = (z : ℝ)}

/-- The source-facing feasible region coincides with the Chapter 6.1 tableau relaxation together
with the mixed-integer lattice condition after swapping the basic and nonbasic summands. -/
theorem pure_gomory_relaxation_feasible_region_eq_inter_swap_mixed_integer_lattice
    (abar : B → N → ℚ)
    (bbar : B → ℚ) :
    pure_gomory_relaxation_feasible_region abar bbar =
      rationalTableauCornerRelaxation abar bbar ∩
        {x | x ∘ Sum.swap ∈ tableau_mixed_integer_lattice} := by
  ext x
  simp [pure_gomory_relaxation_feasible_region, Function.comp, tableau_mixed_integer_lattice]

/-- Membership in `pure_gomory_relaxation_feasible_region abar bbar` means belonging to the
tableau relaxation and having integral nonbasic coordinates. -/
@[simp] theorem mem_pure_gomory_relaxation_feasible_region_iff
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (x : Sum B N → ℝ) :
    x ∈ pure_gomory_relaxation_feasible_region abar bbar ↔
      x ∈ rationalTableauCornerRelaxation abar bbar ∧
        ∀ j : N, ∃ z : ℤ, x (Sum.inr j) = (z : ℝ) :=
  Iff.rfl

/-- The transformed objective value of a point in the Gomory relaxation, with the constant term
omitted so that only the reduced-cost contribution `-∑ j ∈ N, c̄_j x_j` remains. -/
noncomputable def pure_gomory_relaxation_objective
    (reducedCosts : N → ℚ)
    (x : Sum B N → ℝ) : ℝ :=
  -∑ j : N, (reducedCosts j : ℝ) * x (Sum.inr j)

/-- The transformed objective values attained on the pure Gomory relaxation feasible region. -/
noncomputable def pure_gomory_relaxation_objective_values
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    : Set ℝ :=
  pure_gomory_relaxation_objective reducedCosts '' pure_gomory_relaxation_feasible_region abar bbar

/-- Membership in `pure_gomory_relaxation_objective_values abar bbar reducedCosts` means that some
pure-Gomory-feasible point attains the value `r`. -/
theorem mem_pure_gomory_relaxation_objective_values_iff
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (r : ℝ) :
    r ∈ pure_gomory_relaxation_objective_values abar bbar reducedCosts ↔
      ∃ x : Sum B N → ℝ,
        x ∈ pure_gomory_relaxation_feasible_region abar bbar ∧
          pure_gomory_relaxation_objective reducedCosts x = r :=
  Iff.rfl

/-- A point of the pure Gomory relaxation is optimal when it is feasible and attains the greatest
transformed objective value. -/
class pure_gomory_relaxation_optimal_solution
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (x : Sum B N → ℝ) : Prop where
  feasible : x ∈ pure_gomory_relaxation_feasible_region abar bbar
  isGreatest :
    IsGreatest
      (pure_gomory_relaxation_objective_values abar bbar reducedCosts)
      (pure_gomory_relaxation_objective reducedCosts x)

/-- An optimal pure Gomory solution attains one of the recorded transformed objective values. -/
theorem pure_gomory_relaxation_optimal_solution.objective_mem
    {abar : B → N → ℚ}
    {bbar : B → ℚ}
    {reducedCosts : N → ℚ}
    {x : Sum B N → ℝ}
    (hx : pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x) :
    pure_gomory_relaxation_objective reducedCosts x ∈
      pure_gomory_relaxation_objective_values abar bbar reducedCosts :=
  hx.isGreatest.1

/-- Basis-level bookkeeping for Exercise 6.5: `Ā`, `b̄`, and `c̄_N` are the tableau and
reduced-cost data attached to the integer basis block `A_B`. The ambient linear-program data is
suppressed, but the source-required basis condition `det A_B ≠ 0` and the exported tableau-side
properties remain explicit. -/
class pure_gomory_basis_tableau_data
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ) : Prop where
  det_ne_zero : AB.det ≠ 0
  dual_feasible : ∀ j : N, 0 ≤ reducedCosts j
  det_clears_abar :
    ∀ i : B, ∀ j : N, ∃ z : ℤ, (Int.natAbs AB.det : ℚ) * abar i j = z
  det_clears_bbar :
    ∀ i : B, ∃ z : ℤ, (Int.natAbs AB.det : ℚ) * bbar i = z

/-- Helper for Exercise 6.5: once the tableau data `Ā`, `b̄`, and `c̄_N` are fixed together with
the determinant-clearing integrality consequences of the integer basis block `A_B`, the row bound
`b̄_i ≥ (D - 1) m_i` forces every optimal pure Gomory solution to have nonnegative basic
coordinates. -/
theorem pure_gomory_basic_coordinates_nonnegative_of_optimal_solution_of_basis_tableau_data
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (hbasis : pure_gomory_basis_tableau_data AB abar bbar reducedCosts)
    (rowMax : B → ℚ)
    (hrowMax :
      ∀ i : B,
        IsGreatest
          (Set.range (abar i))
          (rowMax i))
    (hbound :
      ∀ i : B,
        bbar i ≥ ((Int.natAbs AB.det : ℚ) - 1) * rowMax i) :
    ∀ x : Sum B N → ℝ,
      pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x →
        ∀ i : B, 0 ≤ x (Sum.inl i) := sorry

/-- Exercise 6.5. Consider a pure integer linear program
`max c x`, `A x = b`, `x_j ∈ ℤ≥0`, where the columns are partitioned as
`A = (A_B, A_N)` and `c = (c_B, c_N)`. Let `Ā = A_B⁻¹ A_N`,
`b̄ = A_B⁻¹ b`, and `c̄_N = c_B A_B⁻¹ A_N - c_N`, and assume the basis is dual feasible in the
sense that `c̄_N ≥ 0`. If `m_i = max_{j ∈ N} Ā i j` and
`b̄ i ≥ (|det A_B| - 1) m_i` for every basic index `i`, then every optimal solution of the
Gomory relaxation has nonnegative basic coordinates. -/
theorem exercise_6_5_basic_coordinates_nonnegative_of_optimal_gomory_relaxation
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (AN : Matrix B N ℤ)
    (b : B → ℤ)
    (cB : B → ℤ)
    (cN : N → ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (hdet : AB.det ≠ 0)
    (habar :
      abar =
        fun i j ↦
          (((AB.map (Int.castRingHom ℚ))⁻¹ * (AN.map (Int.castRingHom ℚ))) i j))
    (hbbar :
      bbar =
        fun i ↦
          (((AB.map (Int.castRingHom ℚ))⁻¹).mulVec (fun k ↦ (b k : ℚ)) i))
    (hdualFeasible :
      ∀ j : N,
        0 ≤
          (((fun i ↦ (cB i : ℚ)) ᵥ*
                (((AB.map (Int.castRingHom ℚ))⁻¹) * (AN.map (Int.castRingHom ℚ)))) j -
            (cN j : ℚ)))
    (rowMax : B → ℚ)
    (hrowMax :
      ∀ i : B,
        IsGreatest
          (Set.range (abar i))
          (rowMax i))
    (hbound :
      ∀ i : B,
        bbar i ≥ ((Int.natAbs AB.det : ℚ) - 1) * rowMax i) :
    ∀ x : Sum B N → ℝ,
      pure_gomory_relaxation_optimal_solution
          abar
          bbar
          (fun j ↦
            (((fun i ↦ (cB i : ℚ)) ᵥ*
                  (((AB.map (Int.castRingHom ℚ))⁻¹) * (AN.map (Int.castRingHom ℚ)))) j -
              (cN j : ℚ)))
          x →
        ∀ i : B, 0 ≤ x (Sum.inl i) := sorry

end Exercise65
