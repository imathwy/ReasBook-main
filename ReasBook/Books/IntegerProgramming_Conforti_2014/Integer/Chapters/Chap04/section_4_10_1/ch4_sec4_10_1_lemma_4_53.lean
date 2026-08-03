import Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2
import Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_theorem_4_51
import Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_1

open scoped Matrix NonnegativeRankNotation

/-!
Domain-style sampling for this refine pass:
* primary domain: extension complexity via slack matrices, nonnegative rank, and rectangle covers
* source-facing owners inspected: `polyhedron_le_set`, `linear_extended_system`, `slack_matrix`
* core/canonical owner theorem reused here:
  `nonnegative_rank_le_extended_formulation_constraint_count`
* bridge/view theorem added here: `rectangle_covering_number_le_nonnegative_rank`

This file operates at the `bridge/view` layer: Lemma 4.53 is the rectangle-covering corollary of
the chapter's canonical nonnegative-rank lower bound for extended formulations.
-/

/-- A nonnegative matrix has rectangle covering number at most its nonnegative rank. -/
theorem rectangle_covering_number_le_nonnegative_rank
    {m n : Type*} [Finite m] [Finite n]
    (S : Matrix.Nonnegative m n ℝ) :
    rectangle_covering_number (S : Matrix m n ℝ) ≤ rank₊ S := sorry

/-- Lemma 4.53. Let `P ⊆ ℝ^n` be a polytope. Every extended formulation of `P` has a number of
constraints at least equal to the rectangle covering number of the slack matrix of any system of
linear inequalities describing `P`. -/
theorem rectangle_covering_number_le_extended_formulation_constraint_count
    {m n p : ℕ}
    {ρ σ κ : Type*}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b)
    (hEF : P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq) :
    rectangle_covering_number (slack_matrix A b vertices) ≤ Fintype.card ρ + Fintype.card σ := by
  let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
  let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
    ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
  have hrect : rectangle_covering_number (slack_matrix A b vertices) ≤ rank₊ S :=
    rectangle_covering_number_le_nonnegative_rank S
  have hnr : rank₊ S ≤ Fintype.card ρ + Fintype.card σ := by
    simpa [S, hvertices] using
      nonnegative_rank_le_extended_formulation_constraint_count
        P A b vertices Aeq Beq beq Aineq Bineq bineq hP_vertices hP_system hEF
  exact hrect.trans hnr
