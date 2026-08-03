import Integer.Chapters.Chap08.section_8_3.ch8_sec8_3_theorem_8_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic recall note: the residual map `benders_residual` for the right-hand side `b - A x`
-- is already owned by Chapter 8 Theorem 8.18, so this file reuses that canonical declaration and
-- adds only the equality-constrained Benders layer specific to Exercise 8.16.

section Exercise816

variable {m n p : ℕ}
variable {K J : Type}

/-- The equality-constrained Benders subproblem feasible set
`{y | G y = rhs, y ≥ 0}` for a fixed right-hand side `rhs`. -/
def benders_equality_subproblem_feasible_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ) : Set (Fin p → ℝ) :=
  {y | G *ᵥ y = rhs ∧ ∀ i, 0 ≤ y i}

/-- Membership in the equality-constrained Benders subproblem feasible set is exactly the system
`G y = rhs` together with nonnegativity of `y`. -/
theorem mem_benders_equality_subproblem_feasible_set_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ benders_equality_subproblem_feasible_set G rhs ↔
      G *ᵥ y = rhs ∧ ∀ i, 0 ≤ y i := Iff.rfl

/-- The equality-constrained Benders subproblem is the ordinary Chapter 8 Benders subproblem
together with the reverse inequality `rhs ≤ G *ᵥ y`. -/
theorem mem_benders_equality_subproblem_feasible_set_iff_mem_benders_subproblem_feasible_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ benders_equality_subproblem_feasible_set G rhs ↔
      y ∈ benders_subproblem_feasible_set G rhs ∧ rhs ≤ G *ᵥ y := by
  constructor
  · intro hy
    exact ⟨⟨hy.1.le, hy.2⟩, hy.1.ge⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨le_antisymm hy.1 hy', hy.2⟩

/-- The `x`-projection of the mixed system `A x + G y = b`, `y ≥ 0`, encoded as existence of an
equality-constrained Benders subproblem solution after fixing `x`. -/
def benders_equality_projection_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ y, y ∈ benders_equality_subproblem_feasible_set G (benders_residual A b x)}

/-- Membership in the equality-constrained `x`-projection means that there exists a nonnegative
vector `y` satisfying `G y = b - A x`. -/
theorem mem_benders_equality_projection_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_equality_projection_set A G b ↔
      ∃ y : Fin p → ℝ,
        y ∈
          benders_equality_subproblem_feasible_set G
            (benders_residual A b x) := Iff.rfl

/-- Every `x` feasible for the equality-constrained Benders projection is feasible for the
ordinary inequality-constrained projection. -/
theorem benders_equality_projection_set_subset
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    benders_equality_projection_set A G b ⊆ benders_projection_set A G b := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  exact ⟨y, (mem_benders_equality_subproblem_feasible_set_iff_mem_benders_subproblem_feasible_set
    G (benders_residual A b x) y).mp hy |>.1⟩

/-- The optimal value `z_LP(x)` of the equality-constrained Benders subproblem with right-hand
side `rhs`. -/
noncomputable def benders_equality_subproblem_value
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) : ℝ :=
  sSup ((fun y : Fin p → ℝ ↦ h ⬝ᵥ y) '' benders_equality_subproblem_feasible_set G rhs)

/-- The feasible set of the mixed problem obtained from (8.26) by replacing `A x + G y ≤ b` by
`A x + G y = b`, with the master variable restricted to `X`. -/
def benders_equality_original_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × (Fin p → ℝ)) :=
  {xy | xy.1 ∈ X ∧
      xy.2 ∈ benders_equality_subproblem_feasible_set G (benders_residual A b xy.1)}

/-- Membership in the equality-constrained original feasible set means `x ∈ X` and `y` solves the
subproblem with equality right-hand side `b - A x`. -/
theorem mem_benders_equality_original_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (Fin p → ℝ)) :
    xy ∈ benders_equality_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        xy.2 ∈
          benders_equality_subproblem_feasible_set G
            (benders_residual A b xy.1) := Iff.rfl

/-- Every feasible pair for the equality-constrained mixed problem is feasible for the ordinary
mixed problem with inequalities. -/
theorem benders_equality_original_feasible_set_subset
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ)) :
    benders_equality_original_feasible_set A G b X ⊆ benders_original_feasible_set A G b X := by
  intro xy hxy
  refine ⟨hxy.1, ?_⟩
  exact (mem_benders_equality_subproblem_feasible_set_iff_mem_benders_subproblem_feasible_set
    G (benders_residual A b xy.1) xy.2).mp hxy.2 |>.1

/-- The source value `z_I` of the equality-constrained mixed problem obtained from (8.26),
namely the maximum of `c x + h y` over feasible pairs `(x, y)` satisfying `A x + G y = b`. -/
noncomputable def benders_equality_original_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ) : ℝ :=
  sSup
    ((fun xy : (Fin n → ℝ) × (Fin p → ℝ) ↦ c ⬝ᵥ xy.1 + h ⬝ᵥ xy.2) ''
      benders_equality_original_feasible_set A G b X)

/-- Exercise 8.16. If the mixed problem (8.26) uses equality constraints `A x + G y = b` instead
of inequalities `A x + G y ≤ b`, then Theorem 8.18 is modified by replacing the Benders
subproblem, its feasible `x`-projection, and the original objective value by their
equality-constrained analogues; under the corresponding feasibility-cut and optimality-cut
hypotheses, the same Benders master value formula remains valid. The proof is modified only by
making those replacements throughout. -/
theorem benders_equality_original_value_eq_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (hproj :
      benders_equality_projection_set A G b =
        benders_feasibility_cut_set A b r)
    (hsubproblem :
      ∀ x : Fin n → ℝ,
        x ∈ benders_equality_projection_set A G b →
          benders_equality_subproblem_value G h (benders_residual A b x) =
            benders_optimality_cut_value A b u x) :
    benders_equality_original_value A G b X c h =
      benders_master_value A b X u r c := sorry

end Exercise816
