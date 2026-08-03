import Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_18
import Integer.Chapters.Chap08.section_8_3.ch8_sec8_3_theorem_8_18

-- This source-facing exercise reuses the Chapter 8 Benders owners
-- `benders_residual`/`benders_subproblem_feasible_set`/`benders_original_feasible_set`/
-- `benders_original_value`, together with the project finite-family extreme-ray owner
-- `IsExtremeRayRepresentativeFamily` built on `IsExtremeRayOfCone`.

open scoped Matrix

section Exercise818

variable {m n p : ℕ}

/-- The cone `C = {u ∈ ℝ^m_+ | u G ≥ 0}` that indexes the feasibility cuts in the Benders
reformulation of `A *ᵥ x + G *ᵥ y ≤ b`, `y ≥ 0`. -/
def benders_feasibility_cone
    (G : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {u | 0 ≤ u ∧ 0 ≤ u ᵥ* G}

/-- Membership in `benders_feasibility_cone G` is exactly the conjunction `u ≥ 0` and
`u ᵥ* G ≥ 0`. -/
theorem mem_benders_feasibility_cone_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (u : Fin m → ℝ) :
    u ∈ benders_feasibility_cone G ↔ 0 ≤ u ∧ 0 ≤ u ᵥ* G :=
  Iff.rfl

/-- The feasible `x`-region of the Benders reformulation cut out by the extreme-ray inequalities
`r^j (b - A x) ≥ 0`. -/
def benders_extreme_ray_reformulation_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : Set (Fin n → ℝ) :=
  X ∩ benders_feasibility_cut_set A b rays

/-- Membership in the extreme-ray reformulation feasible set means `x ∈ X` together with every
feasibility cut `r^j (b - A x) ≥ 0`. -/
theorem mem_benders_extreme_ray_reformulation_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_extreme_ray_reformulation_feasible_set A b X rays ↔
      x ∈ X ∧ ∀ j : Fin q, 0 ≤ rays j ⬝ᵥ benders_residual A b x := by
  simp [benders_extreme_ray_reformulation_feasible_set, mem_benders_feasibility_cut_set_iff]

/-- The value of the Benders reformulation obtained by maximizing `c x` over the extreme-ray
feasibility-cut region. -/
noncomputable def benders_extreme_ray_reformulation_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : ℝ :=
  sSup
    ((fun x : Fin n → ℝ ↦ c ⬝ᵥ x) ''
      benders_extreme_ray_reformulation_feasible_set A b X rays)

/-- Exercise 8.18. For the mixed problem
`z_I := max c x` subject to `A *ᵥ x + G *ᵥ y ≤ b`, `x ∈ X`, and `y ∈ ℝ^p_+`, if `rays`
is a finite representative family of the extreme rays of the cone
`C := {u ∈ ℝ^m_+ | u ᵥ* G ≥ 0}`, then its Benders reformulation is the problem
`max c x` over `x ∈ X` subject to the feasibility cuts `r^j (b - A x) ≥ 0`. -/
theorem benders_original_value_eq_extreme_ray_reformulation_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamily (benders_feasibility_cone G) rays) :
    benders_original_value A G b X c 0 =
      benders_extreme_ray_reformulation_value A b X c rays := sorry

end Exercise818
