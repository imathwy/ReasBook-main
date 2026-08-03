import Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2
import Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1
import Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Exercise619

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

-- This exercise reuses the generic `ℤ_+^q` owner and `is_nonnegative_integer_free` predicate
-- from Exercise 6.14.

/-- The set `B_ψ = {x ∈ ℝ^q | ψ (x - f) ≤ 1}` from Exercise 6.19, expressed as the `f`-translate
of the canonical unit sublevel set of `ψ`. -/
def exercise_6_19_level_set (f : Rq) (ψ : Rq → ℝ) : Set Rq :=
  {x | x - f ∈ sublinear_unit_sublevel_set ψ}

/-- Membership in `exercise_6_19_level_set f ψ` is exactly the defining inequality
`ψ (x - f) ≤ 1`. -/
theorem mem_exercise_6_19_level_set_iff {f : Rq} {ψ : Rq → ℝ} {x : Rq} :
    x ∈ exercise_6_19_level_set f ψ ↔ ψ (x - f) ≤ 1 := sorry

/-- Exercise 6.19 (1). If `ψ : ℝ^q → ℝ` is sublinear and
`B_ψ = {x ∈ ℝ^q | ψ (x - f) ≤ 1}` is `ℤ_+^q`-free, then `ψ` is valid for the continuous infinite
relaxation with right-hand side `f`. -/
theorem exercise_6_19_valid_of_sublinear_of_level_set_free
    (f : Rq) (ψ : Rq → ℝ)
    (hψ_sublinear : ψ.Sublinear)
    (hBψ_free : is_nonnegative_integer_free (exercise_6_19_level_set f ψ)) :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ := sorry

/-- The right-hand side `f = (1/4, 1/2)` from part (b) of Exercise 6.19. -/
noncomputable def exercise_6_19_f : Fin 2 → ℝ :=
  ![(1 / 4 : ℝ), (1 / 2 : ℝ)]

/-- `exercise_6_19_f` is the vector `(1/4, 1/2)` in `ℝ²`. -/
theorem exercise_6_19_f_eq :
    exercise_6_19_f = ![(1 / 4 : ℝ), (1 / 2 : ℝ)] := sorry

/-- The function `ψ(r) = max {4 r₁ + 4 r₂, 4 r₁ - 4 r₂}` from part (b) of Exercise 6.19. -/
def exercise_6_19_explicit_psi : (Fin 2 → ℝ) → ℝ :=
  fun r ↦ max ((4 : ℝ) * r 0 + (4 : ℝ) * r 1) ((4 : ℝ) * r 0 - (4 : ℝ) * r 1)

/-- `exercise_6_19_explicit_psi` evaluates to `max {4 r₁ + 4 r₂, 4 r₁ - 4 r₂}`. -/
theorem exercise_6_19_explicit_psi_apply (r : Fin 2 → ℝ) :
    exercise_6_19_explicit_psi r =
      max ((4 : ℝ) * r 0 + (4 : ℝ) * r 1) ((4 : ℝ) * r 0 - (4 : ℝ) * r 1) := sorry

/-- The set `B_ψ` attached to the explicit function from part (b) of Exercise 6.19. -/
def exercise_6_19_explicit_level_set : Set (Fin 2 → ℝ) :=
  exercise_6_19_level_set exercise_6_19_f exercise_6_19_explicit_psi

/-- Membership in `exercise_6_19_explicit_level_set` is exactly the inequality defining the
explicit `B_ψ` from Exercise 6.19. -/
theorem mem_exercise_6_19_explicit_level_set_iff {x : Fin 2 → ℝ} :
    x ∈ exercise_6_19_explicit_level_set ↔
      exercise_6_19_explicit_psi (x - exercise_6_19_f) ≤ 1 := sorry

/-- The explicit function from part (b) of Exercise 6.19 is sublinear. -/
theorem exercise_6_19_explicit_psi_sublinear :
    exercise_6_19_explicit_psi.Sublinear := sorry

/-- The explicit set `B_ψ` from part (b) of Exercise 6.19 is `ℤ_+^2`-free. -/
theorem exercise_6_19_explicit_level_set_free :
    is_nonnegative_integer_free exercise_6_19_explicit_level_set := sorry

/-- Exercise 6.19 (2). For `q = 2`, `f = (1/4, 1/2)`, and
`ψ(r) = max {4 r₁ + 4 r₂, 4 r₁ - 4 r₂}`, the function `ψ` is valid for the continuous infinite
relaxation. -/
theorem exercise_6_19_explicit_psi_valid :
    IsValidFunctionForContinuousInfiniteRelaxation
      exercise_6_19_f exercise_6_19_explicit_psi := sorry

end Exercise619
