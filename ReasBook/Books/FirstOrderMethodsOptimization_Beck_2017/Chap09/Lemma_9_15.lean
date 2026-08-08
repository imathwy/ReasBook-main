import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {ι : Type*} [Fintype ι]

/-
Domain sampling for Lemma 9.15 uses the existing optimization owner `IsMinOn` from mathlib and
the nearby project pattern of a concrete objective together with atomic minimizer/value lemmas, as
in `finite_intersection_orthogonal_projection_isMinOn` with its direct quadratic objective surface
and the canonical Chapter 8 argmin owner applied to
`polytope_quadratic_vertex_linear_objective`.

This item is `source-facing`: it introduces the fixed-iteration ratio objective and the constant
step family singled out by the textbook. The primitive data are the coefficients `α`, `β`, the
finite index family of steps, and the step family itself. The `core/canonical` owner for the
finite aggregation is therefore an arbitrary `Fintype`-indexed family `ι → ℝ`; the textbook
`m`-step presentation is the specialization `ι = Fin m`, not a second owner. Positivity of the
uniform family and its minimizing property are derived API, so they are stated as separate
theorems rather than bundled into one conjunction. -/

/-- The objective function in the fixed-iteration step-size optimization problem. -/
noncomputable def fixed_iteration_objective (α β : ℝ) (t : ι → ℝ) : ℝ :=
  (α + β * ∑ k, (t k) ^ 2) / ∑ k, t k

/-- The constant step family `t_i = √(α / (β |ι|))` from Lemma 9.15. -/
noncomputable def fixed_iteration_uniform_steps (ι : Type*) [Fintype ι] (α β : ℝ) : ι → ℝ :=
  fun _ ↦ Real.sqrt (α / (β * Fintype.card ι))

-- Proof sketch: unfold `fixed_iteration_uniform_steps`; every coordinate is definitionally the
-- same constant `√(α / (β |ι|))`.
/-- Evaluating `fixed_iteration_uniform_steps α β` at any index gives `√(α / (β |ι|))`. -/
@[simp] theorem fixed_iteration_uniform_steps_apply
    (α β : ℝ) (i : ι) :
    fixed_iteration_uniform_steps ι α β i = Real.sqrt (α / (β * Fintype.card ι)) := sorry

-- Proof sketch: use `hα`, `hβ`, and finiteness with `Nonempty ι` to show
-- `α / (β |ι|)` is positive and apply the positivity of `Real.sqrt`.
/-- The constant step family from Lemma 9.15 is positive coordinatewise when `α` and `β`
are positive. -/
theorem fixed_iteration_uniform_steps_pos
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ i : ι, 0 < fixed_iteration_uniform_steps ι α β i := sorry

-- Proof sketch: use permutation symmetry to reduce to equal coordinates, then solve the
-- resulting one-variable minimization problem on the positive half-line.
/-- Lemma 9.15: for positive `α` and `β`, the ratio
\[
\frac{\alpha + \beta \sum_{i \in ι} t_i^2}{\sum_{i \in ι} t_i}
\]
is minimized over positive step sizes by the constant choice
`t_i = √(α / (β |ι|))`. Specializing to `ι = Fin m` recovers the textbook `m`-step statement. -/
theorem fixed_iteration_objective_minimized_by_uniform_steps
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsMinOn (fixed_iteration_objective α β)
      {t : ι → ℝ | ∀ i, 0 < t i}
      (fixed_iteration_uniform_steps ι α β) := sorry

-- Proof sketch: evaluate the objective on the constant minimizer and simplify the resulting
-- finite sums to obtain the closed-form value.
/-- The uniform minimizer of `fixed_iteration_objective` attains the value
`2 * √(α * β / |ι|)`. -/
theorem fixed_iteration_objective_uniform_step_value
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    fixed_iteration_objective α β (fixed_iteration_uniform_steps ι α β) =
      2 * Real.sqrt (α * β / Fintype.card ι) := sorry

end
