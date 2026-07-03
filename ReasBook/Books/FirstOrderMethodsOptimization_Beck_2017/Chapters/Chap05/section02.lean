

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_2 (from Chap05) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 5.2 is a `bridge/view` item in the chapter smoothness API: the owner predicate
`is_l_smooth_on` is already defined in Definition 5.1, and this file only records the textbook
`C^{1,1}` notation by specializing that owner predicate to the whole space. -/

/-- The notation `C^{1,1}` is represented by the existence of some global smoothness parameter
`L ≥ 0`. -/
def is_c11 (f : E → ℝ) : Prop :=
  ∃ L : NNReal, is_l_smooth_on f Set.univ L

end

/-! ### Proposition_5_2 (from Chap05) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 5.2 is `source-facing`: the mathematical object is the affine functional
`x ↦ b x + c`. The `core/canonical` owners already live upstream as Chapter 5's
`is_l_smooth_on` and mathlib's calculus API for continuous linear maps, so the derivative field is
derived directly from `ContinuousLinearMap.fderiv` and `fderiv_add_const` rather than through any
local wrapper. -/

-- Proof sketch: the Fréchet derivative of `x ↦ b x + c` is the constant map `fun _ ↦ b`, so the
-- derivative field is `0`-Lipschitz on `Set.univ`; differentiability at every point follows from
-- the standard derivative formula for continuous linear maps and addition of a constant.
/-- Proposition 5.2: every affine functional `x ↦ b x + c` on a real normed space is globally
`0`-smooth. -/
theorem is_l_smooth_affine_functional (b : E →L[ℝ] ℝ) (c : ℝ) :
    is_l_smooth_on (fun x ↦ b x + c) Set.univ 0 := by
  rw [is_l_smooth_on_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact b.differentiableAt.add_const c
  · intro x hx y hy
    simp

end
