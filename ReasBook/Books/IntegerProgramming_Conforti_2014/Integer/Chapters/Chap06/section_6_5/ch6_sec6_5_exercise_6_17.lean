import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1
import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27
import Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, so this file reuses the
-- Chapter 6 symmetry owner `satisfies_symmetry_condition`, the chapter's one-dimensional
-- piecewise-linear owner, and the Chapter 6 subadditivity owner `Function.Subadditive`.

section Exercise617

/-- In dimension `q = 1`, the Chapter 6 symmetry owner is exactly the scalar relation
`π(r) + π(-f-r) = 1`. -/
theorem satisfies_symmetry_condition_real_iff {f : ℝ} {π : ℝ → ℝ} :
    satisfies_symmetry_condition (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0)) ↔
      ∀ r : ℝ, π r + π (-f - r) = 1 := by
  constructor
  · intro h r
    simpa using h (fun _ ↦ r)
  · intro h r
    simpa using h (r 0)

/-- `LocallyConvexAt π x` means that `π` is convex on some convex neighborhood of `x`. -/
def LocallyConvexAt (π : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧ ConvexOn ℝ s π

/-- Unfolding lemma for `LocallyConvexAt`. -/
theorem locallyConvexAt_iff {π : ℝ → ℝ} {x : ℝ} :
    LocallyConvexAt π x ↔
      ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧ ConvexOn ℝ s π :=
  Iff.rfl

variable {f : ℝ} {π : ℝ → ℝ}

/-- Exercise 6.17 (1). For a continuous periodic function `π : ℝ → ℝ` that is piecewise-linear
on `[0, 1]`, it suffices to verify the symmetry condition at the breakpoints in `[0, 1]`. The
source also states nonnegativity and `π 0 = 0`, but the criterion itself does not use them. -/
theorem exercise_6_17_symmetry_check_on_breakpoints_suffices
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm_breakpoints : ∀ ⦃r : ℝ⦄, r ∈ hpiece.breakpoints → π r + π (-f - r) = 1) :
    ∀ r : ℝ, π r + π (-f - r) = 1 := sorry

/-- Exercise 6.17 (2). Assume in addition that `π` satisfies the Chapter 6 symmetry condition,
equivalently `π(r) + π(-f-r) = 1` for every real `r`. Then, to check subadditivity, it is enough
to verify `π(a + b) ≤ π(a) + π(b)` at breakpoint pairs `a, b ∈ [0, 1]` for which `π` is locally
convex at both breakpoints. The source also states nonnegativity and `π 0 = 0`, but this
criterion itself does not use them. -/
theorem exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    (h_subadd_breakpoints :
      ∀ ⦃a b : ℝ⦄, a ∈ hpiece.breakpoints → b ∈ hpiece.breakpoints →
        LocallyConvexAt π a → LocallyConvexAt π b → π (a + b) ≤ π a + π b) :
    π.Subadditive := sorry

end Exercise617
