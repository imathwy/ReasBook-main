import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_one_periodic_extension
import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27

-- Declarations for this item will be appended below by the statement pipeline.

section Example624

private noncomputable def example_6_24_pi_on_unit_interval (f : ℝ) : ℝ → ℝ :=
  fun u ↦
    if u ≤ 1 - f then
      u / (1 - f)
    else
      u / (2 - f)

/-- Example 6.24 (1). The discontinuous function from Fig. 6.9 is defined on `[0,1)` by the
displayed two-slope formula and extended to all real arguments by period `1`. -/
noncomputable def example_6_24_pi (f : ℝ) : ℝ → ℝ :=
  onePeriodicExtension (example_6_24_pi_on_unit_interval f)

/-- Unfolding formula for `example_6_24_pi`: the source piecewise expression is evaluated at
`Int.fract r` to produce the `1`-periodic extension. -/
theorem example_6_24_pi_apply (f r : ℝ) :
    example_6_24_pi f r =
      if Int.fract r ≤ 1 - f then
        Int.fract r / (1 - f)
      else
        Int.fract r / (2 - f) :=
  rfl

/-- On the fundamental interval `[0, 1)`, `example_6_24_pi` agrees with the displayed source
formula. -/
theorem example_6_24_pi_eq_on_Ico (f u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_24_pi f u =
      if u ≤ 1 - f then
        u / (1 - f)
      else
        u / (2 - f) := by
  simpa [example_6_24_pi, example_6_24_pi_on_unit_interval] using
    onePeriodicExtension_eq_on_Ico (example_6_24_pi_on_unit_interval f) hu0 hu1

/-- The function `example_6_24_pi f` has period `1`, matching the source's periodic extension. -/
theorem example_6_24_pi_periodic (f : ℝ) :
    Function.Periodic (example_6_24_pi f) 1 :=
  onePeriodicExtension_periodic _

/-- Example 6.24 (2). When the breakpoint `1 - f` lies in the fundamental interval `(0, 1)`, the
function from Fig. 6.9 is discontinuous there. -/
theorem example_6_24_pi_not_continuousAt
    {f : ℝ} (h_break : 1 - f ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ ContinuousAt (example_6_24_pi f) (1 - f) := sorry

/-- Example 6.24 (3). For `0 < 1 - f < 1/2`, the discontinuous two-slope function from Fig. 6.9
is a valid function for the one-dimensional pure integer infinite relaxation. -/
theorem example_6_24_pi_valid
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) :
    pure_integer_valid_function_on_R f (example_6_24_pi f) := sorry

/-- Under the source hypotheses of Example 6.24, `example_6_24_pi f` is available as a valid
function instance. -/
instance instExample624Valid
    {f : ℝ} [Fact (0 < 1 - f)] [Fact (1 - f < (1 : ℝ) / 2)] :
    pure_integer_valid_function_on_R f (example_6_24_pi f) :=
  example_6_24_pi_valid ‹Fact (0 < 1 - f)›.out ‹Fact (1 - f < (1 : ℝ) / 2)›.out

/-- Example 6.24 (4). For `0 < 1 - f < 1/2`, the discontinuous two-slope function from Fig. 6.9
is an extreme valid function for the one-dimensional pure integer infinite relaxation. -/
theorem example_6_24_pi_extreme
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) :
    pure_integer_extreme_valid_function_on_R f (example_6_24_pi f) := sorry

/-- Under the source hypotheses of Example 6.24, `example_6_24_pi f` is available as an extreme
valid function instance. -/
instance instExample624Extreme
    {f : ℝ} [Fact (0 < 1 - f)] [Fact (1 - f < (1 : ℝ) / 2)] :
    pure_integer_extreme_valid_function_on_R f (example_6_24_pi f) :=
  example_6_24_pi_extreme ‹Fact (0 < 1 - f)›.out ‹Fact (1 - f < (1 : ℝ) / 2)›.out

end Example624
