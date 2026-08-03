import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27
import Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: this file keeps the source-facing one-dimensional formulas on `ℝ` and
-- uses the Section 6.3.1 and Section 6.3.4 one-dimensional `...OnR` owners directly rather than
-- exposing the underlying `q = 1` bridge inline.

noncomputable section

section Example637

/-- The translated interval `B - f = [-f, 1 - f]` from Example 6.37, viewed on `ℝ`. -/
def example_6_37_shifted_interval (f : ℚ) : Set ℝ :=
  Set.Icc (-(f : ℝ)) (1 - (f : ℝ))

/-- `example_6_37_shifted_interval f` is the translate of `B = [0,1]` by `-f`, written as the
displayed interval condition on `ℝ`. -/
theorem example_6_37_shifted_interval_eq
    (f : ℚ) :
    example_6_37_shifted_interval f =
      {r : ℝ | 0 ≤ r + (f : ℝ) ∧ r + (f : ℝ) ≤ 1} := by
  ext r
  constructor
  · rintro ⟨hleft, hright⟩
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    constructor <;> linarith

/-- The gauge formula `ψ(r) = max {r / (1 - f), -r / f}` from Example 6.37, written on `ℝ`. -/
def example_6_37_psi (f : ℚ) : ℝ → ℝ :=
  fun r ↦ max (r / (1 - (f : ℝ))) (-r / (f : ℝ))

/-- Expanding `example_6_37_psi f` recovers the displayed maximum formula from Example 6.37. -/
@[simp] theorem example_6_37_psi_apply
    (f : ℚ)
    (r : ℝ) :
    example_6_37_psi f r = max (r / (1 - (f : ℝ))) (-r / (f : ℝ)) :=
  rfl

/-- The trivial lifting `π̄` from Example 6.37, written as the displayed piecewise formula on the
fractional part of a real argument. -/
def example_6_37_bar_pi (f : ℚ) : ℝ → ℝ :=
  fun r ↦
    let u : ℝ := r - (Int.floor r : ℝ)
    if u ≤ 1 - (f : ℝ) then
      u / (1 - (f : ℝ))
    else
      ((Int.ceil r : ℝ) - r) / (f : ℝ)

/-- Expanding `example_6_37_bar_pi f` recovers the displayed floor/ceiling formula for the
trivial lifting `π̄` in Example 6.37. -/
@[simp] theorem example_6_37_bar_pi_apply
    (f : ℚ)
    (r : ℝ) :
    example_6_37_bar_pi f r =
      let u : ℝ := r - (Int.floor r : ℝ)
      if u ≤ 1 - (f : ℝ) then
        u / (1 - (f : ℝ))
      else
        ((Int.ceil r : ℝ) - r) / (f : ℝ) :=
  rfl

/-- Example 6.37 (1). For `q = 1`, `0 < f < 1`, and `B = [0,1]`, if `ψ` is the gauge of `B - f`,
then the explicit function `example_6_37_psi f` agrees with that gauge. -/
theorem example_6_37_psi_eq_gauge
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_37_psi f = gauge (example_6_37_shifted_interval f) := sorry

/-- Example 6.37 (2). For the same one-dimensional set, the trivial lifting `π̄` is the
displayed piecewise floor/ceiling formula, viewed through the canonical one-dimensional lifting
owner on `ℝ`. -/
theorem example_6_37_bar_pi_eq_trivial_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_37_bar_pi f = trivial_lifting_on_R (example_6_37_psi f) := sorry

/-- Example 6.37 (3). The one-dimensional trivial lifting `π̄` is a minimal valid function for
the pure-integer infinite relaxation `G_f`, stated in the repository's canonical `q = 1` owner
on `ℝ`. -/
theorem example_6_37_bar_pi_is_minimal_valid_pure_integer_function
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    pure_integer_minimal_valid_function_on_R (f : ℝ) (example_6_37_bar_pi f) := sorry

/-- Under the source hypotheses of Example 6.37, `example_6_37_bar_pi f` is available through the
canonical one-dimensional pure-integer minimal-valid-function instance. -/
instance instExample637BarPiMinimalValidPureIntegerFunction
    {f : ℚ} [Fact (0 < f)] [Fact (f < 1)] :
    pure_integer_minimal_valid_function_on_R (f : ℝ) (example_6_37_bar_pi f) :=
  example_6_37_bar_pi_is_minimal_valid_pure_integer_function
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- Example 6.37 (4). The same function `π̄` is a minimal lifting of `ψ`, viewed through the
canonical one-dimensional lifting owner on `ℝ`. -/
theorem example_6_37_bar_pi_is_minimal_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    IsMinimalLiftingOfOnR (f : ℝ) (example_6_37_bar_pi f) (example_6_37_psi f) := sorry

/-- Under the source hypotheses of Example 6.37, `example_6_37_bar_pi f` is available through the
canonical minimal-lifting instance on `ℝ`. -/
instance instExample637BarPiMinimalLifting
    {f : ℚ} [Fact (0 < f)] [Fact (f < 1)] :
    IsMinimalLiftingOfOnR (f : ℝ) (example_6_37_bar_pi f) (example_6_37_psi f) :=
  example_6_37_bar_pi_is_minimal_lifting
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- Example 6.37 (5). In this one-dimensional case, `π̄` is the unique minimal lifting of `ψ`;
equivalently, every minimal lifting of `ψ` on `ℝ` is equal to `π̄`. -/
theorem example_6_37_eq_bar_pi_of_minimal_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {π : ℝ → ℝ}
    (hπ : IsMinimalLiftingOfOnR (f : ℝ) π (example_6_37_psi f)) :
    π = example_6_37_bar_pi f := sorry

end Example637
