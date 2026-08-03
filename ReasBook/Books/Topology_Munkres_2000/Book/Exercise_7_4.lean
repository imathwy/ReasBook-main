module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Real.Cardinality

public section

/- Exercise 7.4 (a): A real number is algebraic over `ℚ` when it satisfies a
nonzero polynomial equation with rational coefficients. -/
#check (IsAlgebraic ℚ : ℝ → Prop)

/- Exercise 7.4 (a): The set of real numbers algebraic over `ℚ` is countable. -/
#check (Algebraic.countable ℚ ℝ : {x : ℝ | IsAlgebraic ℚ x}.Countable)

/- Exercise 7.4 (b): A real number is transcendental over `ℚ` when it is not
algebraic over `ℚ`. -/
#check (Transcendental ℚ : ℝ → Prop)

/-- Exercise 7.4 (b): The set of real numbers transcendental over `ℚ` is not
countable. -/
theorem transcendentalReals_not_countable :
    ¬ {x : ℝ | Transcendental ℚ x}.Countable := by
  intro h
  apply Cardinal.not_countable_real
  have transcendental_eq_sdiff :
      {x : ℝ | Transcendental ℚ x} = Set.univ \ {x : ℝ | IsAlgebraic ℚ x} := by
    ext x
    simp [Transcendental]
  have h_transcendental :
      ((Set.univ : Set ℝ) \ {x : ℝ | IsAlgebraic ℚ x}).Countable := by
    rwa [← transcendental_eq_sdiff]
  exact h_transcendental.of_sdiff (Algebraic.countable ℚ ℝ)
