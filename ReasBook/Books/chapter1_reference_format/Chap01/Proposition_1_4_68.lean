import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

/-- Helper for Proposition 1.4.68: if `ℂ` is algebraic over `ℚ`, then every complex number is
algebraic, so the set of algebraic complex numbers is all of `ℂ`. -/
lemma complex_algebraic_set_eq_univ_of_isAlgebraic (h : Algebra.IsAlgebraic ℚ ℂ) :
    ({z : ℂ | IsAlgebraic ℚ z} : Set ℂ) = Set.univ := by
  -- Convert the algebraicity of the whole extension into pointwise algebraicity.
  have hall : ∀ z : ℂ, IsAlgebraic ℚ z := Algebra.isAlgebraic_def.mp h
  -- The defining predicate now holds at every point, so the set is the whole space.
  ext z
  simp [hall z]

/-- Helper for Proposition 1.4.68: if `ℂ` were algebraic over `ℚ`, then `ℂ` itself would be
countable because the algebraic complex numbers form a countable set. -/
lemma complex_univ_countable_of_isAlgebraic (h : Algebra.IsAlgebraic ℚ ℂ) :
    (Set.univ : Set ℂ).Countable := by
  -- Start from the standard countability theorem for algebraic complex numbers.
  have hcount : ({z : ℂ | IsAlgebraic ℚ z} : Set ℂ).Countable := Algebraic.countable ℚ ℂ
  -- Under the algebraicity assumption, that countable set is all of `ℂ`.
  rw [complex_algebraic_set_eq_univ_of_isAlgebraic h] at hcount
  simpa using hcount

/-- Helper for Proposition 1.4.68: the complex numbers are not algebraic over `ℚ`. -/
lemma complex_not_isAlgebraic : ¬ Algebra.IsAlgebraic ℚ ℂ := by
  -- If every complex number were algebraic, `ℂ` would be countable.
  intro h
  have hcount : (Set.univ : Set ℂ).Countable := complex_univ_countable_of_isAlgebraic h
  -- This contradicts the standard uncountability of the complex numbers.
  exact not_countable_complex hcount

/-- Proposition 1.4.68: the `ℚ`-algebra `ℂ` is transcendental. -/
theorem complex_transcendental : Algebra.Transcendental ℚ ℂ := by
  -- Route correction: follow the textbook argument via countability of algebraic numbers,
  -- rather than introducing a specific transcendental witness.
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  -- Once total algebraicity is excluded, transcendence of the extension follows immediately.
  exact complex_not_isAlgebraic

end
