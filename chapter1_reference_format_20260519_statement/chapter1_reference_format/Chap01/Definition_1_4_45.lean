import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.4.45: the owner predicate for algebraic elements is `IsAlgebraic`; an algebraic
number in a field extension `K / ℚ` is the specialization `IsAlgebraic ℚ`. Concretely,
`IsAlgebraic ℚ α` means that `α` is a root of some nonzero polynomial with rational coefficients.
-/
recall IsAlgebraic (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A] (x : A) : Prop

/- The owner predicate for transcendental elements is `Transcendental`; a transcendental number
over `ℚ` is the specialization `Transcendental ℚ`. Concretely, `Transcendental ℚ α` means that
`α` is not algebraic over `ℚ`. -/
recall Transcendental (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A] (x : A) :
  Prop
