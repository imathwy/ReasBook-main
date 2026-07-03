import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.120.2: for a domain `R` and elements `x y : R`, the elements `x` and `y` are
associates if and only if the principal ideals `(x)` and `(y)` coincide. In Lean this is the
canonical theorem `Ideal.span_singleton_eq_span_singleton`, where `(x)` is written as
`Ideal.span ({x} : Set R)`. -/
recall Ideal.span_singleton_eq_span_singleton
