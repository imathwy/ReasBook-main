import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.7.8: a number field is the canonical mathlib class `NumberField`, i.e. a field of
characteristic `0` that is finite-dimensional over `ℚ`. -/
recall NumberField

/- Companion recalls: the defining textbook properties of a number field are provided by the
canonical `NumberField` instances. -/
recall NumberField.to_charZero
recall NumberField.to_finiteDimensional
