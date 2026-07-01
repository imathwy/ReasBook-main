import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (S : Type u)

/- Definition 1.1.6: an equivalence relation on `S` is a setoid on `S`, namely a binary relation
on `S` satisfying reflexivity, symmetry, and transitivity. -/
recall Setoid (S : Type u) : Type u
