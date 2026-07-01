import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (S : Type u)

/- Definition 1.7.6: an equivalence relation on `S` is a binary relation on `S` satisfying
reflexivity, symmetry, and transitivity; in Lean this is the canonical notion `Setoid S`. -/
recall Setoid (S : Type u) : Type u
