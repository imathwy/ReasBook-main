import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (ι : Type v) (E : Type u) [AddCommGroup E] [Module ℝ E]

/- Definition 1.4 is recall-only: a basis of a real vector space `E` is the canonical mathlib
owner object `Module.Basis ι ℝ E`. -/
#check Module.Basis ι ℝ E

/- The owner-side API matches the textbook characterization of a basis: its vectors are linearly
independent, they span the whole space, and conversely `Module.Basis.mk` reconstructs the basis
from that data. -/
recall Module.Basis.linearIndependent
recall Module.Basis.span_eq
recall Module.Basis.mk

end
