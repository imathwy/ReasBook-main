import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (A : Type u) (X : Type v)

/- Text 1.0.23: once the directed-set structure on the index type is fixed in the ambient
context, a net in `X` indexed by `A` is formalized by the canonical function type `A → X`. The
textbook's nonemptiness assumption on `X` does not affect this underlying data. -/
#check A → X
