import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (X : Type u) (Y : Type v)

/- Definition 1.1.2: a map from a set `X` to a set `Y` is the function type `X → Y`; when the
codomain is a set of numbers one also calls such a map a function, and when `X = Y` one also
calls it a transformation. -/
#check (X → Y)
