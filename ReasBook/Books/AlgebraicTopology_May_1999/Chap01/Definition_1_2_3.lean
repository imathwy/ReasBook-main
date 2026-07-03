import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y z : X}

/- Definition 1.2.3: for paths `f : Path x y` and `g : Path y z`, the composite
`Path.trans f g` traverses `f` on the first half of `I` and `g` on the second half, each at
double speed. -/
recall Path.trans (f : Path x y) (g : Path y z) : Path x z
