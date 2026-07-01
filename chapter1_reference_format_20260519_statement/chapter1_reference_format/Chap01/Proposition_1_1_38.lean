import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.1.38: the multiplicative group of the integer ring is the two-element set
`{±1}`; equivalently, every unit of `ℤ` is either `1` or `-1`. -/
recall Int.units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1
