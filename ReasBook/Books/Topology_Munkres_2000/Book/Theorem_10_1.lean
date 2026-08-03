module

public import Mathlib.Data.Fintype.Sort

public section

universe u

variable (A : Type u) [Fintype A] [LinearOrder A]

/- Theorem 10.1 (1): Every finite linear order has the order type of
`Fin (Fintype.card A)`, the zero-based Lean model of the section `{1, …, n}`. -/
#check monoEquivOfFin A rfl

/- Theorem 10.1 (2): Consequently, every finite linear order is well ordered. -/
#synth WellFoundedLT A
