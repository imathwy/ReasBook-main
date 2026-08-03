module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Sort

public section

universe u

/- Exercise 6.4 (1): Every nonempty finite linear order has a largest element. -/
#check fun {A : Type u} [LinearOrder A] [Finite A] [Nonempty A] ↦
  Finite.exists_max (fun a : A ↦ a)

/- Exercise 6.4 (2): Every finite linear order has the order type of
`Fin (Fintype.card A)`. Here `Fin n = {0, …, n - 1}` is the zero-based Lean model
of the positive-integer section `{1, …, n}`. -/
#check fun (A : Type u) [Fintype A] [LinearOrder A] ↦ monoEquivOfFin A rfl
