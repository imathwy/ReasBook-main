module

public import Mathlib.Logic.Equiv.Fin.Basic

public section

/- Example 5.1 (1): Representing sets by their types of elements, the binary
Cartesian product is canonically equivalent to the dependent type of `Fin 2`-tuples
whose coordinates lie in the two factors. -/
#check prodEquivPiFinTwo

/- Example 5.1 (2): For an ambient-valued `Fin 2`-tuple, the coordinatewise
conditions `f 0 ∈ A` and `f 1 ∈ B` are exactly membership of `(f 0, f 1)` in
the binary set product `A ×ˢ B`. -/
#check Fin.preimage_apply_01_prod'
