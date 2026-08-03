module

import Mathlib.GroupTheory.CoprodI

universe u

variable (J : Type u)

/-
Definition 69.3. For an index type `J`, the free group on formal generators
`a_α` is the external free product `Monoid.CoprodI (fun _ : J ↦ Multiplicative ℤ)`;
the canonical inclusion `Monoid.CoprodI.of` sends the integer exponent `n` in the
`α`th factor to the formal power `a_α^n`.
-/
#check Monoid.CoprodI (fun _ : J ↦ Multiplicative ℤ)
#check Monoid.CoprodI.of

/- The one-generator free group is `Multiplicative ℤ`, and mathlib's word model
`FreeGroup J` is canonically the external free product of these factors. -/
#check FreeGroup.mulEquivIntOfUnique
#check freeGroupEquivCoprodI
