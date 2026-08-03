module

import Mathlib.Logic.Equiv.Fin.Basic

universe u

/- Remark 6.1. At this point, uniqueness of the cardinality assigned to a finite set
has not yet been proved. In Lean, the missing assertion is that two equivalences of a
type `A` with finite sections `Fin n` and `Fin m` force `n = m`. -/
#check fun (A : Type u) (n m : ℕ) ↦
  Nonempty (A ≃ Fin n) → Nonempty (A ≃ Fin m) → n = m
