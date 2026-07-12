import Mathlib
open Module
example {A : Type*} [Ring A] (N : Ideal A) (j : ℕ) : N ^ j = N ^ j := by
  set_option pp.all true in
  exact rfl
#check fun {A : Type} [Ring A] (N : Ideal A) (j : ℕ) => (N ^ j : Ideal A)
