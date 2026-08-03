module

import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Logic.Equiv.Basic

/- Exercise 6.6 (a): After identifying the `n`-element set `{1, …, n}` with `Fin n`,
its subsets correspond to functions `Fin n → Bool` by their characteristic functions. -/
#check fun n : ℕ ↦
  (Equiv.piCongrRight (fun _ : Fin n ↦ Equiv.propEquivBool) : Set (Fin n) ≃ (Fin n → Bool))

/- Exercise 6.6 (b): The power set of a finite set is finite. -/
#check Set.Finite.powerset
