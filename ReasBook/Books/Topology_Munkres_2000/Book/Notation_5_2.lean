module

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Lattice

universe u

/- Notation 5.2: A finite family indexed by the positive integers from `1` through
`n` is represented by `A : Set.Icc 1 n → Set X`, while a family indexed by all
positive integers is represented by `A : ℕ+ → Set X`. Their unions and
intersections use the indexed notation `⋃ i, A i` and `⋂ i, A i`. -/
#check fun {X : Type u} (n : ℕ+) (A : Set.Icc 1 n → Set X) ↦ ⋃ i, A i
#check fun {X : Type u} (n : ℕ+) (A : Set.Icc 1 n → Set X) ↦ ⋂ i, A i
#check fun {X : Type u} (A : ℕ+ → Set X) ↦ ⋃ i, A i
#check fun {X : Type u} (A : ℕ+ → Set X) ↦ ⋂ i, A i
