module

public import Topology_Munkres_2000.Book.Notation_5_3.Tuples

universe u

open scoped Book

/- Notation 5.3: When every factor is the same type `X`, the type of
`m`-tuples is denoted `X^m` in the book, and the type of `ω`-tuples is denoted
`X^ω`. In Lean these are the function types indexed by `Set.Icc 1 m` and `ℕ+`,
respectively. -/
#check fun (m : ℕ+) (X : Type u) ↦ X ^ m
#check fun (X : Type u) ↦ X ^ω
