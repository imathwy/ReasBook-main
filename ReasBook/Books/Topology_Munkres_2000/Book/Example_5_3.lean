module

public import Topology_Munkres_2000.Book.Notation_5_3.Tuples
public import Mathlib.Data.Real.Basic

public section

open scoped Book

/- Example 5.3 (1): Euclidean `m`-space is the type of real-valued functions
whose coordinates are indexed by the positive integers in `Set.Icc 1 m`. -/
#check fun (m : ℕ+) ↦ ℝ ^ m

/- Example 5.3 (2): Infinite-dimensional euclidean space consists of
`ω`-tuples of real numbers, represented by functions `ℕ+ → ℝ`. -/
#check ℝ ^ω
