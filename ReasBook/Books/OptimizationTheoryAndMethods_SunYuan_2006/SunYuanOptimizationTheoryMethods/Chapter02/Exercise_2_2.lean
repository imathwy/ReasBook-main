import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Nat.Fib.Basic

-- Semantic recall: this exercise asks for the Fibonacci algorithm together with an implementation,
-- so the file reuses mathlib's canonical Fibonacci API directly. `Nat.fib` is the specification,
-- `Nat.fastFib` is the executable program, `Nat.fastFib_eq` is the correctness bridge, and
-- `Nat.fib_add_two` records the standard recurrence.

/- Chapter02 Exercise 2.2

Recall-only entry: the source asks for the Fibonacci algorithm and its MATLAB/FORTRAN/C
implementation. In Lean, the canonical specification is `Nat.fib`, the executable algorithm is
`Nat.fastFib`, and `Nat.fastFib_eq` identifies the program with the specification.
-/
#check Nat.fib

#check Nat.fastFib

#check Nat.fastFib_eq

#check Nat.fib_add_two
