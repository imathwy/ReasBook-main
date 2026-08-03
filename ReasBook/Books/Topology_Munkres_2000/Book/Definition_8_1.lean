module

public import Topology_Munkres_2000.Book.Definition_8_1.RecursionFormula

universe u

/- Definition 8.1: A recursion formula for `h` specifies `h 1` and, for each
`i > 1`, expresses `h i` using the restriction of `h` to `Set.Iio i`. -/
#check Function.IsPositiveRecursionFormula
