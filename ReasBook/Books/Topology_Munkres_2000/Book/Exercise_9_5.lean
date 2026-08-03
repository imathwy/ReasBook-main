module

import Mathlib.Logic.Function.Basic

/- Exercise 9.5 (1): The choice axiom gives a right inverse to every surjective
function. -/
#check Function.Surjective.hasRightInverse

/- Exercise 9.5 (2): An injective function with nonempty domain has a left inverse.
The textbook's final question asks about proof provenance rather than an additional
mathematical statement; the usual construction sends points outside the range to a
fixed element of the domain and therefore needs no further arbitrary choices. -/
#check Function.Injective.hasLeftInverse
