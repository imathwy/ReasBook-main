module

import Mathlib.Order.Cover

universe u

variable {X : Type u} [LinearOrder X] {s : Set X} {a b c : X}

/- Exercise 3.11 (1): An element of an ordered set has at most one immediate
successor. -/
#check (CovBy.unique_right : a ⋖ b → a ⋖ c → b = c)

/- Exercise 3.11 (2): An element of an ordered set has at most one immediate
predecessor. -/
#check (CovBy.unique_left : b ⋖ a → c ⋖ a → b = c)

/- Exercise 3.11 (3): A subset of an ordered set has at most one smallest
element. -/
#check (IsLeast.unique : IsLeast s a → IsLeast s b → a = b)

/- Exercise 3.11 (4): A subset of an ordered set has at most one largest
element. -/
#check (IsGreatest.unique : IsGreatest s a → IsGreatest s b → a = b)
