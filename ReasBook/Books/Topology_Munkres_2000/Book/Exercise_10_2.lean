module

import Mathlib.Order.Cover
import Mathlib.Data.Int.SuccPred
import Topology_Munkres_2000.Book.Example_10_3

public section

/- Exercise 10.2 (1): In a well-ordered linear type, every nonmaximal element
has an immediate successor. -/
#check exists_covBy_of_wellFoundedLT

/- Exercise 10.2 (2): In the usual order on `ℤ`, the integer `z + 1` is the
immediate successor of `z`. -/
#check (Order.covBy_add_one : ∀ z : ℤ, z ⋖ z + 1)

/- Exercise 10.2 (3): The usual order on `ℤ` is not well founded, so the
immediate-successor property does not imply that an order is well ordered. -/
#check integersNotWellOrdered
