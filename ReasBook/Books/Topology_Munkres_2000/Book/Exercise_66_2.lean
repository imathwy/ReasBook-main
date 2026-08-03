module

public import Topology_Munkres_2000.Book.Theorem_66_1

/-
Exercise 66.2. A smooth simple closed plane curve, smoothly parameterized by a simple loop, has
winding number `1` or `-1` about the origin when the origin lies in the bounded component of its
complement.
-/
#check PlaneLoop.windingNumber_eq_one_or_neg_one_of_smooth
