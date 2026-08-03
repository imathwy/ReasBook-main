module

public import Topology_Munkres_2000.Book.Exercise_10_8.Lex
public import Mathlib.Data.Sum.Order

public section

/- Exercise 10.8 (1): The tagged sum of two well-ordered types, representing a disjoint
union, is well-ordered by the relation that places the first summand before the second. -/
#check Sum.instIsWellOrderLex

/- Exercise 10.8 (2): A tagged dependent sum of well-ordered fibers indexed by a
well-ordered type, representing an indexed disjoint family, is well-ordered lexicographically. -/
#check Sigma.instIsWellOrderLex
