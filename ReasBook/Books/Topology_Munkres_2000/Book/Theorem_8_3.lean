module

public import Topology_Munkres_2000.Book.Theorem_8_1

public section

/- Theorem 8.3. For an infinite set `C` of positive natural numbers, there exists
a unique function `h : ℕ+ → C` such that `h i` is the least element not among
`h '' Set.Iio i` for every `i`. -/
#check existsUnique_recursiveLeastUnused
