module

import Topology_Munkres_2000.Book.Theorem_8_4

public section

/- Definition 7.4 (Principle of recursive definition). The initial value `a₀`
specifies `h 1`, while `ρ` specifies each later value `h i` from the restriction
of `h` to the positive integers in `Set.Iio i`; together they determine a unique
function `h : ℕ+ → A`. -/
#check existsUnique_positiveRecursive
