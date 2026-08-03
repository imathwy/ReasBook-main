module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum

public section

universe u

/- Definition 24.1: A nontrivial linearly ordered set is a linear continuum when it
has the least upper bound property and is densely ordered. -/
#check fun (L : Type u) [LinearOrder L] [Nontrivial L] ↦ LinearContinuum L

-- The existing owner exposes the least-upper-bound and density conditions directly.
#check LinearContinuum.iff
