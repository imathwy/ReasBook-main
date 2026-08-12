import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 2.3.3: the free abelian group functor is left adjoint to the forgetful functor
from abelian groups to sets, meaning that morphisms from the free abelian group on a set `S`
to an abelian group `A` are naturally identified with functions from `S` to the underlying set
of `A`. -/
#check AddCommGrpCat.adj
