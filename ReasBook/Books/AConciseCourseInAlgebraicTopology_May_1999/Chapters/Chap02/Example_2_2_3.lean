import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Example 2.2.3: the forgetful functor from topological spaces to sets is a basic example of a
functor. -/
#check (forget TopCat)

/- The forgetful functor from abelian groups to sets is another basic example of a functor. -/
#check (forget AddCommGrpCat)

/- The free abelian group construction defines a functor from sets to abelian groups. -/
recall AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}
