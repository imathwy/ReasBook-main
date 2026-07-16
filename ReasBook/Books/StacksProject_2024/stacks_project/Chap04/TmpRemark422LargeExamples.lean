import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap04.Definition_4_3_3

universe u

namespace CategoryTheory

#check (inferInstance : LargeCategory (Type u))
#check (inferInstance : LargeCategory AddCommGrpCat)
#check (inferInstance : LargeCategory GrpCat)
#check (inferInstance : LargeCategory RingCat)
#check (inferInstance : LargeCategory TopCat)
#check (inferInstance : LargeCategory AlgebraicGeometry.Scheme)

end CategoryTheory
