import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap04.Definition_4_3_3

universe u

namespace CategoryTheory

section Sheaf

variable (C : Type u) [SmallCategory C]
variable (J : GrothendieckTopology C)
variable (X : TopCat)

#check Sheaf
#check TopCat.Sheaf
#check (inferInstance : LargeCategory (Sheaf J (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf AddCommGrpCat))

end Sheaf

end CategoryTheory
