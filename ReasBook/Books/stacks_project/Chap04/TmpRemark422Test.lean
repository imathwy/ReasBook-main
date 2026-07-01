import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap04.Definition_4_3_3

universe u

namespace CategoryTheory

recall LargeCategory
recall SmallCategory

#check (inferInstance : LargeCategory (Type u))
#check (inferInstance : LargeCategory AddCommGrpCat)
#check (inferInstance : LargeCategory GrpCat)
#check (inferInstance : LargeCategory RingCat)
#check (inferInstance : LargeCategory TopCat)
#check (inferInstance : LargeCategory AlgebraicGeometry.Scheme)

section AlgebraicExamples

variable (G : Type u) [Group G]
variable (R : Type u) [Ring R]
variable (k : Type u) [Field k]

#check (inferInstance : LargeCategory (Action (Type u) G))
#check (inferInstance : LargeCategory (ModuleCat R))
#check (inferInstance : LargeCategory (ModuleCat k))

end AlgebraicExamples

section Presheaf

variable (C : Type u) [SmallCategory C]
variable (X : TopCat)

#check Presheaf
#check (inferInstance : LargeCategory (Presheaf C))
#check TopCat.Presheaf
#check (inferInstance : LargeCategory (X.Presheaf (Type u)))
#check (inferInstance : LargeCategory (X.Presheaf AddCommGrpCat))

end Presheaf

section SetValuedFunctors

variable (C : Type u) [SmallCategory C]

#check (inferInstance : LargeCategory (C ⥤ Type u))

end SetValuedFunctors

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
