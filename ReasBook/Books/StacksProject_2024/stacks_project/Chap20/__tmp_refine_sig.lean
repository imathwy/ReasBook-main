import StacksProject_2024.stacks_project.Chap20.Theorem_20_18_2_Proper_base_change

open CategoryTheory

noncomputable section

universe u1 u2 u3 v1 v2 v3

section

variable {A : Type u1} {B : Type u2} {C : Type u3}
variable [Category.{v1} A] [Category.{v2} B] [Category.{v3} C]
variable (W : MorphismProperty A)
variable {F : A ⥤ B} {G : B ⥤ C}
variable {RF RF' : A.W.Localization ⥤ B} {RG : B ⥤ C}
variable {α : F ⟶ W.Q ⋙ RF} {α' : F ⟶ W.Q ⋙ RF'} {β : G ⟶ 𝟭 _ ⋙ RG}

#check Functor.IsRightDerivedFunctor.comp
#check Functor.IsRightDerivedFunctor.ofIso
#check Functor.IsRightDerivedFunctor.ofNatIso
#check Functor.HasRightDerivedFunctor.mk'

end
