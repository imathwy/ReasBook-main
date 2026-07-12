import StacksProject_2024.Temp.PlusNotationOwner
open CategoryTheory Opposite
open scoped CategoryTheory.GrothendieckTopology
universe v u
section
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))
#check (P⁺ : Cᵒᵖ ⥤ Type (max u v))
#check (J.toPlus P : P ⟶ P⁺)
end
