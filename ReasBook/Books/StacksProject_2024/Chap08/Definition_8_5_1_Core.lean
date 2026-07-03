import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap08.Definition_8_4_1

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Definition 8.5.1 core: a category over the site `(C, J)` is a stack in groupoids when it is
already a stack on the site and is fibred in groupoids. This small owner file isolates the
statement needed by Lemma 8.5.3 from the heavier wrapper module. -/
class IsStackInGroupoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackOnSite J p where
  toIsFibredInGroupoids : IsFibredInGroupoids p

attribute [instance] IsStackInGroupoids.toIsFibredInGroupoids

/-- A fibred-in-groupoids functor that is already a stack over `(C, J)` is a stack in groupoids. -/
instance (J : GrothendieckTopology C) [IsFibredInGroupoids p] [IsStackOnSite J p] :
    IsStackInGroupoids J p where
  toIsStackOnSite := inferInstance
  toIsFibredInGroupoids := inferInstance

end

end CategoryTheory
