import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable (U : C)

/- Lemma 19.14.1: in the Gabriel-Popescu setup, the functor
`preadditiveCoyonedaObj U : C ⥤ ModuleCat (End U)ᵐᵒᵖ` has a left adjoint
`tensorObj U : ModuleCat (End U)ᵐᵒᵖ ⥤ C`. This is exactly the canonical adjunction
`tensorObjPreadditiveCoyonedaObjAdjunction`. -/
recall tensorObjPreadditiveCoyonedaObjAdjunction

end CategoryTheory.IsGrothendieckAbelian
