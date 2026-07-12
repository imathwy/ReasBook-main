import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable (U : C)

/- Domain-style sampling for Lemma 19.14.1:
- primary domain: the Gabriel-Popescu module embedding attached to an object in a Grothendieck
  abelian category;
- sampled owner declarations:
  `preadditiveCoyonedaObj`,
  `tensorObj`,
  `tensorObjPreadditiveCoyonedaObjAdjunction`,
  `GabrielPopescu.full`;
- best owner abstraction: the canonical adjunction
  `tensorObj U ⊣ preadditiveCoyonedaObj U`;
- primitive data: the object `U : C`;
- derived API: the left-adjoint structure on `tensorObj U`, and under separator hypotheses the
  fullness and faithfulness consequences used later in the chapter.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that the module-valued functor represented by `U` admits a
  left adjoint;
- `core/canonical`: `tensorObjPreadditiveCoyonedaObjAdjunction U`;
- `bridge/view`: none beyond this direct recall.

This item is therefore a pure canonical recall: introducing a local adjunction alias or a wrapper
for the left adjoint would duplicate the upstream owner without adding mathematical content. -/

/- Lemma 19.14.1: in the Gabriel-Popescu setup, the functor
`preadditiveCoyonedaObj U : C ⥤ ModuleCat (End U)ᵐᵒᵖ` has a left adjoint
`tensorObj U : ModuleCat (End U)ᵐᵒᵖ ⥤ C`. This is exactly the canonical adjunction
`tensorObjPreadditiveCoyonedaObjAdjunction`. -/
recall tensorObjPreadditiveCoyonedaObjAdjunction

end CategoryTheory.IsGrothendieckAbelian
