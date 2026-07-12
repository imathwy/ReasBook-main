import Mathlib
import StacksProject_2024.Chap04.Definition_4_42_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

/- Domain-style sampling for Lemma 4.42.4:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base and
  the induced functors on their fiber categories;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `sliceTwoFibreProductStructuredArrowEquivFiber`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the source-facing owner hom `F : X ⟶ Y`, together with its canonical
  slice base change `F.sliceTwoFibreProduct G` over `C/U`; the fiberwise statement should be
  derived from that owner data rather than from a parallel local slice wrapper;
- primitive data: the owner morphism `F` and, for a chosen `y ∈ Y_U`, the canonical Yoneda
  representing morphism `Gy : C/U ⟶ Y`;
- derived API: the slice object `F.sliceTwoFibreProduct G`, its fibred-in-setoids consequence via
  Lemma `4.40.2`, and the comparison equivalence of Lemma `4.42.1`.

Source/core/bridge triage:
- `source-facing`: `fiber_functor_faithful_of_is_representable`;
- `core/canonical`: `F.IsRepresentable`, `F.sliceTwoFibreProduct G`, and the owner theorem
  `isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- `bridge/view`: the Yoneda-selected morphism `Gy` and the equivalence
  `sliceTwoFibreProductStructuredArrowEquivFiber`. -/

-- Proof sketch: for a fixed object `U : C`, Lemma `4.42.1` identifies the fiber over `𝟙 U` of
-- the representable base change `(C/U) ×_Y X → C/U` with the comma-style fiber category attached
-- to `F_U`. By Lemma `4.40.2`, a representable fibred category in groupoids is fibred in setoids,
-- so this fiber category is a setoid; that is exactly the faithfulness of `F_U`.
/-- Lemma 4.42.4: if a `1`-morphism `F : X ⟶ Y` of categories fibred in groupoids over `C` is
representable, then for every object `U : C` the induced functor `F_U : X_U ⥤ Y_U` between fiber
categories is faithful. -/
theorem fiber_functor_faithful_of_is_representable
    (F : FibredInGroupoidsMor X Y)
    (hF : F.IsRepresentable)
    (U : C) :
    (fiberFunctor F U).Faithful := sorry

end FibredInGroupoidsMor

end CategoryTheory
