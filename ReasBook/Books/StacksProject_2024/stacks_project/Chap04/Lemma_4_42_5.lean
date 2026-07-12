import Mathlib
import StacksProject_2024.Chap04.Definition_4_42_3
import StacksProject_2024.Chap04.Lemma_4_39_6
import StacksProject_2024.Chap04.Lemma_4_40_2
import StacksProject_2024.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open Functor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

variable {X Y : FibredInGroupoidsOver C}

/- Domain-style sampling for Lemma 4.42.5:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the owner hom `F : X ⟶ Y` together with the canonical slice base-change
  object `F.sliceTwoFibreProduct G` attached to an actual slice morphism `G : C/U ⟶ Y`; the
  source-facing fibre-object formulation is recovered through Yoneda equivalence only as internal
  bridge data, not as a second public owner;
- primitive data: the owner morphism `F`, faithfulness of `F.toBasedFunctor`, and for each slice
  morphism `G : C/U ⟶ Y` representability of the canonical iso-class presheaf of
  `F.sliceTwoFibreProduct G`;
- derived API: the representability criterion from Lemma `4.40.2`, and the internal Yoneda bridge
  from a fiber object `y ∈ Y_U` to a slice morphism `G : C/U ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: Lemma 4.42.5;
- `core/canonical`: `F.IsRepresentable`;
- `bridge/view`: the internal Yoneda-selected morphism `C/U ⟶ Y` attached to a fiber object
  `y ∈ Y_U`. -/

-- Proof sketch: fix `U : C` and `G : C/U ⟶ Y`. The category `F.sliceTwoFibreProduct G` is the
-- canonical slice base change of `F` along `G`, and its iso-class presheaf is exactly the owner
-- presheaf `fiberIsoClassPresheaf (F.sliceTwoFibreProduct G).p`. Under Yoneda, taking `G`
-- corresponding to `y ∈ Y_U` recovers the source presheaf of pairs
-- `(x, \phi : f^* y ⟶ F(x))`. Faithfulness of `F.toBasedFunctor` forces each such slice
-- projection to be fibred in setoids, and Lemma `4.40.2` upgrades representability of every
-- slice iso-class presheaf to representability of every slice base change, hence of `F`.
/-- Lemma 4.42.5: let `F : X ⟶ Y` be a morphism of categories fibred in groupoids over `C`.
Assume that the underlying based functor `F.toBasedFunctor` is faithful and that for every object
`U : C` and every slice morphism `G : C/U ⟶ Y`, the canonical presheaf of isomorphism classes of
objects in the slice base change `F.sliceTwoFibreProduct G` is representable. Via the Yoneda
equivalence for `Y_U`, this is exactly the source presheaf of isomorphism classes of pairs
`(x, \phi : f^* y ⟶ F(x))`. Then `F` is representable. -/
theorem isRepresentable_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isRepresentable
    (F : FibredInGroupoidsMor X Y)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hRepresentable :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ Y),
        ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf).IsRepresentable) :
    F.IsRepresentable := sorry

end FibredInGroupoidsMor

end CategoryTheory
