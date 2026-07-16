import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativityBoundaries

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomRepresentativeOver

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- On the common triple cover, the two source-associated binary compositions have
heterogeneously equal local `down` morphisms.  The proof follows the Stacks calculation:
both sides are reassociated to the same product of the three local morphisms, with the two
pseudofunctor comparison boundaries supplied by
`associativityTripleCover_targetHom_middleIso_heq` and
`associativityTripleCover_targetHom_heq`. -/
theorem associativityTripleCover_local_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      ((compositionLocal (J := J) (composeOver (J := J) α β) γ I).down)
      ((compositionLocal (J := J) α (composeOver (J := J) β γ)
        (associativityTripleCoverToRightMember (J := J) α β γ I)).down) := by
  dsimp [compositionLocal]
  let Iab := associativityTripleCoverToLeftComposite (J := J) α β γ I
  let Ir := associativityTripleCoverToRightMember (J := J) α β γ I
  let Ibc := associativityTripleCoverToRightComposite (J := J) α β γ I
  let A := (compositionLeftLocal (J := J) α β Iab).down
  let Mab := (compositionMiddleIso (J := J) α β Iab).hom
  let B := (compositionRightLocal (J := J) α β Iab).down
  let Tab := compositionTargetHom (J := J) α β Iab
  let Mleft := (compositionMiddleIso (J := J) (composeOver (J := J) α β) γ I).hom
  let G := (compositionRightLocal (J := J) (composeOver (J := J) α β) γ I).down
  let Tleft := compositionTargetHom (J := J) (composeOver (J := J) α β) γ I
  let A' := (compositionLeftLocal (J := J) α (composeOver (J := J) β γ) Ir).down
  let Mright := (compositionMiddleIso (J := J) α (composeOver (J := J) β γ) Ir).hom
  let B' := (compositionLeftLocal (J := J) β γ Ibc).down
  let Mbc := (compositionMiddleIso (J := J) β γ Ibc).hom
  let G' := (compositionRightLocal (J := J) β γ Ibc).down
  let Tbc := compositionTargetHom (J := J) β γ Ibc
  let Tright := compositionTargetHom (J := J) α (composeOver (J := J) β γ) Ir
  have hA : HEq A A' :=
    associativityTripleCover_alphaLocal_down_heq (J := J) α β γ I
  have hM : HEq Mab Mright := by
    rfl
  have hB : HEq B B' :=
    associativityTripleCover_betaLocal_down_heq (J := J) α β γ I
  have hG : HEq G G' :=
    associativityTripleCover_gammaLocal_down_heq (J := J) α β γ I
  have hTM : HEq (Tab ≫ Mleft) Mbc :=
    associativityTripleCover_targetHom_middleIso_heq (J := J) α β γ I
  have hT : HEq Tleft (Tbc ≫ Tright) :=
    associativityTripleCover_targetHom_heq (J := J) α β γ I
  have hAM : HEq (A ≫ Mab) (A' ≫ Mright) := by
    refine heq_comp ?_ ?_ ?_ hA hM
    all_goals
      simp [A, A', Mab, Mright, Iab, Ir, Ibc, associativityTripleCoverToLeftComposite,
        associativityTripleCoverToRightMember, associativityTripleCoverToRightComposite,
        LocallyDefinedHomRepresentative.compositionCoverToLeft,
        LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  have hAMB : HEq ((A ≫ Mab) ≫ B) ((A' ≫ Mright) ≫ B') := by
    refine heq_comp ?_ ?_ ?_ hAM hB
    all_goals
      simp [A, A', Mab, Mright, B, B', Iab, Ir, Ibc,
        associativityTripleCoverToLeftComposite, associativityTripleCoverToRightMember,
        associativityTripleCoverToRightComposite,
        LocallyDefinedHomRepresentative.compositionCoverToLeft,
        LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  have hAMBT :
      HEq (((A ≫ Mab) ≫ B) ≫ (Tab ≫ Mleft))
        (((A' ≫ Mright) ≫ B') ≫ Mbc) := by
    refine heq_comp ?_ ?_ ?_ hAMB hTM
    all_goals
      simp [A, A', Mab, Mright, B, B', Tab, Mleft, Mbc, Iab, Ir, Ibc,
        associativityTripleCoverToLeftComposite, associativityTripleCoverToRightMember,
        associativityTripleCoverToRightComposite,
        LocallyDefinedHomRepresentative.compositionCoverToLeft,
        LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  have hAMBTG :
      HEq ((((A ≫ Mab) ≫ B) ≫ (Tab ≫ Mleft)) ≫ G)
        ((((A' ≫ Mright) ≫ B') ≫ Mbc) ≫ G') := by
    refine heq_comp ?_ ?_ ?_ hAMBT hG
    all_goals
      simp [A, A', Mab, Mright, B, B', Tab, Mleft, Mbc, G, G', Iab, Ir, Ibc,
        associativityTripleCoverToLeftComposite, associativityTripleCoverToRightMember,
        associativityTripleCoverToRightComposite,
        LocallyDefinedHomRepresentative.compositionCoverToLeft,
        LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  have hnorm :
      HEq (((((A ≫ Mab) ≫ B) ≫ (Tab ≫ Mleft)) ≫ G) ≫ Tleft)
        (((((A' ≫ Mright) ≫ B') ≫ Mbc) ≫ G') ≫ (Tbc ≫ Tright)) := by
    refine heq_comp ?_ ?_ ?_ hAMBTG hT
    all_goals
      simp [A, A', Mab, Mright, B, B', Tab, Mleft, Mbc, G, G', Tleft, Tbc, Tright,
        Iab, Ir, Ibc, associativityTripleCoverToLeftComposite,
        associativityTripleCoverToRightMember, associativityTripleCoverToRightComposite,
        LocallyDefinedHomRepresentative.compositionCoverToLeft,
        LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc]
  have hleftAssoc :
      HEq
        (((compositionLeftLocal (J := J) α β Iab).down ≫
              (compositionMiddleIso (J := J) α β Iab).hom ≫
            (compositionRightLocal (J := J) α β Iab).down ≫
              compositionTargetHom (J := J) α β Iab) ≫
          Mleft ≫ G ≫ Tleft)
        (((((A ≫ Mab) ≫ B) ≫ (Tab ≫ Mleft)) ≫ G) ≫ Tleft) := by
    exact heq_of_eq (by
      simp only [A, Mab, B, Tab, Mleft, G, Tleft, Iab, Category.assoc])
  have hrightAssoc :
      HEq
        (((((A' ≫ Mright) ≫ B') ≫ Mbc) ≫ G') ≫ (Tbc ≫ Tright))
        ((A' ≫ Mright ≫
          ((B' ≫ Mbc ≫ G' ≫ Tbc)) ≫ Tright)) := by
    exact heq_of_eq (by
      simp only [A', Mright, B', Mbc, G', Tbc, Tright, Ibc, Ir, Category.assoc])
  exact HEq.trans hleftAssoc (HEq.trans hnorm hrightAssoc)

/-- The fixed-base source associativity law for `composeOver`, obtained from the explicit
common-triple-cover local calculation. -/
theorem composeOverAssociativityLaw_holds
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) :
    composeOverAssociativityLaw (J := J) α β γ :=
  composeOverAssociativityLaw_of_local_down_heq (J := J) α β γ
    (associativityTripleCover_local_down_heq (J := J) α β γ)

end LocallyDefinedHomRepresentativeOver
end FibredCategoryMor

end CategoryTheory
