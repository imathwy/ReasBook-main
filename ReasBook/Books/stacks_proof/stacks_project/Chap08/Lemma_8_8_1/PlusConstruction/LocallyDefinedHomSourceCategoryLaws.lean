import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomSourceIdentityLaws
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCategoryLaws
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativityLocal

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

/-- Source stage 2.4 category-law frontier for locally-defined morphisms, with the identity
representative written literally as the Stacks datum `(id_U, {id_U}, id_x)`.

This is intentionally separate from `LocallyDefinedHomCategoryFrontier`, whose identity fields
still use the ordinary-arrow representative of `𝟙 x`.  Bridging these two identity owners is a
remaining coherence step; this structure records the source-faithful target without erasing that
transport. -/
structure LocallyDefinedHomSourceCategoryFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2.4 left identity on the fixed-base local family, using the literal source
  identity representative. -/
  leftIdentity :
    ∀ ⦃x y : X.S⦄ ⦃f : X.p.obj x ⟶ X.p.obj y⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f),
      LocallyDefinedHomRepresentativeOver.sourceComposeOverLeftIdentityFamilyLaw
        (J := J) α
  /-- Source stage 2.4 right identity on the fixed-base local family, using the literal source
  identity representative. -/
  rightIdentity :
    ∀ ⦃x y : X.S⦄ ⦃f : X.p.obj x ⟶ X.p.obj y⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f),
      LocallyDefinedHomRepresentativeOver.sourceComposeOverRightIdentityFamilyLaw
        (J := J) α
  /-- Source stage 2.4 associativity on the common triple cover. -/
  associativity :
    ∀ ⦃w x y z : X.S⦄
      ⦃f : X.p.obj w ⟶ X.p.obj x⦄
      ⦃g : X.p.obj x ⟶ X.p.obj y⦄
      ⦃k : X.p.obj y ⟶ X.p.obj z⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
      (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
      (γ : LocallyDefinedHomRepresentativeOver (J := J) X k),
      LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw (J := J) α β γ

/-- Source stage 2.4 category-law frontier after discharging the two literal identity laws.
The only remaining source-local law is associativity on the common triple cover. -/
noncomputable def sourceCategoryFrontierOfAssociativity
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hAssoc :
      ∀ ⦃w x y z : X.S⦄
        ⦃f : X.p.obj w ⟶ X.p.obj x⦄
        ⦃g : X.p.obj x ⟶ X.p.obj y⦄
        ⦃k : X.p.obj y ⟶ X.p.obj z⦄
        (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
        (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
        (γ : LocallyDefinedHomRepresentativeOver (J := J) X k),
        LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw (J := J) α β γ) :
    LocallyDefinedHomSourceCategoryFrontier (J := J) X where
  leftIdentity := by
    intro x y f α
    exact LocallyDefinedHomRepresentativeOver.sourceComposeOverLeftIdentityFamilyLaw_holds
      (J := J) α
  rightIdentity := by
    intro x y f α
    exact LocallyDefinedHomRepresentativeOver.sourceComposeOverRightIdentityFamilyLaw_holds
      (J := J) α
  associativity := hAssoc

/-- Source stage 2.4 category-law frontier with the literal source identity representative and
the common-triple-cover associativity calculation discharged.  This remains on the source
identity owner surface; comparison with the ordinary identity representative is intentionally a
separate bridge. -/
noncomputable def sourceCategoryFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    LocallyDefinedHomSourceCategoryFrontier (J := J) X :=
  sourceCategoryFrontierOfAssociativity (J := J) X (by
    intro w x y z f g k α β γ
    exact LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw_holds
      (J := J) α β γ)

namespace LocallyDefinedHom

/-- Conditional source stage 2 left identity for plus-packaged locally-defined morphisms, using
the literal source identity representative. -/
theorem source_id_comp_of_sourceCategoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomSourceCategoryFrontier (J := J) X)
    {x y : X.S} (a : locallyDefinedHom (J := J) X x y) :
    comp (J := J) (sourceIdentityHomToLocallyDefinedHom (J := J) X x) a = a :=
  source_id_comp_of_representative_familyLaw (J := J) a
    (chooseRepresentative (J := J) a) (chooseRepresentative_spec (J := J) a)
    (H.leftIdentity (chooseRepresentative (J := J) a).representative)

/-- Conditional source stage 2 right identity for plus-packaged locally-defined morphisms, using
the literal source identity representative. -/
theorem source_comp_id_of_sourceCategoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomSourceCategoryFrontier (J := J) X)
    {x y : X.S} (a : locallyDefinedHom (J := J) X x y) :
    comp (J := J) a (sourceIdentityHomToLocallyDefinedHom (J := J) X y) = a :=
  source_comp_id_of_representative_familyLaw (J := J) a
    (chooseRepresentative (J := J) a) (chooseRepresentative_spec (J := J) a)
    (H.rightIdentity (chooseRepresentative (J := J) a).representative)

/-- Conditional source stage 2 associativity for plus-packaged locally-defined morphisms.  This
is the common-triple-cover part of the source proof and is independent of the identity-owner
choice. -/
theorem assoc_of_sourceCategoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomSourceCategoryFrontier (J := J) X)
    {w x y z : X.S}
    (a : locallyDefinedHom (J := J) X w x)
    (b : locallyDefinedHom (J := J) X x y)
    (c : locallyDefinedHom (J := J) X y z) :
    comp (J := J) (comp (J := J) a b) c =
      comp (J := J) a (comp (J := J) b c) := by
  let α := chooseRepresentative (J := J) a
  let β := chooseRepresentative (J := J) b
  let γ := chooseRepresentative (J := J) c
  have hα : α.toLocallyDefinedHom = a := chooseRepresentative_spec (J := J) a
  have hβ : β.toLocallyDefinedHom = b := chooseRepresentative_spec (J := J) b
  have hγ : γ.toLocallyDefinedHom = c := chooseRepresentative_spec (J := J) c
  have hab :
      comp (J := J) a b =
        (LocallyDefinedHomRepresentative.compose (J := J) α β).toLocallyDefinedHom :=
    comp_eq_of_representatives (J := J) a b α β hα hβ
  have hbc :
      comp (J := J) b c =
        (LocallyDefinedHomRepresentative.compose (J := J) β γ).toLocallyDefinedHom :=
    comp_eq_of_representatives (J := J) b c β γ hβ hγ
  calc
    comp (J := J) (comp (J := J) a b) c =
        (LocallyDefinedHomRepresentative.compose (J := J)
          (LocallyDefinedHomRepresentative.compose (J := J) α β) γ).toLocallyDefinedHom := by
      exact comp_eq_of_representatives (J := J)
        (comp (J := J) a b) c
        (LocallyDefinedHomRepresentative.compose (J := J) α β) γ hab.symm hγ
    _ =
        (LocallyDefinedHomRepresentative.compose (J := J) α
          (LocallyDefinedHomRepresentative.compose (J := J) β γ)).toLocallyDefinedHom :=
      LocallyDefinedHomRepresentative.compose_assoc_equivalent_of_associativityLaw
        (J := J) α β γ (H.associativity α.representative β.representative γ.representative)
    _ = comp (J := J) a (comp (J := J) b c) := by
      symm
      exact comp_eq_of_representatives (J := J)
        a (comp (J := J) b c)
        α (LocallyDefinedHomRepresentative.compose (J := J) β γ) hα hbc.symm

end LocallyDefinedHom

namespace LocallyDefinedHomTotal

/-- Conditional category structure for the source stage 2 locally-defined-Hom total surface,
using the literal identity representative from the source proof.

This does not replace the ordinary-identity category frontier.  It records the Stacks 2.4
category construction on its own owner surface while the ordinary/source identity comparison is
kept as an explicit remaining bridge. -/
@[reducible]
noncomputable def sourceCategoryOfFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : LocallyDefinedHomSourceCategoryFrontier (J := J) X) :
    Category (LocallyDefinedHomTotal (J := J) X) where
  Hom x y := locallyDefinedHom (J := J) X x.obj y.obj
  id x := sourceIdentityHomToLocallyDefinedHom (J := J) X x.obj
  comp f g := LocallyDefinedHom.comp (J := J) f g
  id_comp := by
    intro x y f
    exact LocallyDefinedHom.source_id_comp_of_sourceCategoryFrontier (J := J) H f
  comp_id := by
    intro x y f
    exact LocallyDefinedHom.source_comp_id_of_sourceCategoryFrontier (J := J) H f
  assoc := by
    intro w x y z f g h
    exact LocallyDefinedHom.assoc_of_sourceCategoryFrontier (J := J) H f g h

/-- Conditional category structure after the source identity laws have been discharged; the
remaining input is exactly the source proof's common-triple-cover associativity law. -/
@[reducible]
noncomputable def sourceCategoryOfAssociativity
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hAssoc :
      ∀ ⦃w x y z : X.S⦄
        ⦃f : X.p.obj w ⟶ X.p.obj x⦄
        ⦃g : X.p.obj x ⟶ X.p.obj y⦄
        ⦃k : X.p.obj y ⟶ X.p.obj z⦄
        (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
        (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
        (γ : LocallyDefinedHomRepresentativeOver (J := J) X k),
        LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw (J := J) α β γ) :
    Category (LocallyDefinedHomTotal (J := J) X) :=
  sourceCategoryOfFrontier (J := J) X
    (sourceCategoryFrontierOfAssociativity (J := J) X hAssoc)

/-- Source stage 2 category structure using the literal source identity representative.  The
ordinary-identity owner bridge is not folded into this definition. -/
@[reducible]
noncomputable def sourceCategory
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    Category (LocallyDefinedHomTotal (J := J) X) :=
  sourceCategoryOfFrontier (J := J) X (sourceCategoryFrontier (J := J) X)

end LocallyDefinedHomTotal

end FibredCategoryMor

end CategoryTheory
