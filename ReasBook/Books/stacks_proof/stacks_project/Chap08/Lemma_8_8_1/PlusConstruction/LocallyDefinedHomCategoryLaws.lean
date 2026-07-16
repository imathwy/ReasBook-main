import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentity
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomTotal

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

/-- Source stage 2.4 associativity law for fixed-base raw locally-defined representatives.

This is the Prop frontier corresponding to the Stacks proof sentence: on the common triple cover
`U_i ×_V V_j ×_W W_k`, both bracketings have local component `c_k ∘ b_j ∘ a_i`.  The displayed
base arrows differ only by categorical associativity, so the left bracketing is first transported
along that equality. -/
noncomputable def composeOverAssociativityLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k) : Prop :=
  Equivalent (J := J)
    (castBase (J := J) (by simp [Category.assoc] : (f ≫ g) ≫ k = f ≫ (g ≫ k))
      (composeOver (J := J) (composeOver (J := J) α β) γ))
    (composeOver (J := J) α (composeOver (J := J) β γ))

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomRepresentative

/-- Raw locally-defined composition is associative once the fixed-base triple-cover law is
supplied. -/
theorem compose_assoc_equivalent_of_associativityLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X w x)
    (β : LocallyDefinedHomRepresentative (J := J) X x y)
    (γ : LocallyDefinedHomRepresentative (J := J) X y z)
    (hLaw :
      LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw
        (J := J) α.representative β.representative γ.representative) :
    Equivalent (J := J)
      (compose (J := J) (compose (J := J) α β) γ)
      (compose (J := J) α (compose (J := J) β γ)) := by
  apply (equivalent_iff_exists_base_eq (J := J)
    (compose (J := J) (compose (J := J) α β) γ)
    (compose (J := J) α (compose (J := J) β γ))).2
  refine ⟨by simp [Category.assoc], ?_⟩
  exact hLaw

end LocallyDefinedHomRepresentative

/-- Source stage 2 category-law frontier for locally-defined morphisms.  The fields are exactly
the omitted Stacks local calculations:

* left and right identity reduce to the trivial-cover identity refinements;
* associativity reduces to the common triple cover where both bracketings are the same local
  composite.

This keeps the owner-correct formal category surface separate from the remaining pseudofunctor
coherence calculations. -/
structure LocallyDefinedHomCategoryFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2.4 left identity on the fixed-base local family. -/
  leftIdentity :
    ∀ ⦃x y : X.S⦄ ⦃f : X.p.obj x ⟶ X.p.obj y⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f),
      LocallyDefinedHomRepresentativeOver.composeOverLeftIdentityFamilyLaw (J := J) α
  /-- Source stage 2.4 right identity on the fixed-base local family. -/
  rightIdentity :
    ∀ ⦃x y : X.S⦄ ⦃f : X.p.obj x ⟶ X.p.obj y⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f),
      LocallyDefinedHomRepresentativeOver.composeOverRightIdentityFamilyLaw (J := J) α
  /-- Source stage 2.4 associativity on the fixed-base common triple cover. -/
  associativity :
    ∀ ⦃w x y z : X.S⦄
      ⦃f : X.p.obj w ⟶ X.p.obj x⦄
      ⦃g : X.p.obj x ⟶ X.p.obj y⦄
      ⦃k : X.p.obj y ⟶ X.p.obj z⦄
      (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
      (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
      (γ : LocallyDefinedHomRepresentativeOver (J := J) X k),
      LocallyDefinedHomRepresentativeOver.composeOverAssociativityLaw (J := J) α β γ

namespace LocallyDefinedHom

/-- Conditional source stage 2 left identity for plus-packaged locally-defined morphisms. -/
theorem id_comp_of_categoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomCategoryFrontier (J := J) X)
    {x y : X.S} (a : locallyDefinedHom (J := J) X x y) :
    comp (J := J) (locallyDefinedHomId (J := J) X x) a = a :=
  id_comp_of_representative_familyLaw (J := J) a
    (chooseRepresentative (J := J) a) (chooseRepresentative_spec (J := J) a)
    (H.leftIdentity (chooseRepresentative (J := J) a).representative)

/-- Conditional source stage 2 right identity for plus-packaged locally-defined morphisms. -/
theorem comp_id_of_categoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomCategoryFrontier (J := J) X)
    {x y : X.S} (a : locallyDefinedHom (J := J) X x y) :
    comp (J := J) a (locallyDefinedHomId (J := J) X y) = a :=
  comp_id_of_representative_familyLaw (J := J) a
    (chooseRepresentative (J := J) a) (chooseRepresentative_spec (J := J) a)
    (H.rightIdentity (chooseRepresentative (J := J) a).representative)

/-- Conditional source stage 2 associativity for plus-packaged locally-defined morphisms. -/
theorem assoc_of_categoryFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : LocallyDefinedHomCategoryFrontier (J := J) X)
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

/-- Conditional category instance for the source stage 2 locally-defined-Hom total surface.  This
records that the only missing work for a full category is the three source-local laws bundled in
`LocallyDefinedHomCategoryFrontier`. -/
@[reducible]
noncomputable def categoryOfFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : LocallyDefinedHomCategoryFrontier (J := J) X) :
    Category (LocallyDefinedHomTotal (J := J) X) where
  Hom x y := locallyDefinedHom (J := J) X x.obj y.obj
  id x := locallyDefinedHomId (J := J) X x.obj
  comp f g := LocallyDefinedHom.comp (J := J) f g
  id_comp := by
    intro x y f
    exact LocallyDefinedHom.id_comp_of_categoryFrontier (J := J) H f
  comp_id := by
    intro x y f
    exact LocallyDefinedHom.comp_id_of_categoryFrontier (J := J) H f
  assoc := by
    intro w x y z f g h
    exact LocallyDefinedHom.assoc_of_categoryFrontier (J := J) H f g h

end LocallyDefinedHomTotal

end FibredCategoryMor

end CategoryTheory
