import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativity

universe u v uX vX w wA

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem ulift_heq_of_down_heq
    {A B : Type wA}
    {x : ULift.{w, wA} A} {y : ULift.{w, wA} B} (h : HEq x.down y.down) :
    HEq x y := by
  cases x
  cases y
  cases h
  rfl

namespace FibredCategoryMor
namespace LocallyDefinedHomRepresentativeOver

noncomputable section

/-- Associativity on fixed-base representatives follows once the two refined matching families
on the source triple cover have been identified.  This separates the common-refinement
bookkeeping from the remaining source-local calculation. -/
theorem composeOverAssociativityLaw_of_refined_family_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (hfamily :
      (castBase (J := J)
        (by simp [Category.assoc] : (f ≫ g) ≫ k = f ≫ (g ≫ k))
        (composeOver (J := J) (composeOver (J := J) α β) γ)).family.refine
          (associativityTripleCoverToCastLeftHom (J := J) α β γ) =
        (composeOver (J := J) α (composeOver (J := J) β γ)).family.refine
          (associativityTripleCoverToRightHom (J := J) α β γ)) :
    composeOverAssociativityLaw (J := J) α β γ := by
  dsimp [composeOverAssociativityLaw, Equivalent]
  exact ⟨associativityTripleCover (J := J) α β γ,
    associativityTripleCoverToCastLeftHom (J := J) α β γ,
    associativityTripleCoverToRightHom (J := J) α β γ, hfamily⟩

/-- Pointwise heterogeneous equality of the two refined matching-family values is enough for
the fixed-base associativity law. -/
theorem composeOverAssociativityLaw_of_refined_family_apply_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (hpoint :
      ∀ I : (associativityTripleCover (J := J) α β γ).Arrow,
        HEq
          (((castBase (J := J)
            (by simp [Category.assoc] : (f ≫ g) ≫ k = f ≫ (g ≫ k))
            (composeOver (J := J) (composeOver (J := J) α β) γ)).family.refine
              (associativityTripleCoverToCastLeftHom (J := J) α β γ)) I)
          (((composeOver (J := J) α (composeOver (J := J) β γ)).family.refine
              (associativityTripleCoverToRightHom (J := J) α β γ)) I)) :
    composeOverAssociativityLaw (J := J) α β γ := by
  apply composeOverAssociativityLaw_of_refined_family_eq (J := J) α β γ
  apply Meq.ext
  intro I
  exact eq_of_heq (hpoint I)

/-- The only non-bookkeeping part of source associativity is the pointwise local calculation on
`U_i ×_V V_j ×_W W_k`: after unfolding both bracketings, their local morphisms agree.  Once that
calculation is supplied as a heterogeneous equality of the `down` morphisms, the fixed-base
associativity law follows. -/
theorem composeOverAssociativityLaw_of_local_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (hlocal :
      ∀ I : (associativityTripleCover (J := J) α β γ).Arrow,
        HEq
          ((compositionLocal (J := J) (composeOver (J := J) α β) γ I).down)
          ((compositionLocal (J := J) α (composeOver (J := J) β γ)
            (associativityTripleCoverToRightMember (J := J) α β γ I)).down)) :
    composeOverAssociativityLaw (J := J) α β γ := by
  apply composeOverAssociativityLaw_of_refined_family_apply_heq (J := J) α β γ
  intro I
  let leftComp := composeOver (J := J) (composeOver (J := J) α β) γ
  let hbase : (f ≫ g) ≫ k = f ≫ (g ≫ k) := by simp [Category.assoc]
  have hleftRefine :
      ((castBase (J := J) hbase leftComp).family.refine
          (associativityTripleCoverToCastLeftHom (J := J) α β γ)) I =
        (castBaseFamily (J := J) hbase leftComp) I := by
    have hfamily := castBase_family_refine_coverHomCastBase (J := J) hbase leftComp
    exact congrFun (congrArg Subtype.val hfamily) I
  have hcast := castBaseFamily_apply_heq (J := J) hbase leftComp I
  have hleftLocal := composeOver_family_apply (J := J)
    (composeOver (J := J) α β) γ I
  have hrightLocal := composeOver_family_apply (J := J)
    α (composeOver (J := J) β γ)
    (associativityTripleCoverToRightMember (J := J) α β γ I)
  have hlocalUp :
      HEq
        (compositionLocal (J := J) (composeOver (J := J) α β) γ I)
        (compositionLocal (J := J) α (composeOver (J := J) β γ)
          (associativityTripleCoverToRightMember (J := J) α β γ I)) :=
    ulift_heq_of_down_heq (hlocal I)
  refine HEq.trans (heq_of_eq hleftRefine) ?_
  exact HEq.trans hcast
    (HEq.trans (heq_of_eq hleftLocal)
      (HEq.trans hlocalUp
        (HEq.trans (heq_of_eq hrightLocal.symm) (by rfl))))

end

end LocallyDefinedHomRepresentativeOver
end FibredCategoryMor

end CategoryTheory
