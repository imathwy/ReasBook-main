import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativityCoherence
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativityLaw

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

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- First source-associativity boundary: after expanding the left bracketing on the triple
cover, the target comparison from the inner composite followed by the outer middle comparison is
the single middle comparison for the right bracketing. -/
theorem associativityTripleCover_targetHom_middleIso_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      (compositionTargetHom (J := J) α β
          (associativityTripleCoverToLeftComposite (J := J) α β γ I) ≫
        (compositionMiddleIso (J := J) (composeOver (J := J) α β) γ I).hom)
      ((compositionMiddleIso (J := J) β γ
        (associativityTripleCoverToRightComposite (J := J) α β γ I)).hom) := by
  dsimp [compositionTargetHom, compositionMiddleIso]
  let Fp := canonicalFiberPseudofunctor X.p
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  rw [← Pseudofunctor.mapComp'_eq_mapComp Fp g.op.toLoc f.op.toLoc]
  have houter :
      HEq
        ((Fp.mapComp' (g.op.toLoc ≫ f.op.toLoc) I.Y.hom.op.toLoc
            ((g.op.toLoc ≫ f.op.toLoc) ≫ I.Y.hom.op.toLoc) (by rfl)).inv.toNatTrans.app yF)
        ((Fp.mapComp' (g.op.toLoc ≫ f.op.toLoc) I.Y.hom.op.toLoc
            (g.op.toLoc ≫ f.op.toLoc ≫ I.Y.hom.op.toLoc)
            (by simp [Category.assoc])).inv.toNatTrans.app yF) := by
    exact Pseudofunctor.mapComp'_inv_app_heq_of_eq
      (F := Fp)
      (U := LocallyDiscrete.mk (op (X.p.obj y)))
      (V := LocallyDiscrete.mk (op (X.p.obj w)))
      (W := LocallyDiscrete.mk (op I.Y.left))
      (f := g.op.toLoc ≫ f.op.toLoc)
      (g := I.Y.hom.op.toLoc)
      (k := (g.op.toLoc ≫ f.op.toLoc) ≫ I.Y.hom.op.toLoc)
      (k' := g.op.toLoc ≫ f.op.toLoc ≫ I.Y.hom.op.toLoc)
      (hk := by simp [Category.assoc])
      (h := by rfl)
      (h' := by simp [Category.assoc])
      yF
  let Iab := associativityTripleCoverToLeftComposite (J := J) α β γ I
  let A :=
    (((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc Iab.Y.hom.op.toLoc
          (f.op.toLoc ≫ Iab.Y.hom.op.toLoc) (by rfl)).hom.toNatTrans.app
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj yF))
  let B :=
      ((canonicalFiberPseudofunctor X.p).map Iab.Y.hom.op.toLoc).toFunctor.map
        ((Fp.mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app
          yF)
  let L := A ≫ B
  let C0 :=
    ((Fp.mapComp' (g.op.toLoc ≫ f.op.toLoc) I.Y.hom.op.toLoc
        ((g.op.toLoc ≫ f.op.toLoc) ≫ I.Y.hom.op.toLoc) (by rfl)).inv.toNatTrans.app yF)
  let C1 :=
    ((Fp.mapComp' (g.op.toLoc ≫ f.op.toLoc) I.Y.hom.op.toLoc
        (g.op.toLoc ≫ f.op.toLoc ≫ I.Y.hom.op.toLoc)
        (by simp [Category.assoc])).inv.toNatTrans.app yF)
  let R :=
    ((Fp.mapComp' g.op.toLoc (f.op.toLoc ≫ I.Y.hom.op.toLoc)
      (g.op.toLoc ≫ f.op.toLoc ≫ I.Y.hom.op.toLoc)
      (by rfl)).inv.toNatTrans.app yF)
  have hstep1 : HEq (L ≫ C0) (L ≫ C1) := by
    refine heq_comp ?_ ?_ ?_ (heq_of_eq rfl) houter
    · simp [yF, Iab, LocallyDefinedHomRepresentative.compositionCoverToLeft]
    · simp [yF, Iab, LocallyDefinedHomRepresentative.compositionCoverToLeft]
    · simp [Fp, yF, Category.assoc]
  have hstep2 : HEq (L ≫ C1) R := by
    have hassoc : HEq (L ≫ C1) (A ≫ (B ≫ C1)) := by
      exact heq_of_eq (Category.assoc A B C1)
    have hcoh : HEq (A ≫ (B ≫ C1)) R := by
      exact heq_of_eq (by
        simpa [Fp, yF, associativityTripleCoverToLeftComposite,
          LocallyDefinedHomRepresentative.compositionCoverToLeft, Iab, A, B, C1, R,
          Category.assoc] using
          (Fp.mapComp'₀₁₃_inv_app
            g.op.toLoc f.op.toLoc I.Y.hom.op.toLoc
            (g.op.toLoc ≫ f.op.toLoc)
            (f.op.toLoc ≫ I.Y.hom.op.toLoc)
            (g.op.toLoc ≫ f.op.toLoc ≫ I.Y.hom.op.toLoc)
            (by rfl) (by rfl) (by simp) yF).symm)
    exact HEq.trans hassoc hcoh
  exact HEq.trans hstep1 hstep2

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Second source-associativity boundary: the target comparison for the left bracketing equals
the two target comparisons appearing in the right bracketing. -/
theorem associativityTripleCover_targetHom_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    {f : X.p.obj w ⟶ X.p.obj x}
    {g : X.p.obj x ⟶ X.p.obj y}
    {k : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (γ : LocallyDefinedHomRepresentativeOver (J := J) X k)
    (I : (associativityTripleCover (J := J) α β γ).Arrow) :
    HEq
      (compositionTargetHom (J := J) (composeOver (J := J) α β) γ I)
      (compositionTargetHom (J := J) β γ
          (associativityTripleCoverToRightComposite (J := J) α β γ I) ≫
        compositionTargetHom (J := J) α (composeOver (J := J) β γ)
          (associativityTripleCoverToRightMember (J := J) α β γ I)) := by
  dsimp [compositionTargetHom]
  let Fp := canonicalFiberPseudofunctor X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  rw [← Pseudofunctor.mapComp'_eq_mapComp Fp k.op.toLoc (g.op.toLoc ≫ f.op.toLoc)]
  rw [← Pseudofunctor.mapComp'_eq_mapComp Fp k.op.toLoc g.op.toLoc]
  rw [← Pseudofunctor.mapComp'_eq_mapComp Fp (k.op.toLoc ≫ g.op.toLoc) f.op.toLoc]
  simpa [Fp, zF, associativityTripleCoverToRightComposite,
    associativityTripleCoverToRightMember,
    LocallyDefinedHomRepresentative.compositionCoverToRight, Category.assoc] using
    (Pseudofunctor.mapComp_target_assoc_heq
      (F := Fp) k.op.toLoc g.op.toLoc f.op.toLoc I.Y.hom.op.toLoc zF)

end LocallyDefinedHomRepresentativeOver
end FibredCategoryMor

end CategoryTheory
