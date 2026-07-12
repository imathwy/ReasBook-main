import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomSourceIdentity

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

/-- Source stage 2.4 left identity, pointwise form: after expanding the local composite of the
literal source identity representative with a fixed representative, the local arrow is
heterogeneously the original local arrow on the induced refinement. -/
theorem sourceIdentityCompositionCoverLeft_local_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J)
      (sourceIdentityHomToRepresentativeOver (J := J) X x) α).Arrow) :
    HEq
      ((compositionLocal (J := J)
        (sourceIdentityHomToRepresentativeOver (J := J) X x) α I).down)
      ((α.family (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow)).down) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  have hleft := sourceIdentityCompositionCoverLeft_leftLocal_down (J := J) α I
  dsimp only at hleft
  dsimp [compositionLocal]
  rw [hleft]
  have hLM := Pseudofunctor.map_mapId_inv_comp_mapComp_id_inv_core
    (F := Fp) I.Y.hom xF
  dsimp [Fp, xF] at hLM
  dsimp [compositionMiddleIso]
  have hM :
      HEq
        (((canonicalFiberPseudofunctor X.p).mapComp'
            (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
            I.Y.hom.op.toLoc (by simp)).inv.toNatTrans.app
          (Functor.Fiber.mk (p := X.p) (a := x) rfl))
        (((canonicalFiberPseudofunctor X.p).mapComp'
            (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
            (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).inv.toNatTrans.app
          (Functor.Fiber.mk (p := X.p) (a := x) rfl)) := by
    exact Pseudofunctor.mapComp'_inv_app_heq_of_eq
      (F := Fp)
      (U := LocallyDiscrete.mk (op (X.p.obj x)))
      (V := LocallyDiscrete.mk (op (X.p.obj x)))
      (W := LocallyDiscrete.mk (op I.Y.left))
      (f := 𝟙 (LocallyDiscrete.mk (op (X.p.obj x))))
      (g := I.Y.hom.op.toLoc)
      (k := I.Y.hom.op.toLoc)
      (k' := 𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc)
      (hk := by simp)
      (h := by simp)
      (h' := rfl)
      xF
  have hfront :
      HEq
        (((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
                (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp'
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).inv.toNatTrans.app
            (Functor.Fiber.mk (p := X.p) (a := x) rfl))
        (𝟙 (((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := x) rfl))) := by
    refine HEq.trans ?_ (heq_of_eq hLM)
    refine heq_comp (by simp) (by simp) (by simp) (heq_of_eq rfl) hM.symm
  have hfrontN :
      HEq
        (((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
                (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp'
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).inv.toNatTrans.app
            (Functor.Fiber.mk (p := X.p) (a := x) rfl))
        (𝟙 (((canonicalFiberPseudofunctor X.p).map
          ((compositionCoverToRight (J := J)
            (sourceIdentityHomToRepresentativeOver (J := J) X x) α I).Y.hom).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := x) rfl))) := by
    have hid :
        HEq
          (𝟙 (((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.obj
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)))
          (𝟙 (((canonicalFiberPseudofunctor X.p).map
            (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc)).toFunctor.obj
            (Functor.Fiber.mk (p := X.p) (a := x) rfl))) := by
      exact congr_arg_heq
        (fun m : LocallyDiscrete.mk (op (X.p.obj x)) ⟶ LocallyDiscrete.mk (op I.Y.left) =>
          𝟙 (((canonicalFiberPseudofunctor X.p).map m).toFunctor.obj
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)))
        (by simp)
    simpa [LocallyDefinedHomRepresentative.compositionCoverToRight_hom] using
      HEq.trans hfront hid
  have hfrontTail :
      HEq
        ((((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
                (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp'
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).inv.toNatTrans.app
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫
          (((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
            (sourceIdentityHomToRepresentativeOver (J := J) X x).compositionTargetHom α I))
        (((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
          (sourceIdentityHomToRepresentativeOver (J := J) X x).compositionTargetHom α I) := by
    refine HEq.trans ?_ (heq_of_eq (Category.id_comp _))
    refine heq_comp (by simp) (by simp) (by simp) hfrontN (heq_of_eq rfl)
  have htail :
      HEq
        (((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
          (sourceIdentityHomToRepresentativeOver (J := J) X x).compositionTargetHom α I)
        ((α.family (⟨I.Y, I.f,
          (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
          α.cover.Arrow)).down) := by
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    have hright := sourceIdentityCompositionCoverLeft_rightLocal_down_heq (J := J) α I
    have htargetCore :=
      canonicalFiberPseudofunctor_leftIdentityTargetTail_comp_transport_core
        (p := X.p) f I.Y.hom yF
    dsimp [compositionTargetHom]
    let zU := (Fp.map f.op.toLoc).toFunctor.obj yF
    let hbase : f = 𝟙 (X.p.obj x) ≫ f := (Category.id_comp f).symm
    let targetTransport :
        zU ⟶ (𝟙 (X.p.obj x) ≫ f) ^*[canonicalPullbackChoice X.p] yF :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k) hbase)).app yF
    have htargetCore' :
        ((Fp.mapComp' (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              I.Y.hom.op.toLoc (by simp)).hom.toNatTrans.app zU) ≫
          (Fp.map I.Y.hom.op.toLoc).toFunctor.map
            ((Fp.mapComp f.op.toLoc (𝟙 (X.p.obj x)).op.toLoc).inv.toNatTrans.app yF) =
        (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport := by
      simpa [Fp, yF, zU, hbase, targetTransport] using htargetCore
    have hhom :
        HEq
          ((Fp.mapComp' (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).hom.toNatTrans.app zU)
          ((Fp.mapComp' (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              I.Y.hom.op.toLoc (by simp)).hom.toNatTrans.app zU) := by
      exact (Pseudofunctor.mapComp'_hom_app_heq_of_eq
        (F := Fp)
        (U := LocallyDiscrete.mk (op (X.p.obj x)))
        (V := LocallyDiscrete.mk (op (X.p.obj x)))
        (W := LocallyDiscrete.mk (op I.Y.left))
        (f := 𝟙 (LocallyDiscrete.mk (op (X.p.obj x))))
        (g := I.Y.hom.op.toLoc)
        (k := I.Y.hom.op.toLoc)
        (k' := 𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc)
        (hk := by simp)
        (h := by simp)
        (h' := rfl)
        zU).symm
    have htarget :
        HEq
          (((Fp.mapComp' (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
                (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).hom.toNatTrans.app zU) ≫
            (Fp.map I.Y.hom.op.toLoc).toFunctor.map
              ((Fp.mapComp f.op.toLoc (𝟙 (X.p.obj x)).op.toLoc).inv.toNatTrans.app yF))
          ((Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport) := by
      refine HEq.trans ?_ (heq_of_eq htargetCore')
      refine heq_comp (by simp) (by simp) (by simp) hhom (heq_of_eq rfl)
    let aLocal :=
      (α.family (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow)).down
    have hzU :
        zU = f ^*[canonicalPullbackChoice X.p] yF := by
      rfl
    have hrightTail :
        HEq
          (((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
            ((Fp.mapComp' (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
                  (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).hom.toNatTrans.app zU) ≫
              (Fp.map I.Y.hom.op.toLoc).toFunctor.map
                ((Fp.mapComp f.op.toLoc (𝟙 (X.p.obj x)).op.toLoc).inv.toNatTrans.app yF))
          (aLocal ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport) := by
      refine heq_comp ?_ ?_ ?_ hright htarget
      · simp [LocallyDefinedHomRepresentative.compositionCoverToRight_hom]
      · simp [LocallyDefinedHomRepresentative.compositionCoverToRight_hom]
      · simp
        change (Fp.map I.Y.hom.op.toLoc).toFunctor.obj zU =
          (Fp.map I.Y.hom.op.toLoc).toFunctor.obj (f ^*[canonicalPullbackChoice X.p] yF)
        rw [hzU]
        rfl
    have hcancel :
        HEq (aLocal ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport) aLocal := by
      simpa [Fp, yF, zU, hbase, targetTransport, aLocal] using
        canonicalFiberPseudofunctor_map_eqToHom_transport_tail_heq
          (p := X.p) hbase I.Y.hom yF (e := aLocal)
    exact HEq.trans hrightTail hcancel
  have hfrontTailR :
      HEq
        (((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
                (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫
          ((canonicalFiberPseudofunctor X.p).mapComp'
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x)))) I.Y.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))) ≫ I.Y.hom.op.toLoc) rfl).inv.toNatTrans.app
            (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫
          ((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
            (sourceIdentityHomToRepresentativeOver (J := J) X x).compositionTargetHom α I)
        (((sourceIdentityHomToRepresentativeOver (J := J) X x).compositionRightLocal α I).down ≫
          (sourceIdentityHomToRepresentativeOver (J := J) X x).compositionTargetHom α I) := by
    refine HEq.trans (heq_of_eq ?_) hfrontTail
    simp only [Category.assoc]
  exact HEq.trans hfrontTailR htail

/-- Source stage 2.4 left identity for the literal source identity representative, promoted from
the pointwise local calculation to the matching-family law. -/
theorem sourceComposeOverLeftIdentityFamilyLaw_holds
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    sourceComposeOverLeftIdentityFamilyLaw (J := J) α := by
  dsimp [sourceComposeOverLeftIdentityFamilyLaw]
  let comp := composeOver (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α
  let hbase : 𝟙 (X.p.obj x) ≫ f = f := by simp
  change castBaseFamily (J := J) hbase comp =
    α.family.refine (sourceIdentityCompositionCoverLeftHom (J := J) α)
  apply Meq.ext
  intro I
  apply eq_of_heq
  have hcast := castBaseFamily_apply_heq (J := J) hbase comp I
  have hcomp := composeOver_family_apply (J := J)
    (sourceIdentityHomToRepresentativeOver (J := J) X x) α I
  have hlocal := sourceIdentityCompositionCoverLeft_local_down_heq (J := J) α I
  have hlocalUp :
      HEq
        (compositionLocal (J := J)
          (sourceIdentityHomToRepresentativeOver (J := J) X x) α I)
        (α.family (⟨I.Y, I.f,
          (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
          α.cover.Arrow)) :=
    ulift_heq_of_down_heq hlocal
  have hrefineUp :
      HEq
        (α.family (⟨I.Y, I.f,
          (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
          α.cover.Arrow))
        ((α.family.refine (sourceIdentityCompositionCoverLeftHom (J := J) α)) I) := by
    rfl
  exact HEq.trans hcast
    (HEq.trans (heq_of_eq hcomp) (HEq.trans hlocalUp hrefineUp))

/-- Source stage 2.4 right identity, pointwise form: after expanding the local composite of a
fixed representative with the literal source identity representative, the local arrow is
heterogeneously the original local arrow on the induced refinement. -/
theorem sourceIdentityCompositionCoverRight_local_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J) α
      (sourceIdentityHomToRepresentativeOver (J := J) X y)).Arrow) :
    HEq
      ((compositionLocal (J := J) α
        (sourceIdentityHomToRepresentativeOver (J := J) X y) I).down)
      ((α.family (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverRightHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow)).down) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  have hleft := sourceIdentityCompositionCoverRight_leftLocal_down_heq (J := J) α I
  have hrightRaw :=
    sourceIdentityHomToRepresentativeOver_family_apply_down (J := J) X y
      (compositionCoverToRight (J := J) α
        (sourceIdentityHomToRepresentativeOver (J := J) X y) I)
  have hright :
      ((compositionRightLocal (J := J) α
        (sourceIdentityHomToRepresentativeOver (J := J) X y) I).down) =
        (Fp.map (I.Y.hom ≫ f).op.toLoc).toFunctor.map
          ((Fp.mapId (LocallyDiscrete.mk (op (X.p.obj y)))).inv.toNatTrans.app yF) := by
    simpa [compositionRightLocal, Fp, yF,
      LocallyDefinedHomRepresentative.compositionCoverToRight_hom] using hrightRaw
  dsimp [compositionLocal]
  rw [hright]
  have htail := Pseudofunctor.mapComp_rightIdentityTail_heq
    (F := Fp) f I.Y.hom yF
    (e := (compositionLeftLocal (J := J) α
      (sourceIdentityHomToRepresentativeOver (J := J) X y) I).down)
  exact HEq.trans
    (by
      simpa [Fp, yF, compositionMiddleIso, compositionTargetHom, Category.assoc] using htail)
    hleft

/-- Source stage 2.4 right identity for the literal source identity representative, promoted
from the pointwise local calculation to the matching-family law. -/
theorem sourceComposeOverRightIdentityFamilyLaw_holds
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    sourceComposeOverRightIdentityFamilyLaw (J := J) α := by
  dsimp [sourceComposeOverRightIdentityFamilyLaw]
  let comp := composeOver (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y)
  let hbase : f ≫ 𝟙 (X.p.obj y) = f := by simp
  change castBaseFamily (J := J) hbase comp =
    α.family.refine (sourceIdentityCompositionCoverRightHom (J := J) α)
  apply Meq.ext
  intro I
  apply eq_of_heq
  have hcast := castBaseFamily_apply_heq (J := J) hbase comp I
  have hcomp := composeOver_family_apply (J := J)
    α (sourceIdentityHomToRepresentativeOver (J := J) X y) I
  have hlocal := sourceIdentityCompositionCoverRight_local_down_heq (J := J) α I
  have hlocalUp :
      HEq
        (compositionLocal (J := J) α
          (sourceIdentityHomToRepresentativeOver (J := J) X y) I)
        (α.family (⟨I.Y, I.f,
          (leOfHom (sourceIdentityCompositionCoverRightHom (J := J) α)) _ I.hf⟩ :
          α.cover.Arrow)) :=
    ulift_heq_of_down_heq hlocal
  have hrefineUp :
      HEq
        (α.family (⟨I.Y, I.f,
          (leOfHom (sourceIdentityCompositionCoverRightHom (J := J) α)) _ I.hf⟩ :
          α.cover.Arrow))
        ((α.family.refine (sourceIdentityCompositionCoverRightHom (J := J) α)) I) := by
    rfl
  exact HEq.trans hcast
    (HEq.trans (heq_of_eq hcomp) (HEq.trans hlocalUp hrefineUp))

end LocallyDefinedHomRepresentativeOver

end FibredCategoryMor

end CategoryTheory
