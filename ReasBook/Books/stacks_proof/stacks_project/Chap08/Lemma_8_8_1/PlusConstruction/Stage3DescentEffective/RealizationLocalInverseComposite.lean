import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseIdentities

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
namespace DescentCompletionObject

/-- Local composite calculation for the glued source side:
`Lambda_I ; Lambda_I^{-1}` is the source overlap after choosing one middle datum-cover member. -/
theorem projectionDescentRealizationComponent_comp_inverse_localComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (A B : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y) (k : W ⟶ K.Y)
    (hAB : a ≫ A.f = b ≫ B.f)
    (hAK : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f)
    (hKB : k ≫ K.f ≫ 𝟙 I.Y = b ≫ B.f) :
    projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K a k hAK ≫
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K B k b hKB =
    ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).overlapIso
        a b hAB).hom := by
  let Source :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let hKA : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f := by
    simpa [Category.assoc] using hAK.symm
  have htarget :=
    projectionDescentRealizationInverseComponent_targetOverlap_sameSource
      (J := J) hSheaf D hPull hComp I K A B k a b hAB hKA hKB
  have hself :=
    projectionDescentRealizationComponent_comp_inverse_self
      (J := J) hSheaf D hPull hComp I A K a k hAK
  dsimp [Source] at htarget
  calc
    projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K a k hAK ≫
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K B k b hKB =
        projectionDescentRealizationComponent (J := J)
            hSheaf D hPull hComp I A K a k hAK ≫
          (projectionDescentRealizationInverseComponent (J := J)
              hSheaf D hPull hComp I K A k a hKA ≫
            (Source.overlapIso a b hAB).hom) := by
          have hrewrite := congrArg
            (fun q =>
              projectionDescentRealizationComponent (J := J)
                hSheaf D hPull hComp I A K a k hAK ≫ q)
            htarget.symm
          simpa [Source, Category.assoc] using hrewrite
    _ =
        (projectionDescentRealizationComponent (J := J)
            hSheaf D hPull hComp I A K a k hAK ≫
          projectionDescentRealizationInverseComponent (J := J)
              hSheaf D hPull hComp I K A k a hKA) ≫
            (Source.overlapIso a b hAB).hom := by
          rw [Category.assoc]
    _ = 𝟙 _ ≫ (Source.overlapIso a b hAB).hom := by
          rw [hself]
    _ = (Source.overlapIso a b hAB).hom := by
          simp

/-- Local composite calculation for the datum side:
`Lambda_I^{-1} ; Lambda_I` is the datum overlap after choosing one middle source-cover member. -/
theorem projectionDescentRealizationInverseComponent_comp_realization_localComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (K L : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y) (a : W ⟶ A.Y)
    (hKL : k ≫ K.f = l ≫ L.f)
    (hKA : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f)
    (hAL : a ≫ A.f ≫ 𝟙 I.Y = l ≫ L.f) :
    projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A k a hKA ≫
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A L a l hAL =
    ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        k l hKL).hom := by
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let hAK : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f := by
    simpa [Category.assoc] using hKA.symm
  have htarget :=
    projectionDescentRealizationComponent_targetOverlap_sameSource
      (J := J) hSheaf D hPull hComp I A K L a k l hKL hAK hAL
  have hself :=
    projectionDescentRealizationInverseComponent_comp_realization_self
      (J := J) hSheaf D hPull hComp I K A k a hKA
  dsimp [Target] at htarget
  calc
    projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A k a hKA ≫
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A L a l hAL =
        projectionDescentRealizationInverseComponent (J := J)
            hSheaf D hPull hComp I K A k a hKA ≫
          (projectionDescentRealizationComponent (J := J)
              hSheaf D hPull hComp I A K a k hAK ≫
            (Target.overlapIso k l hKL).hom) := by
          have hrewrite := congrArg
            (fun q =>
              projectionDescentRealizationInverseComponent (J := J)
                hSheaf D hPull hComp I K A k a hKA ≫ q)
            htarget.symm
          simpa [Target, Category.assoc] using hrewrite
    _ =
        (projectionDescentRealizationInverseComponent (J := J)
            hSheaf D hPull hComp I K A k a hKA ≫
          projectionDescentRealizationComponent (J := J)
              hSheaf D hPull hComp I A K a k hAK) ≫
            (Target.overlapIso k l hKL).hom := by
          rw [Category.assoc]
    _ = 𝟙 _ ≫ (Target.overlapIso k l hKL).hom := by
          rw [hself]
    _ = (Target.overlapIso k l hKL).hom := by
          simp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued composite `Lambda_I ; Lambda_I^{-1}` has the identity component family on
`(glued X)|_{T_I}`. -/
theorem projectionDescentRealizationComponent_comp_inverse_compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hnat :
      projectionDescentRealizationComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hcompat)
    (hinvcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hinvnat :
      projectionDescentRealizationInverseComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hinvcompat)
    {W : C}
    (A B : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f ≫ ((𝟙 I.Y) ≫ (𝟙 I.Y)) = b ≫ B.f) :
    DescentCompletionObjectOver.HomOver.compositionFamily (J := J) hSheaf
        (projectionDescentRealizationHomOver
          (J := J) hSheaf D hPull hComp I hcompat)
        (projectionDescentRealizationInverseHomOver
          (J := J) hSheaf D hPull hComp I hinvcompat)
        hnat hinvnat A B a b h =
      (DescentCompletionObjectOver.idHomOver (J := J)
        (DescentCompletionObjectOver.pullback (J := J)
          (projectionDescentTotalCoverGluedObjectOfTransitionLaws
            (J := J) hSheaf D hPull hComp).object I.f)).family A B a b
        (by simpa [Category.assoc] using h) := by
  let Source :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let α := projectionDescentRealizationHomOver
    (J := J) hSheaf D hPull hComp I hcompat
  let β := projectionDescentRealizationInverseHomOver
    (J := J) hSheaf D hPull hComp I hinvcompat
  let hαnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) α := hnat
  let hβnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) β := hinvnat
  let hid : a ≫ A.f = b ≫ B.f := by
    simpa [Category.assoc] using h
  let M := DescentCompletionObjectOver.HomOver.compositionMiddleCover (J := J)
    (D := Source) (E := Target) (H := Source)
    (f := 𝟙 I.Y) (g := 𝟙 I.Y) A B a b h
  apply fiberHom_ext_of_cover (J := J) X.p M
    (Source.restrictedLocalObject A a) (Source.restrictedLocalObject B b)
    (hSheaf W (Source.restrictedLocalObject A a) (Source.restrictedLocalObject B b))
  intro Kp
  have hmapComp :=
    DescentCompletionObjectOver.HomOver.compositionFamily_map (J := J)
      hSheaf α β hαnat hβnat A B a b h Kp
  have hmapId :=
    DescentCompletionObjectOver.HomOver.overlapIso_map_eq (J := J)
      Source A B a b hid Kp.f
  rw [hmapComp]
  rw [DescentCompletionObjectOver.idHomOver_family, hmapId]
  simp only [DescentCompletionObjectOver.HomOver.compositionMiddleCoverSection,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverSourceIso,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverTargetIso,
    DescentCompletionObjectOver.restrictedLocalObjectCompIso,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv]
  have hlocal :=
    projectionDescentRealizationComponent_comp_inverse_localComposite
      (J := J) hSheaf D hPull hComp I A B Kp.base
      (Kp.f ≫ a) (Kp.f ≫ b) (𝟙 Kp.Y)
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hid)
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simp [Category.assoc])
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h)
  let L :=
    ((canonicalFiberPseudofunctor X.p).mapComp' a.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ a).op.toLoc) (by rfl)).inv.toNatTrans.app (Source.localObject A)
  let R :=
    ((canonicalFiberPseudofunctor X.p).mapComp' b.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ b).op.toLoc) (by rfl)).hom.toNatTrans.app (Source.localObject B)
  have hwrapped := congrArg (fun t => L ≫ t ≫ R) hlocal
  simpa [Source, Target, α, β, hαnat, hβnat, M,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverComposite,
    DescentCompletionObjectOver.HomOver.localComposite,
    projectionDescentRealizationHomOver,
    projectionDescentRealizationInverseHomOver,
    L, R, hid, Category.assoc] using hwrapped

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued composite `Lambda_I^{-1} ; Lambda_I` has the identity component family on `X_I`. -/
theorem projectionDescentRealizationInverseComponent_comp_realization_compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hnat :
      projectionDescentRealizationComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hcompat)
    (hinvcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hinvnat :
      projectionDescentRealizationInverseComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hinvcompat)
    {W : C}
    (K L : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (h : k ≫ K.f ≫ ((𝟙 I.Y) ≫ (𝟙 I.Y)) = l ≫ L.f) :
    DescentCompletionObjectOver.HomOver.compositionFamily (J := J) hSheaf
        (projectionDescentRealizationInverseHomOver
          (J := J) hSheaf D hPull hComp I hinvcompat)
        (projectionDescentRealizationHomOver
          (J := J) hSheaf D hPull hComp I hcompat)
        hinvnat hnat K L k l h =
      (DescentCompletionObjectOver.idHomOver (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)).family K L k l
        (by simpa [Category.assoc] using h) := by
  let Source :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let α := projectionDescentRealizationInverseHomOver
    (J := J) hSheaf D hPull hComp I hinvcompat
  let β := projectionDescentRealizationHomOver
    (J := J) hSheaf D hPull hComp I hcompat
  let hαnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) α := hinvnat
  let hβnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) β := hnat
  let hid : k ≫ K.f = l ≫ L.f := by
    simpa [Category.assoc] using h
  let M := DescentCompletionObjectOver.HomOver.compositionMiddleCover (J := J)
    (D := Target) (E := Source) (H := Target)
    (f := 𝟙 I.Y) (g := 𝟙 I.Y) K L k l h
  apply fiberHom_ext_of_cover (J := J) X.p M
    (Target.restrictedLocalObject K k) (Target.restrictedLocalObject L l)
    (hSheaf W (Target.restrictedLocalObject K k) (Target.restrictedLocalObject L l))
  intro Ap
  have hmapComp :=
    DescentCompletionObjectOver.HomOver.compositionFamily_map (J := J)
      hSheaf α β hαnat hβnat K L k l h Ap
  have hmapId :=
    DescentCompletionObjectOver.HomOver.overlapIso_map_eq (J := J)
      Target K L k l hid Ap.f
  rw [hmapComp]
  rw [DescentCompletionObjectOver.idHomOver_family, hmapId]
  simp only [DescentCompletionObjectOver.HomOver.compositionMiddleCoverSection,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverSourceIso,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverTargetIso,
    DescentCompletionObjectOver.restrictedLocalObjectCompIso,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv]
  have hlocal :=
    projectionDescentRealizationInverseComponent_comp_realization_localComposite
      (J := J) hSheaf D hPull hComp I K L Ap.base
      (Ap.f ≫ k) (Ap.f ≫ l) (𝟙 Ap.Y)
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simpa [Category.assoc] using congrArg (fun q => Ap.f ≫ q) hid)
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simp [Category.assoc])
      (by
        dsimp [M, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
        simpa [Category.assoc] using congrArg (fun q => Ap.f ≫ q) h)
  let Lw :=
    ((canonicalFiberPseudofunctor X.p).mapComp' k.op.toLoc Ap.f.op.toLoc
      ((Ap.f ≫ k).op.toLoc) (by rfl)).inv.toNatTrans.app (Target.localObject K)
  let Rw :=
    ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc Ap.f.op.toLoc
      ((Ap.f ≫ l).op.toLoc) (by rfl)).hom.toNatTrans.app (Target.localObject L)
  have hwrapped := congrArg (fun t => Lw ≫ t ≫ Rw) hlocal
  simpa [Source, Target, α, β, hαnat, hβnat, M,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverComposite,
    DescentCompletionObjectOver.HomOver.localComposite,
    projectionDescentRealizationHomOver,
    projectionDescentRealizationInverseHomOver,
    Lw, Rw, hid, Category.assoc] using hwrapped

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
