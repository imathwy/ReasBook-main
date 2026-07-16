import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.TargetPrimeSquares
import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.CoverEquivalence

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: strictifying a lifted component isomorphism recovers the
target-side component isomorphism used to define it. -/
private theorem pullbackProjection_sourcePrimeComponentIso_hom_strictification
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc)
    (I : T.Arrow) :
    (pullbackProjection_targetFiberFunctor u p I.Y).map
        (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I).hom =
      (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom := by
  -- Unfold the lifted component: it is the fully faithful preimage of the target component.
  let FsrcI := pullbackProjection_targetFiberFunctor u p I.Y
  letI : FsrcI.IsEquivalence := pullbackProjection_targetFiberFunctor_isEquivalence u p I.Y
  let hFsrcI : FsrcI.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful FsrcI
  simpa [pullbackProjection_sourcePrimeComponentIso, FsrcI, hFsrcI]

/-- Helper for Chap08 Lemma 8 12 2: after strictifying on the chosen overlap, the desired
source-prime component square becomes a target-fiber square. -/
private theorem pullbackProjection_sourcePrimeIso_comm_after_strictification
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc)
    (I J₁ : T.Arrow) :
    let sq := coverSourceChosenPullback T I J₁
    let Fover := pullbackProjection_targetFiberFunctor u p sq.pullback
    Fover.map
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map sq.p₁.op.toLoc).toFunctor.map
            (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I).hom ≫
          Dsrc.hom I J₁) =
      Fover.map
        (((pullbackProjection_sourcePrimeDescentFunctor u p T).obj
              (pullbackProjection_ofTargetFiberObj u p A)).hom I J₁ ≫
          ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map sq.p₂.op.toLoc).toFunctor.map
            (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e J₁).hom) := by
  -- Conjugate by the endpoint target-restriction comparisons; the conjugated square is the
  -- target descent-data naturality square for `e`.
  let sq := coverSourceChosenPullback T I J₁
  let Fover := pullbackProjection_targetFiberFunctor u p sq.pullback
  let X := pullbackProjection_ofTargetFiberObj u p A
  let B := pullbackProjection_targetFiberObj u p X
  let D₀ :=
    (pullbackProjection_sourcePrimeDescentFunctor u p T).obj
      X
  let eLeft := pullbackProjection_targetRestrictionIso u p sq.p₁ (D₀.obj I)
  let eRight := pullbackProjection_targetRestrictionIso u p sq.p₂ (Dsrc.obj J₁)
  let eDLeft := pullbackProjection_targetRestrictionIso u p sq.p₁ (Dsrc.obj I)
  let eD0Right := pullbackProjection_targetRestrictionIso u p sq.p₂ (D₀.obj J₁)
  let sourceLeft :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map sq.p₁.op.toLoc).toFunctor.map
      (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I).hom
  let sourceRight :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map sq.p₂.op.toLoc).toFunctor.map
      (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e J₁).hom
  let betaI :
      pullbackProjection_targetFiberObj u p (D₀.obj I) ≅
        ((pullbackProjection_targetPrimeDescentFunctor u p T).obj A).obj I :=
    pullbackProjection_targetRestrictionIso u p I.f X ≪≫
      (((canonicalFiberPseudofunctor p).map (u.map I.f).op.toLoc).toFunctor.mapIso
        (pullbackProjection_targetFiberCounitIso u p A))
  let betaJ :
      pullbackProjection_targetFiberObj u p (D₀.obj J₁) ≅
        ((pullbackProjection_targetPrimeDescentFunctor u p T).obj A).obj J₁ :=
    pullbackProjection_targetRestrictionIso u p J₁.f X ≪≫
      (((canonicalFiberPseudofunctor p).map (u.map J₁.f).op.toLoc).toFunctor.mapIso
        (pullbackProjection_targetFiberCounitIso u p A))
  have hleftNat :
      eLeft.inv ≫ Fover.map sourceLeft ≫ eDLeft.hom =
        ((canonicalFiberPseudofunctor p).map
            (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor.map
          (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom := by
    have hnat :=
      pullbackProjection_targetRestrictionIso_naturality_over_vertical u p sq.p₁
        (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I).hom
    simpa [sourceLeft, eLeft, eDLeft, Fover, sq, coverImageChosenPullback,
      imageChosenPullback,
      pullbackProjection_sourcePrimeComponentIso_hom_strictification u p T Dsrc A e I]
      using hnat
  have hrightNat :
      eD0Right.inv ≫ Fover.map sourceRight ≫ eRight.hom =
        ((canonicalFiberPseudofunctor p).map
            (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor.map
          (pullbackProjection_targetStrictComponentIso u p T Dsrc A e J₁).hom := by
    have hnat :=
      pullbackProjection_targetRestrictionIso_naturality_over_vertical u p sq.p₂
        (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e J₁).hom
    simpa [sourceRight, eD0Right, eRight, Fover, sq, coverImageChosenPullback,
      imageChosenPullback,
      pullbackProjection_sourcePrimeComponentIso_hom_strictification u p T Dsrc A e J₁]
      using hnat
  have hDsrc :
      eDLeft.inv ≫ Fover.map (Dsrc.hom I J₁) ≫ eRight.hom =
        (pullbackProjection_targetDescentDataPrime u p T Dsrc).hom I J₁ := by
    rfl
  have hD₀ :
      eLeft.inv ≫ Fover.map (D₀.hom I J₁) ≫ eD0Right.hom =
        (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁ := by
    rfl
  have hbeta :
      ((canonicalFiberPseudofunctor p).map
          (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor.map betaI.hom ≫
        ((pullbackProjection_targetPrimeDescentFunctor u p T).obj A).hom I J₁ =
      (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁ ≫
        ((canonicalFiberPseudofunctor p).map
          (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor.map betaJ.hom := by
    -- Split `betaI` and `betaJ` into restriction and counit factors, then paste the
    -- restriction square with the counit naturality square.
    let F₁ :=
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor
    let F₂ :=
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor
    let gammaI := (pullbackProjection_targetRestrictionIso u p I.f X).hom
    let gammaJ := (pullbackProjection_targetRestrictionIso u p J₁.f X).hom
    let deltaI :=
      ((canonicalFiberPseudofunctor p).map (u.map I.f).op.toLoc).toFunctor.map
        (pullbackProjection_targetFiberCounitIso u p A).hom
    let deltaJ :=
      ((canonicalFiberPseudofunctor p).map (u.map J₁.f).op.toLoc).toFunctor.map
        (pullbackProjection_targetFiberCounitIso u p A).hom
    let homA := ((pullbackProjection_targetPrimeDescentFunctor u p T).obj A).hom I J₁
    let homB := ((pullbackProjection_targetPrimeDescentFunctor u p T).obj B).hom I J₁
    let homD₀ := (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁
    have hres : F₁.map gammaI ≫ homB = homD₀ ≫ F₂.map gammaJ := by
      simpa [F₁, F₂, gammaI, gammaJ, homB, homD₀, X, B, D₀] using
        pullbackProjection_targetRestriction_primeFunctor_hom u p T A I J₁
    have hcounit : F₁.map deltaI ≫ homA = homB ≫ F₂.map deltaJ := by
      simpa [F₁, F₂, deltaI, deltaJ, homA, homB, X, B] using
        pullbackProjection_targetFiberCounit_primeFunctor_hom u p T A I J₁
    have hpaste :
        (F₁.map gammaI ≫ F₁.map deltaI) ≫ homA =
          homD₀ ≫ (F₂.map gammaJ ≫ F₂.map deltaJ) :=
      compCompCompEqOfPaste hres hcounit
    have hmapI : F₁.map betaI.hom = F₁.map gammaI ≫ F₁.map deltaI := by
      simp only [betaI, gammaI, deltaI, Iso.trans_hom, Functor.mapIso_hom]
      exact F₁.map_comp gammaI deltaI
    have hmapJ : F₂.map betaJ.hom = F₂.map gammaJ ≫ F₂.map deltaJ := by
      simp only [betaJ, gammaJ, deltaJ, Iso.trans_hom, Functor.mapIso_hom]
      exact F₂.map_comp gammaJ deltaJ
    change F₁.map betaI.hom ≫ homA = homD₀ ≫ F₂.map betaJ.hom
    exact
      (congrArg (fun m ↦ m ≫ homA) hmapI).trans
        (hpaste.trans (congrArg (fun m ↦ homD₀ ≫ m) hmapJ.symm))
  have he := e.hom.comm I J₁
  let targetLeft :=
    ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor.map
        (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom ≫
      (pullbackProjection_targetDescentDataPrime u p T Dsrc).hom I J₁
  let targetRight :=
    (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁ ≫
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor.map
        (pullbackProjection_targetStrictComponentIso u p T Dsrc A e J₁).hom
  have hstrict :
      targetLeft = targetRight := by
    -- Expand each strict component as the two-factor comparison `beta` followed by the
    -- component of the target-prime descent-data isomorphism.
    let F₁ :=
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor
    let F₂ :=
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor
    let homD₀ := (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁
    let homDsrc := (pullbackProjection_targetDescentDataPrime u p T Dsrc).hom I J₁
    have hstrictHomI :
        (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom =
          betaI.hom ≫ e.hom.hom I := by
      simp only [X, pullbackProjection_targetStrictComponentIso, betaI,
        descentDataPrimeComponentIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rfl
    have hstrictHomJ :
        (pullbackProjection_targetStrictComponentIso u p T Dsrc A e J₁).hom =
          betaJ.hom ≫ e.hom.hom J₁ := by
      simp only [X, pullbackProjection_targetStrictComponentIso, betaJ,
        descentDataPrimeComponentIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rfl
    have hmapI :
        F₁.map (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom =
          F₁.map betaI.hom ≫ F₁.map (e.hom.hom I) := by
      rw [hstrictHomI]
      exact F₁.map_comp betaI.hom (e.hom.hom I)
    have hmapJ :
        F₂.map (pullbackProjection_targetStrictComponentIso u p T Dsrc A e J₁).hom =
          F₂.map betaJ.hom ≫ F₂.map (e.hom.hom J₁) := by
      rw [hstrictHomJ]
      exact F₂.map_comp betaJ.hom (e.hom.hom J₁)
    -- Paste the `beta` square with the target-prime descent-data naturality square for `e`.
    have hpaste :
        (F₁.map betaI.hom ≫ F₁.map (e.hom.hom I)) ≫ homDsrc =
          homD₀ ≫ (F₂.map betaJ.hom ≫ F₂.map (e.hom.hom J₁)) :=
      compCompCompEqOfPaste hbeta he
    change
      F₁.map (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I).hom ≫ homDsrc =
        homD₀ ≫ F₂.map (pullbackProjection_targetStrictComponentIso u p T Dsrc A e J₁).hom
    exact
      (congrArg (fun m ↦ m ≫ homDsrc) hmapI).trans
        (hpaste.trans (congrArg (fun m ↦ homD₀ ≫ m) hmapJ.symm))
  refine (cancel_mono eRight.hom).1 ?_
  refine (cancel_epi eLeft.inv).1 ?_
  change
    eLeft.inv ≫ (Fover.map (sourceLeft ≫ Dsrc.hom I J₁) ≫ eRight.hom) =
      eLeft.inv ≫ (Fover.map (D₀.hom I J₁ ≫ sourceRight) ≫ eRight.hom)
  have hleftFinal :
      eLeft.inv ≫ (Fover.map (sourceLeft ≫ Dsrc.hom I J₁) ≫ eRight.hom) =
        targetLeft := by
    -- Split the mapped composite, insert the middle comparison isomorphism, and consume the
    -- two named target-side normal forms.
    calc
      eLeft.inv ≫ (Fover.map (sourceLeft ≫ Dsrc.hom I J₁) ≫ eRight.hom) =
          eLeft.inv ≫ Fover.map sourceLeft ≫ Fover.map (Dsrc.hom I J₁) ≫
            eRight.hom := by
            exact mapCompWhisker Fover eLeft.inv sourceLeft (Dsrc.hom I J₁)
              eRight.hom
      _ =
          eLeft.inv ≫ Fover.map sourceLeft ≫ (eDLeft.hom ≫ eDLeft.inv) ≫
            Fover.map (Dsrc.hom I J₁) ≫ eRight.hom := by
            simpa only [Category.assoc] using
              compIsoHomInvWhisker (eLeft.inv ≫ Fover.map sourceLeft) eDLeft
                (Fover.map (Dsrc.hom I J₁)) eRight.hom
      _ =
          (eLeft.inv ≫ Fover.map sourceLeft ≫ eDLeft.hom) ≫
            (eDLeft.inv ≫ Fover.map (Dsrc.hom I J₁) ≫ eRight.hom) := by
            simp only [Category.assoc]
      _ = targetLeft := by
            rw [hleftNat, hDsrc]
            rfl
  have hrightFinal :
      targetRight =
        eLeft.inv ≫ (Fover.map (D₀.hom I J₁ ≫ sourceRight) ≫ eRight.hom) := by
    -- The right endpoint is the same calculation with the comparison for `D₀` at `J₁`.
    calc
      targetRight =
          (eLeft.inv ≫ Fover.map (D₀.hom I J₁) ≫ eD0Right.hom) ≫
            (eD0Right.inv ≫ Fover.map sourceRight ≫ eRight.hom) := by
            rw [hD₀, hrightNat]
            rfl
      _ =
          eLeft.inv ≫ Fover.map (D₀.hom I J₁) ≫ Fover.map sourceRight ≫
            eRight.hom := by
            simpa only [Category.assoc] using
              (compIsoHomInvWhisker (eLeft.inv ≫ Fover.map (D₀.hom I J₁))
                eD0Right (Fover.map sourceRight) eRight.hom).symm
      _ =
          eLeft.inv ≫ (Fover.map (D₀.hom I J₁ ≫ sourceRight) ≫ eRight.hom) := by
            exact (mapCompWhisker Fover eLeft.inv (D₀.hom I J₁) sourceRight
              eRight.hom).symm
  exact hleftFinal.trans (hstrict.trans hrightFinal)

/-- Helper for Chap08 Lemma 8 12 2: the lifted component isomorphisms commute with the source
prime descent morphisms. -/
private theorem pullbackProjection_sourcePrimeIso_comm
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc)
    (I J₁ : T.Arrow) :
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
          (coverSourceChosenPullback T I J₁).p₁.op.toLoc).toFunctor.map
        (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I).hom ≫
      Dsrc.hom I J₁ =
    ((pullbackProjection_sourcePrimeDescentFunctor u p T).obj
        (pullbackProjection_ofTargetFiberObj u p A)).hom I J₁ ≫
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
          (coverSourceChosenPullback T I J₁).p₂.op.toLoc).toFunctor.map
        (pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e J₁).hom := by
  -- Apply the fully faithful strictification functor on the chosen source overlap.
  let sq := coverSourceChosenPullback T I J₁
  let Fover := pullbackProjection_targetFiberFunctor u p sq.pullback
  letI : Fover.IsEquivalence := pullbackProjection_targetFiberFunctor_isEquivalence u p sq.pullback
  let hFover : Fover.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Fover
  exact hFover.map_injective
    (pullbackProjection_sourcePrimeIso_comm_after_strictification u p T Dsrc A e I J₁)

/-- Helper for Chap08 Lemma 8 12 2: a target-effective prime descent object gives the required
source prime descent object. -/
private noncomputable def pullbackProjection_sourcePrimeIso
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc) :
    (pullbackProjection_sourcePrimeDescentFunctor u p T).obj
        (pullbackProjection_ofTargetFiberObj u p A) ≅ Dsrc :=
  Pseudofunctor.DescentData'.isoMk
    (fun I ↦ pullbackProjection_sourcePrimeComponentIso u p T Dsrc A e I)
    (pullbackProjection_sourcePrimeIso_comm u p T Dsrc A e)

/-- Helper for Chap08 Lemma 8 12 2: source descent data for the pullback projection are
objectwise in the essential image of the canonical descent functor. -/
private theorem pullbackProjection_cover_toDescentData_essSurj
    [Functor.IsContinuous u J K]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [IsStackOnSite K p] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).EssSurj := by
  -- Strictify the source prime datum to the target image cover, descend it on the target stack,
  -- then lift the chosen target object back through the pullback projection.
  refine ⟨?_⟩
  intro Dfull
  let sourceEqv :=
    Pseudofunctor.DescentData'.descentDataEquivalence
      (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
      (coverSourceChosenPullback S) (coverSourceChosenPullback₃ S)
  let Dsrc := sourceEqv.inverse.obj Dfull
  let targetPrimeFunctor := pullbackProjection_targetPrimeDescentFunctor u p S
  have hTargetFull :
      ((canonicalFiberPseudofunctor p).toDescentData
        (fun I : S.Arrow ↦ u.map I.f)).IsEquivalence :=
    targetStack_imageDescentFunctor_isEquivalence (J := J) (K := K) u p S
  let targetEqv :=
    Pseudofunctor.DescentData'.descentDataEquivalence
      (canonicalFiberPseudofunctor p) (coverImageChosenPullback u S) (coverImageChosenPullback₃ u S)
  have hTargetPrime : targetPrimeFunctor.IsEquivalence := by
    dsimp [targetPrimeFunctor, pullbackProjection_targetPrimeDescentFunctor]
    exact
      @Functor.isEquivalence_trans _ _ _ _ _ _
        ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ u.map I.f))
        targetEqv.inverse hTargetFull inferInstance
  letI : targetPrimeFunctor.IsEquivalence := hTargetPrime
  obtain ⟨A, ⟨eA⟩⟩ :=
    Functor.EssSurj.mem_essImage
      (F := targetPrimeFunctor) (pullbackProjection_targetDescentDataPrime u p S Dsrc)
  let X := pullbackProjection_ofTargetFiberObj u p A
  refine ⟨X, ⟨?_⟩⟩
  let ePrime := pullbackProjection_sourcePrimeIso u p S Dsrc A eA
  exact
    (sourceEqv.counitIso.app (((canonicalFiberPseudofunctor
      (CategoricalPullback.π₁ u p)).toDescentData (fun I : S.Arrow ↦ I.f)).obj X)).symm ≪≫
      sourceEqv.functor.mapIso ePrime ≪≫
      sourceEqv.counitIso.app Dfull

/-- Helper for Chap08 Lemma 8 12 2: fixed-cover canonical descent for the categorical pullback
projection is the remaining coverwise bridge needed to assemble the stack condition. -/
theorem pullbackProjection_coverwiseCanonicalDescentFunctor_isEquivalence
    [Functor.IsContinuous u J K]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [IsStackOnSite K p] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  -- Route correction: the full descent-transport equivalence is stronger than needed for full
  -- faithfulness. First install the explicit Hom-sheaf prestack proof, then isolate the remaining
  -- objectwise effectiveness problem as essential surjectivity.
  letI :
      Pseudofunctor.IsPrestack
        (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J :=
    pullbackProjection_canonicalFiber_isPrestack (J := J) (K := K) u p
  have hEss :
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
        (fun I : S.Arrow ↦ I.f)).EssSurj :=
    pullbackProjection_cover_toDescentData_essSurj (J := J) (K := K) u p S
  exact pullbackProjection_cover_isEquivalence_of_prestack_essSurj u p S hEss

end

end CategoryTheory
