import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_42_5
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.TerminalCovers
import stacks_proof.stacks_project.Chap08.Definition_8_5_1
import stacks_proof.stacks_project.Chap08.Definition_8_6_1
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6.FixedCoverEquivalenceBridge
import stacks_proof.stacks_project.Chap08.Lemma_8_6_3
import stacks_proof.stacks_project.Chap08.Lemma_8_6_11.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FibredInGroupoidsOver C}
variable [IsStackInGroupoids J T.p]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)


/-- Helper for Chap08 Lemma 8 6 11: slice iso-class gluing supplies essential surjectivity of
the fixed-cover canonical descent functor on the source. -/
private theorem canonicalDescentFunctor_essSurj_of_sliceIsoClassSheaves
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hSheaf :
      ∀ {V : C} (G : ofFunctor (Over.forget V) ⟶ T),
        Presheaf.IsSheaf (J.over V) ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)).EssSurj := by
  -- Glue the local slice-pairs attached to a source descent datum; the glued pair supplies the
  -- global source object, and the local slice isomorphisms give the descent comparison.
  classical
  let ΦX := (canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let ΦT := (canonicalFiberPseudofunctor T.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let H := FibredInGroupoidsMor.toFibredCategoryMor F
  have hTarget : ΦT.IsEquivalence := canonicalDescentFunctor_isEquivalence_of_stack T S
  letI : ΦT.EssSurj := hTarget.essSurj
  refine ⟨?_⟩
  intro D
  let Ψ := cover_descent_data_functor_of_stack_morphism H S
  obtain ⟨y, ⟨eTarget⟩⟩ := Functor.EssSurj.mem_essImage (F := ΦT) (Ψ.obj D)
  let G := fiberObjectSliceMorphism T y
  let P := ((F.sliceTwoFibreProduct G).p).fiberIsoClassPresheaf
  let π : (I : S.Arrow) → Over.mk I.f ⟶ Over.mk (𝟙 U) := fun I ↦ Over.homMk I.f
  let localClass : (I : S.Arrow) → P.obj (Opposite.op (Over.mk I.f)) := fun I ↦
    Quotient.mk''
      (sliceLocalObject F y (Over.mk I.f) (D.obj I)
        ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫ eTarget.hom.hom I))
  have hcompatible : Presieve.Arrows.Compatible P π localClass := by
    intro I J Z fI fJ hcomm
    -- Route correction: rather than proving one large arbitrary-overlap square, normalize each
    -- restricted slice representative over `Z` and then compare the two normal forms.
    have hfI : fI.left ≫ I.f = Z.hom := by
      simpa using (Over.w fI)
    have hfJ : fJ.left ≫ J.f = Z.hom := by
      simpa using (Over.w fJ)
    let eZ := fiberObjectSliceMorphism_evaluationIso T y Z
    let xI : X.p.Fiber Z.left :=
      ((canonicalFiberPseudofunctor X.p).map fI.left.op.toLoc).toFunctor.obj (D.obj I)
    let xJ : X.p.Fiber Z.left :=
      ((canonicalFiberPseudofunctor X.p).map fJ.left.op.toLoc).toFunctor.obj (D.obj J)
    let cI := (canonicalFiberPseudofunctor T.p).mapComp'
      I.f.op.toLoc fI.left.op.toLoc Z.hom.op.toLoc
      (comp_toLoc_eq I.f fI.left Z.hom hfI)
    let cJ := (canonicalFiberPseudofunctor T.p).mapComp'
      J.f.op.toLoc fJ.left.op.toLoc Z.hom.op.toLoc
      (comp_toLoc_eq J.f fJ.left Z.hom hfJ)
    let eFI := FibredCategoryMor.pullbackComparison H fI.left (D.obj I)
    let eFJ := FibredCategoryMor.pullbackComparison H fJ.left (D.obj J)
    let τI :
        (fiberFunctor G Z.left).obj (⟨Z, rfl⟩ : (Over.forget U).Fiber Z.left) ⟶
          (fiberFunctor F Z.left).obj xI :=
      eZ.hom ≫ cI.hom.toNatTrans.app y ≫
        ((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
          (eTarget.hom.hom I) ≫ eFI.hom
    let τJ :
        (fiberFunctor G Z.left).obj (⟨Z, rfl⟩ : (Over.forget U).Fiber Z.left) ⟶
          (fiberFunctor F Z.left).obj xJ :=
      eZ.hom ≫ cJ.hom.toNatTrans.app y ≫
        ((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
          (eTarget.hom.hom J) ≫ eFJ.hom
    have hbI : X.p.IsHomLift fI.left ((canonicalPullbackChoice X.p).map fI.left (D.obj I)) := by
      simpa using
        ((canonicalPullbackChoice X.p).isStronglyCartesian fI.left (D.obj I)).toIsHomLift
    have hbJ : X.p.IsHomLift fJ.left ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)) := by
      simpa using
        ((canonicalPullbackChoice X.p).isStronglyCartesian fJ.left (D.obj J)).toIsHomLift
    have hleft := sliceLocalClass_restrict_eq_of_sourceTargetSquare
      (F := F) (y := y) (a := fI)
      (xV := D.obj I)
      (τV := (fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫ eTarget.hom.hom I)
      (xW := xI)
      (τW := τI)
      (b := (canonicalPullbackChoice X.p).map fI.left (D.obj I))
      (hb := hbI)
      (hτ := by
        -- The cover-evaluation comparison restricted along `fI` agrees with the arbitrary
        -- evaluation comparison at `Z`; then the target descent morphism is pulled back through
        -- the stack-morphism comparison.
        have hrestrict :=
          fiberObjectSliceMorphism_coverEvaluationIso_restrict_hom
            (Y := T) (S := S) y I fI
        have hmap :=
          canonical_pullbackFunctor_map_fac
            (p := T.p) (f := fI.left) (φ := eTarget.hom.hom I)
        have hpost := FibredCategoryMor.pullbackComparison_hom_postcompose
          H fI.left (D.obj I)
        have hpost' :
            (canonicalPullbackChoice T.p).map fI.left ((Ψ.obj D).obj I) =
              eFI.hom.1 ≫
                (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fI.left (D.obj I)) := by
          -- The owner lemma spells the target component through the raw fiber functor; this
          -- bridge records the same postcomposition in the descent-data-functor spelling.
          change
            (canonicalPullbackChoice T.toFibredCategoryOver.p).map fI.left
                ((FibredCategoryMor.fiberFunctor H I.Y).obj (D.obj I)) =
              (FibredCategoryMor.pullbackComparison H fI.left (D.obj I)).hom.1 ≫
                (SubTwoCategory.Hom.toHom H).map
                  ((canonicalPullbackChoice X.toFibredCategoryOver.p).map fI.left (D.obj I))
          exact hpost.symm
        have htail :
            (canonicalPullbackChoice T.p).map fI.left ((ΦT.obj y).obj I) ≫
                (eTarget.hom.hom I).1 =
              (((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
                  (eTarget.hom.hom I)).1 ≫
                (eFI.hom.1 ≫
                  (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fI.left (D.obj I))) := by
          -- Combine the target pullback functoriality with the stack-morphism pullback bridge
          -- before reattaching the common left pre.
          exact hmap.symm.trans
            (congrArg
              (fun k ↦
                (((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
                    (eTarget.hom.hom I)).1 ≫ k)
              hpost')
        change
          (toBasedFunctor (fiberObjectSliceMorphism T y)).map fI ≫
              ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom.1 ≫
                (eTarget.hom.hom I).1) =
            τI.1 ≫
              (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fI.left (D.obj I))
        have hstart :
            ((toBasedFunctor (fiberObjectSliceMorphism T y)).map fI ≫
                (fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom.1) ≫
              (eTarget.hom.hom I).1 =
            (eZ.hom.1 ≫
                ((cI.hom.toNatTrans.app y).1 ≫
                  (canonicalPullbackChoice T.p).map fI.left ((ΦT.obj y).obj I))) ≫
              (eTarget.hom.hom I).1 := by
          simpa only [ΦT, cI, eZ] using
            congrArg (fun k ↦ k ≫ (eTarget.hom.hom I).1) hrestrict
        have hfinish :
            (eZ.hom.1 ≫
                ((cI.hom.toNatTrans.app y).1 ≫
                  (canonicalPullbackChoice T.p).map fI.left ((ΦT.obj y).obj I))) ≫
              (eTarget.hom.hom I).1 =
              τI.1 ≫
                (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fI.left (D.obj I)) := by
          -- Reassociate the prefixed target-side pullback square into the chosen normal form `τI`.
          have hprefix :=
            congrArg (fun k ↦ eZ.hom.1 ≫ ((cI.hom.toNatTrans.app y).1 ≫ k)) htail
          have htail' :
              (fun k ↦ eZ.hom.1 ≫ ((cI.hom.toNatTrans.app y).1 ≫ k))
                (((((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
                  (eTarget.hom.hom I))).1 ≫
                  (eFI.hom.1 ≫
                    (toBasedFunctor F).map
                      ((canonicalPullbackChoice X.p).map fI.left (D.obj I)))) =
                τI.1 ≫
                  (toBasedFunctor F).map
                    ((canonicalPullbackChoice X.p).map fI.left (D.obj I)) := by
            -- Project the fiber composite defining `τI` to the total category, then only
            -- reassociate; this avoids asking `simp` to unfold the whole fiber structure.
            change
              eZ.hom.1 ≫ (cI.hom.toNatTrans.app y).1 ≫
                  (((((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
                    (eTarget.hom.hom I))).1 ≫
                    (eFI.hom.1 ≫
                      (toBasedFunctor F).map
                        ((canonicalPullbackChoice X.p).map fI.left (D.obj I)))) =
                (eZ.hom.1 ≫ (cI.hom.toNatTrans.app y).1 ≫
                    ((((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
                      (eTarget.hom.hom I))).1 ≫ eFI.hom.1) ≫
                  (toBasedFunctor F).map
                    ((canonicalPullbackChoice X.p).map fI.left (D.obj I))
            simp only [Category.assoc]
          simpa only [Category.assoc] using hprefix.trans htail'
        exact (Category.assoc _ _ _).symm.trans (hstart.trans hfinish))
    have hright := sliceLocalClass_restrict_eq_of_sourceTargetSquare
      (F := F) (y := y) (a := fJ)
      (xV := D.obj J)
      (τV := (fiberObjectSliceMorphism_coverEvaluationIso T S y J).hom ≫ eTarget.hom.hom J)
      (xW := xJ)
      (τW := τJ)
      (b := (canonicalPullbackChoice X.p).map fJ.left (D.obj J))
      (hb := hbJ)
      (hτ := by
        -- The right cover-local representative is normalized in the same one-arrow form.
        have hrestrict :=
          fiberObjectSliceMorphism_coverEvaluationIso_restrict_hom
            (Y := T) (S := S) y J fJ
        have hmap :=
          canonical_pullbackFunctor_map_fac
            (p := T.p) (f := fJ.left) (φ := eTarget.hom.hom J)
        have hpost := FibredCategoryMor.pullbackComparison_hom_postcompose
          H fJ.left (D.obj J)
        have hpost' :
            (canonicalPullbackChoice T.p).map fJ.left ((Ψ.obj D).obj J) =
              eFJ.hom.1 ≫
                (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)) := by
          -- The right side uses the same spelling bridge for the target descent component.
          change
            (canonicalPullbackChoice T.toFibredCategoryOver.p).map fJ.left
                ((FibredCategoryMor.fiberFunctor H J.Y).obj (D.obj J)) =
              (FibredCategoryMor.pullbackComparison H fJ.left (D.obj J)).hom.1 ≫
                (SubTwoCategory.Hom.toHom H).map
                  ((canonicalPullbackChoice X.toFibredCategoryOver.p).map fJ.left (D.obj J))
          exact hpost.symm
        have htail :
            (canonicalPullbackChoice T.p).map fJ.left ((ΦT.obj y).obj J) ≫
                (eTarget.hom.hom J).1 =
              (((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
                  (eTarget.hom.hom J)).1 ≫
                (eFJ.hom.1 ≫
                  (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fJ.left (D.obj J))) := by
          -- Combine the right target pullback functoriality with the stack-morphism bridge.
          exact hmap.symm.trans
            (congrArg
              (fun k ↦
                (((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
                    (eTarget.hom.hom J)).1 ≫ k)
              hpost')
        change
          (toBasedFunctor (fiberObjectSliceMorphism T y)).map fJ ≫
              ((fiberObjectSliceMorphism_coverEvaluationIso T S y J).hom.1 ≫
                (eTarget.hom.hom J).1) =
            τJ.1 ≫
              (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fJ.left (D.obj J))
        have hstart :
            ((toBasedFunctor (fiberObjectSliceMorphism T y)).map fJ ≫
                (fiberObjectSliceMorphism_coverEvaluationIso T S y J).hom.1) ≫
              (eTarget.hom.hom J).1 =
            (eZ.hom.1 ≫
                ((cJ.hom.toNatTrans.app y).1 ≫
                  (canonicalPullbackChoice T.p).map fJ.left ((ΦT.obj y).obj J))) ≫
              (eTarget.hom.hom J).1 := by
          simpa only [ΦT, cJ, eZ] using
            congrArg (fun k ↦ k ≫ (eTarget.hom.hom J).1) hrestrict
        have hfinish :
            (eZ.hom.1 ≫
                ((cJ.hom.toNatTrans.app y).1 ≫
                  (canonicalPullbackChoice T.p).map fJ.left ((ΦT.obj y).obj J))) ≫
              (eTarget.hom.hom J).1 =
              τJ.1 ≫
                (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)) := by
          -- Reassociate the prefixed target-side pullback square into the chosen normal form `τJ`.
          have hprefix :=
            congrArg (fun k ↦ eZ.hom.1 ≫ ((cJ.hom.toNatTrans.app y).1 ≫ k)) htail
          have htail' :
              (fun k ↦ eZ.hom.1 ≫ ((cJ.hom.toNatTrans.app y).1 ≫ k))
                (((((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
                  (eTarget.hom.hom J))).1 ≫
                  (eFJ.hom.1 ≫
                    (toBasedFunctor F).map
                      ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)))) =
                τJ.1 ≫
                  (toBasedFunctor F).map
                    ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)) := by
            -- Project the fiber composite defining `τJ` to the total category, then only
            -- reassociate; this is the right-hand copy of the `τI` normalization above.
            change
              eZ.hom.1 ≫ (cJ.hom.toNatTrans.app y).1 ≫
                  (((((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
                    (eTarget.hom.hom J))).1 ≫
                    (eFJ.hom.1 ≫
                      (toBasedFunctor F).map
                        ((canonicalPullbackChoice X.p).map fJ.left (D.obj J)))) =
                (eZ.hom.1 ≫ (cJ.hom.toNatTrans.app y).1 ≫
                    ((((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
                      (eTarget.hom.hom J))).1 ≫ eFJ.hom.1) ≫
                  (toBasedFunctor F).map
                    ((canonicalPullbackChoice X.p).map fJ.left (D.obj J))
            simp only [Category.assoc]
          simpa only [Category.assoc] using hprefix.trans htail'
        exact (Category.assoc _ _ _).symm.trans (hstart.trans hfinish))
    have hlocal :
        @Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct G).p).Fiber Z))
            (sliceLocalObject F y Z xI τI) =
          @Quotient.mk'' _
            (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct G).p).Fiber Z))
            (sliceLocalObject F y Z xJ τJ) := by
      -- The source descent isomorphism gives the source part; `eTarget.hom.comm` supplies the
      -- target square after both sides have been normalized over the common slice object.
      rw [Quotient.eq'']
      let eSource := D.iso Z.hom fI.left fJ.left hfI hfJ
      have htriangle :
          τI ≫ (fiberFunctor F Z.left).map eSource.hom = τJ := by
        -- Project the fiber equality to the total category and compare both sides after
        -- inserting the inverse/right comparison pair from the transported target overlap.
        apply Functor.Fiber.hom_ext
        change
          τI.1 ≫
              (toBasedFunctor F).map (D.hom Z.hom fI.left fJ.left hfI hfJ).1 =
            τJ.1
        let d := D.hom Z.hom fI.left fJ.left hfI hfJ
        let fD := (toBasedFunctor F).map d.1
        let a := eZ.hom.1
        let bI := (cI.hom.toNatTrans.app y).1
        let bIinv := (cI.inv.toNatTrans.app y).1
        let bJ := (cJ.hom.toNatTrans.app y).1
        let mI :=
          (((canonicalFiberPseudofunctor T.p).map fI.left.op.toLoc).toFunctor.map
            (eTarget.hom.hom I)).1
        let mJ :=
          (((canonicalFiberPseudofunctor T.p).map fJ.left.op.toLoc).toFunctor.map
            (eTarget.hom.hom J)).1
        let tHom := ((ΦT.obj y).hom Z.hom fI.left fJ.left hfI hfJ).1
        have hTargetSquare :
            mI ≫ eFI.hom.1 ≫ fD ≫ eFJ.inv.1 = tHom ≫ mJ := by
          -- The target descent isomorphism square, unfolded only to the comparison-conjugated
          -- normal form for the image descent datum `Ψ.obj D`.
          have hcomm' := congrArg (fun k ↦ k.1)
            (eTarget.hom.comm Z.hom fI.left fJ.left hfI hfJ)
          simpa only [d, fD, mI, mJ, tHom, Ψ,
            cover_descent_data_functor_hom_of_stack_morphism, Category.assoc] using hcomm'
        have hΦ : tHom = bIinv ≫ bJ := by
          -- The canonical target descent overlap is exactly the composite of the two comparison
          -- isomorphism components at `y`.
          rfl
        have hcancelI : bI ≫ bIinv = 𝟙 _ := by
          -- Cancel the left pseudofunctor-composition comparison after evaluating at `y`.
          simpa only [bI, bIinv, Category.assoc] using
            congrArg (fun k ↦ (k.toNatTrans.app y).1) cI.hom_inv_id
        have hcancelJ : eFJ.inv.1 ≫ eFJ.hom.1 = 𝟙 _ := by
          -- Cancel the inserted right pullback-comparison pair in the total category.
          exact congrArg (fun k ↦ k.1) eFJ.inv_hom_id
        change (a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD =
          a ≫ bJ ≫ mJ ≫ eFJ.hom.1
        have hinsertJ :
            (a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD =
              ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD ≫ eFJ.inv.1) ≫
                eFJ.hom.1 := by
          -- Insert `eFJ.inv ≫ eFJ.hom` so the transported overlap square can be applied.
          symm
          calc
            ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD ≫ eFJ.inv.1) ≫
                eFJ.hom.1 =
              ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD) ≫
                (eFJ.inv.1 ≫ eFJ.hom.1) := by
                simp only [Category.assoc]
            _ = ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD) ≫ 𝟙 _ := by
                exact congrArg
                  (fun k ↦ ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD) ≫ k)
                  hcancelJ
            _ = (a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD := by
                rw [Category.comp_id]
        have hcancelPrefix :
            (a ≫ bI ≫ ((bIinv ≫ bJ) ≫ mJ)) ≫ eFJ.hom.1 =
              a ≫ bJ ≫ mJ ≫ eFJ.hom.1 := by
          -- After the target overlap is expanded, cancel the left comparison pair and reassociate.
          calc
            (a ≫ bI ≫ ((bIinv ≫ bJ) ≫ mJ)) ≫ eFJ.hom.1 =
                a ≫ (bI ≫ bIinv) ≫ bJ ≫ mJ ≫ eFJ.hom.1 := by
                simp only [Category.assoc]
            _ = a ≫ 𝟙 _ ≫ bJ ≫ mJ ≫ eFJ.hom.1 := by
                exact congrArg (fun k ↦ a ≫ k ≫ bJ ≫ mJ ≫ eFJ.hom.1) hcancelI
            _ = a ≫ bJ ≫ mJ ≫ eFJ.hom.1 := by
                simp only [Category.id_comp]
        exact
          calc
            (a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD =
                ((a ≫ bI ≫ mI ≫ eFI.hom.1) ≫ fD ≫ eFJ.inv.1) ≫
                  eFJ.hom.1 := by
                exact hinsertJ
            _ = (a ≫ bI ≫ (mI ≫ eFI.hom.1 ≫ fD ≫ eFJ.inv.1)) ≫
                  eFJ.hom.1 := by
                simp only [Category.assoc]
            _ = (a ≫ bI ≫ (tHom ≫ mJ)) ≫ eFJ.hom.1 := by
                exact congrArg (fun k ↦ (a ≫ bI ≫ k) ≫ eFJ.hom.1) hTargetSquare
            _ = (a ≫ bI ≫ ((bIinv ≫ bJ) ≫ mJ)) ≫ eFJ.hom.1 := by
                exact congrArg
                  (fun k ↦ (a ≫ bI ≫ (k ≫ mJ)) ≫ eFJ.hom.1) hΦ
            _ = a ≫ bJ ≫ mJ ≫ eFJ.hom.1 := by
                exact hcancelPrefix
      let eStructured : StructuredArrow.mk τI ≅ StructuredArrow.mk τJ :=
        StructuredArrow.isoMk eSource htriangle
      exact ⟨(sliceTwoFibreProductStructuredArrowEquivFiber
        (G := FibredInGroupoidsMor.toBasedFunctor G)
        (F := FibredInGroupoidsMor.toBasedFunctor F)
        (f := Z)).functor.mapIso eStructured⟩
    simpa [P, localClass, G, xI, xJ, τI, τJ] using hleft.trans (hlocal.trans hright.symm)
  have hsheafOfArrows :
      Presieve.IsSheafFor P
        (Presieve.ofArrows (fun I : S.Arrow ↦ Over.mk I.f) π) := by
    rw [Presieve.isSheafFor_iff_generate]
    simpa [P, G, π, GrothendieckTopology.localized_cover_descent_terminal_cover] using
      (Presheaf.IsSheaf.isSheafFor
        (hSheaf G)
        ((GrothendieckTopology.localized_cover_descent_terminal_cover (J := J) S).1)
        ((GrothendieckTopology.localized_cover_descent_terminal_cover (J := J) S).condition))
  have hbij :
      Function.Bijective (Presieve.Arrows.toCompatible P π) :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := P) (π := π)).mp hsheafOfArrows
  obtain ⟨globalClass, hglobalClass⟩ := hbij.2 ⟨localClass, hcompatible⟩
  let z : ((F.sliceTwoFibreProduct G).p).Fiber (Over.mk (𝟙 U)) :=
    Quotient.out globalClass
  have hz : Quotient.mk'' z = globalClass := by
    exact Quotient.out_eq globalClass
  let E :=
    sliceTwoFibreProductStructuredArrowEquivFiber
      (G := FibredInGroupoidsMor.toBasedFunctor G)
      (F := FibredInGroupoidsMor.toBasedFunctor F)
      (f := Over.mk (𝟙 U))
  let A := E.inverse.obj z
  let x : X.p.Fiber U := A.right
  let τ :
      (fiberFunctor G U).obj (idSliceFiberObj U) ⟶
        (fiberFunctor F U).obj x := A.hom
  let eTerminal := fiberObjectSliceMorphism_terminalEvaluationIso T y
  let γ : y ⟶ (fiberFunctor F U).obj x := eTerminal.inv ≫ τ
  have hglobalRep :
      (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct G).p).Fiber (Over.mk (𝟙 U))))
          (sliceLocalObject F y (Over.mk (𝟙 U)) x τ)) =
        (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct G).p).Fiber (Over.mk (𝟙 U))))
          z) := by
    rw [Quotient.eq'']
    have hA : StructuredArrow.mk A.hom = A := by
      cases A
      rfl
    refine ⟨?_⟩
    simpa [sliceLocalObject, G, E, A, x, τ, hA] using (E.counitIso.app z)
  have hlocalClassEq :
      ∀ I : S.Arrow,
        (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct G).p).Fiber (Over.mk I.f)))
          (sliceLocalObject F y (Over.mk I.f)
            ((ΦX.obj x).obj I)
            ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫
              (ΦT.map γ).hom I ≫ (FibredCategoryMor.pullbackComparison H I.f x).hom))) =
        localClass I := by
    intro I
    have hpoint :
        P.map (π I).op globalClass = localClass I := by
      exact congrFun (congrArg Subtype.val hglobalClass) I
    have hrestrict :=
      sliceLocalClass_terminal_restrict_eq F S y x τ I
    have hleft :
        P.map (π I).op
            (Quotient.mk''
              (sliceLocalObject F y (Over.mk (𝟙 U)) x τ)) =
          localClass I := by
      calc
        P.map (π I).op
            (Quotient.mk''
              (sliceLocalObject F y (Over.mk (𝟙 U)) x τ)) =
          P.map (π I).op (Quotient.mk'' z) := by
            exact congrArg (fun s ↦ P.map (π I).op s) hglobalRep
        _ = P.map (π I).op globalClass := by
            exact congrArg (fun s ↦ P.map (π I).op s) hz
        _ = localClass I := hpoint
    simpa only [P, G, ΦX, ΦT, H, π, localClass] using hrestrict.symm.trans hleft
  let localIso : (I : S.Arrow) → ((ΦX.obj x).obj I) ≅ D.obj I := fun I ↦
    Classical.choose
      (exists_source_iso_of_sliceLocalClass_eq F y (Over.mk I.f)
        ((ΦX.obj x).obj I) (D.obj I)
        ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫
          (ΦT.map γ).hom I ≫ (FibredCategoryMor.pullbackComparison H I.f x).hom)
        ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫ eTarget.hom.hom I)
        (hlocalClassEq I))
  have hlocalIso :
      ∀ I : S.Arrow,
        ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫
            (ΦT.map γ).hom I ≫ (FibredCategoryMor.pullbackComparison H I.f x).hom) ≫
          (fiberFunctor F I.Y).map (localIso I).hom =
        (fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫ eTarget.hom.hom I := by
    intro I
    exact
      Classical.choose_spec
        (exists_source_iso_of_sliceLocalClass_eq F y (Over.mk I.f)
          ((ΦX.obj x).obj I) (D.obj I)
          ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫
            (ΦT.map γ).hom I ≫ (FibredCategoryMor.pullbackComparison H I.f x).hom)
          ((fiberObjectSliceMorphism_coverEvaluationIso T S y I).hom ≫ eTarget.hom.hom I)
          (hlocalClassEq I))
  refine ⟨x, ⟨?_⟩⟩
  refine Pseudofunctor.DescentData.isoMk localIso ?_
  intro V q I J fI fJ hfI hfJ
  letI : (fiberFunctor F V).Faithful :=
    (faithful_iff_fiberwise (F := F)).1 hFaithful V
  apply (fiberFunctor F V).map_injective
  let HT := canonicalFiberPseudofunctor T.p
  let HX := canonicalFiberPseudofunctor X.p
  let FV := fiberFunctor F V
  let hti := (HT.map fI.op.toLoc).toFunctor
  let htj := (HT.map fJ.op.toLoc).toFunctor
  let φI := (HX.map fI.op.toLoc).toFunctor.map (localIso I).hom
  let φJ := (HX.map fJ.op.toLoc).toFunctor.map (localIso J).hom
  let eXI := FibredCategoryMor.pullbackComparison H fI ((ΦX.obj x).obj I)
  let eXJ := FibredCategoryMor.pullbackComparison H fJ ((ΦX.obj x).obj J)
  let eDI := FibredCategoryMor.pullbackComparison H fI (D.obj I)
  let eDJ := FibredCategoryMor.pullbackComparison H fJ (D.obj J)
  let exCoverI := FibredCategoryMor.pullbackComparison H I.f x
  let exCoverJ := FibredCategoryMor.pullbackComparison H J.f x
  let γI := (ΦT.map γ).hom I
  let γJ := (ΦT.map γ).hom J
  let targetI := eTarget.hom.hom I
  let targetJ := eTarget.hom.hom J
  have hcompI :
      γI ≫ exCoverI.hom ≫ (fiberFunctor F I.Y).map (localIso I).hom = targetI := by
    -- Cancel the cover-evaluation isomorphism from the chosen local slice isomorphism over `I`.
    apply (Iso.cancel_iso_hom_left (fiberObjectSliceMorphism_coverEvaluationIso T S y I) _ _).1
    simpa only [γI, exCoverI, targetI, Category.assoc] using hlocalIso I
  have hcompJ :
      γJ ≫ exCoverJ.hom ≫ (fiberFunctor F J.Y).map (localIso J).hom = targetJ := by
    -- The same cancellation over `J` gives the right component normal form.
    apply (Iso.cancel_iso_hom_left (fiberObjectSliceMorphism_coverEvaluationIso T S y J) _ _).1
    simpa only [γJ, exCoverJ, targetJ, Category.assoc] using hlocalIso J
  have hcompI_map :
      hti.map γI ≫ hti.map exCoverI.hom ≫
          hti.map ((fiberFunctor F I.Y).map (localIso I).hom) =
        hti.map targetI := by
    -- Pull the component normal form over `I` down to the common refinement `V`.
    calc
      hti.map γI ≫ hti.map exCoverI.hom ≫
          hti.map ((fiberFunctor F I.Y).map (localIso I).hom) =
        hti.map (γI ≫ exCoverI.hom ≫ (fiberFunctor F I.Y).map (localIso I).hom) := by
          rw [← hti.map_comp, ← hti.map_comp]
      _ = hti.map targetI := by
          exact congrArg hti.map hcompI
  have hcompJ_map :
      htj.map γJ ≫ htj.map exCoverJ.hom ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
        htj.map targetJ := by
    -- Pull the right component normal form to the same common refinement.
    calc
      htj.map γJ ≫ htj.map exCoverJ.hom ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
        htj.map (γJ ≫ exCoverJ.hom ≫ (fiberFunctor F J.Y).map (localIso J).hom) := by
          rw [← htj.map_comp, ← htj.map_comp]
      _ = htj.map targetJ := by
          exact congrArg htj.map hcompJ
  have hnatI :
      hti.map ((fiberFunctor F I.Y).map (localIso I).hom) ≫ eDI.hom =
        eXI.hom ≫ FV.map φI := by
    -- Naturality of the pullback comparison moves the mapped local isomorphism past the
    -- comparison shell on the left cover leg.
    simpa only [HT, HX, FV, hti, φI, eXI, eDI, H] using
      FibredCategoryMor.pullbackComparison_naturality_over_vertical H fI (localIso I).hom
  have hnatJ :
      htj.map ((fiberFunctor F J.Y).map (localIso J).hom) ≫ eDJ.hom =
        eXJ.hom ≫ FV.map φJ := by
    -- Naturality supplies the corresponding right-leg comparison square.
    simpa only [HT, HX, FV, htj, φJ, eXJ, eDJ, H] using
      FibredCategoryMor.pullbackComparison_naturality_over_vertical H fJ (localIso J).hom
  let dD := D.hom q fI fJ hfI hfJ
  let dX := (ΦX.obj x).hom q fI fJ hfI hfJ
  change FV.map (φI ≫ dD) = FV.map (dX ≫ φJ)
  rw [FV.map_comp, FV.map_comp]
  let pre := hti.map γI ≫ hti.map exCoverI.hom ≫ eXI.hom
  have hnatJ_inv :
      FV.map φJ ≫ eDJ.inv =
        eXJ.inv ≫ htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
    -- Move the right comparison shell across the mapped local isomorphism in inverse form.
    simpa only [HT, HX, FV, htj, φJ, eXJ, eDJ, H] using
      FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical H fJ (localIso J).hom
  have hDtransport :
      ((cover_descent_data_functor_of_stack_morphism H S).obj D).hom
          (i₁ := I) (i₂ := J) q fI fJ hfI hfJ =
        (FibredCategoryMor.pullbackComparison H fI (D.obj I)).hom ≫
          (FibredCategoryMor.fiberFunctor H V).map (D.hom q fI fJ hfI hfJ) ≫
            (FibredCategoryMor.pullbackComparison H fJ (D.obj J)).inv := by
    -- The stack-morphism descent functor transports source overlaps by conjugating with the
    -- pullback-comparison isomorphisms.
    exact
      coverDescentDataFunctor_hom_eq_pullbackComparison
        (H := H) (S := S) (D := D) (q := q)
        (f₁ := fI) (f₂ := fJ) (hf₁ := hfI) (hf₂ := hfJ)
  have hXtransport :
      ((cover_descent_data_functor_of_stack_morphism H S).obj (ΦX.obj x)).hom
          (i₁ := I) (i₂ := J) q fI fJ hfI hfJ =
        (FibredCategoryMor.pullbackComparison H fI ((ΦX.obj x).obj I)).hom ≫
          (FibredCategoryMor.fiberFunctor H V).map ((ΦX.obj x).hom q fI fJ hfI hfJ) ≫
            (FibredCategoryMor.pullbackComparison H fJ ((ΦX.obj x).obj J)).inv := by
    -- The same transported-overlap normal form applies to the canonical source descent datum.
    exact
      coverDescentDataFunctor_hom_eq_pullbackComparison
        (H := H) (S := S) (D := ΦX.obj x) (q := q)
        (f₁ := fI) (f₂ := fJ) (hf₁ := hfI) (hf₂ := hfJ)
  have hcanonicalTarget :
      hti.map exCoverI.hom ≫
          ((cover_descent_data_functor_of_stack_morphism H S).obj
            (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ =
        ((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ) ≫
          htj.map exCoverJ.hom := by
    -- The canonical descent datum of the global source object is identified with the transported
    -- target descent datum through the comparison components.
    exact
      cover_descent_data_functor_of_stack_morphism_component_comm
        (H := H) S x (q := q)
        (I₁ := I) (I₂ := J) (f₁ := fI) (f₂ := fJ) (hf₁ := hfI) (hf₂ := hfJ)
  have hgammaComm :
      hti.map γI ≫ ((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ) =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map γJ := by
    -- Naturality of the descended target morphism `γ` supplies the middle target square.
    simpa only [ΦT, HT, hti, htj, γI, γJ] using
      (ΦT.map γ).comm q fI fJ hfI hfJ
  have htargetComm :
      hti.map targetI ≫
          ((cover_descent_data_functor_of_stack_morphism H S).obj D).hom
            (i₁ := I) (i₂ := J) q fI fJ hfI hfJ =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map targetJ := by
    -- The target isomorphism `eTarget` compares the glued target object with the transported
    -- source descent datum.
    simpa only [ΦT, Ψ, HT, hti, htj, targetI, targetJ] using
      eTarget.hom.comm q fI fJ hfI hfJ
  have hrightTail :
      ((((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map γJ) ≫
          htj.map exCoverJ.hom) ≫
            htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map targetJ := by
    -- Reassemble the normalized right target path using the component equality over `J`.
    rw [← hcompJ_map]
    simp only [Category.assoc]
    rfl
  have hrightFinal :
      ((hti.map γI ≫
          ((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ)) ≫
        htj.map exCoverJ.hom) ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map targetJ := by
    -- Combine naturality of `γ` with the already reassembled right component path.
    exact
      (congrArg
        (fun k ↦ (k ≫ htj.map exCoverJ.hom) ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom))
        hgammaComm).trans hrightTail
  have hrightFromCanonicalSource :
      (((hti.map γI ≫ hti.map exCoverI.hom) ≫
          ((cover_descent_data_functor_of_stack_morphism H S).obj
            (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom)) =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map targetJ := by
    -- Consume the canonical target comparison from the left-associated normal form.
    have hassocStart :
        (((hti.map γI ≫ hti.map exCoverI.hom) ≫
            ((cover_descent_data_functor_of_stack_morphism H S).obj
              (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
            htj.map ((fiberFunctor F J.Y).map (localIso J).hom)) =
          hti.map γI ≫ hti.map exCoverI.hom ≫
            ((cover_descent_data_functor_of_stack_morphism H S).obj
              (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
      simp only [Category.assoc]
    have hassoc₀ :
        hti.map γI ≫ hti.map exCoverI.hom ≫
            ((cover_descent_data_functor_of_stack_morphism H S).obj
              (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
          hti.map γI ≫
            (hti.map exCoverI.hom ≫
              ((cover_descent_data_functor_of_stack_morphism H S).obj
                (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
                htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
      simp only [Category.assoc]
    have hcan :
        hti.map γI ≫
            (hti.map exCoverI.hom ≫
              ((cover_descent_data_functor_of_stack_morphism H S).obj
                (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
          hti.map γI ≫
            (((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ) ≫
              htj.map exCoverJ.hom) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
      exact congrArg
        (fun k ↦ hti.map γI ≫ k ≫
          htj.map ((fiberFunctor F J.Y).map (localIso J).hom))
        hcanonicalTarget
    have hassoc₁ :
        hti.map γI ≫
            (((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ) ≫
              htj.map exCoverJ.hom) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) =
          ((hti.map γI ≫
              ((ΦT.obj ((fiberFunctor F U).obj x)).hom q fI fJ hfI hfJ)) ≫
            htj.map exCoverJ.hom) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
      simp only [Category.assoc]
    exact hassocStart.trans (hassoc₀.trans (hcan.trans (hassoc₁.trans hrightFinal)))
  have hleftNormalized :
      pre ≫ FV.map φI ≫ FV.map dD ≫ eDJ.inv =
        hti.map targetI ≫
          ((cover_descent_data_functor_of_stack_morphism H S).obj D).hom
            (i₁ := I) (i₂ := J) q fI fJ hfI hfJ := by
    -- Normalize the left side to the target overlap of `eTarget`.
    calc
      pre ≫ FV.map φI ≫ FV.map dD ≫ eDJ.inv =
          hti.map γI ≫ hti.map exCoverI.hom ≫
            (eXI.hom ≫ FV.map φI) ≫ FV.map dD ≫ eDJ.inv := by
            simp only [pre, Category.assoc]
      _ =
          hti.map γI ≫ hti.map exCoverI.hom ≫
            (hti.map ((fiberFunctor F I.Y).map (localIso I).hom) ≫ eDI.hom) ≫
              FV.map dD ≫ eDJ.inv := by
            exact congrArg
              (fun k ↦ hti.map γI ≫ hti.map exCoverI.hom ≫ k ≫ FV.map dD ≫ eDJ.inv)
              hnatI.symm
      _ =
          (hti.map γI ≫ hti.map exCoverI.hom ≫
              hti.map ((fiberFunctor F I.Y).map (localIso I).hom)) ≫
            eDI.hom ≫ FV.map dD ≫ eDJ.inv := by
            simp only [Category.assoc]
      _ = hti.map targetI ≫ eDI.hom ≫ FV.map dD ≫ eDJ.inv := by
            exact congrArg (fun k ↦ k ≫ eDI.hom ≫ FV.map dD ≫ eDJ.inv) hcompI_map
      _ =
          hti.map targetI ≫
            ((cover_descent_data_functor_of_stack_morphism H S).obj D).hom
              (i₁ := I) (i₂ := J) q fI fJ hfI hfJ := by
            exact congrArg (fun k ↦ hti.map targetI ≫ k) hDtransport.symm
  have hrightNormalized :
      pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv =
        ((ΦT.obj y).hom q fI fJ hfI hfJ) ≫ htj.map targetJ := by
    -- Normalize the right side through the canonical target descent datum and then use the
    -- component normal form over `J`.
    have hrightAlmost :
        pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv =
          (((hti.map γI ≫ hti.map exCoverI.hom) ≫
            ((cover_descent_data_functor_of_stack_morphism H S).obj
              (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
            htj.map ((fiberFunctor F J.Y).map (localIso J).hom)) := by
      calc
        pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv =
            hti.map γI ≫ hti.map exCoverI.hom ≫ eXI.hom ≫ FV.map dX ≫
              (FV.map φJ ≫ eDJ.inv) := by
              simp only [pre, Category.assoc]
        _ =
            hti.map γI ≫ hti.map exCoverI.hom ≫ eXI.hom ≫ FV.map dX ≫
              (eXJ.inv ≫ htj.map ((fiberFunctor F J.Y).map (localIso J).hom)) := by
              exact congrArg
                (fun k ↦
                  hti.map γI ≫ hti.map exCoverI.hom ≫ eXI.hom ≫ FV.map dX ≫ k)
                hnatJ_inv
        _ =
            hti.map γI ≫ hti.map exCoverI.hom ≫
              (eXI.hom ≫ FV.map dX ≫ eXJ.inv) ≫
                htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
              simp only [Category.assoc]
        _ =
            ((hti.map γI ≫ hti.map exCoverI.hom) ≫
              (eXI.hom ≫ FV.map dX ≫ eXJ.inv)) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom) := by
              simp only [Category.assoc]
        _ =
            (((hti.map γI ≫ hti.map exCoverI.hom) ≫
              ((cover_descent_data_functor_of_stack_morphism H S).obj
                (ΦX.obj x)).hom (i₁ := I) (i₂ := J) q fI fJ hfI hfJ) ≫
              htj.map ((fiberFunctor F J.Y).map (localIso J).hom)) := by
              exact congrArg
                (fun k ↦
                  ((hti.map γI ≫ hti.map exCoverI.hom) ≫ k) ≫
                    htj.map ((fiberFunctor F J.Y).map (localIso J).hom))
                hXtransport.symm
    exact hrightAlmost.trans hrightFromCanonicalSource
  have hprepostTail :
      hti.map targetI ≫
          ((cover_descent_data_functor_of_stack_morphism H S).obj D).hom
            (i₁ := I) (i₂ := J) q fI fJ hfI hfJ =
        pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv := by
    -- The target overlap square and the right normalization finish the pre/post comparison.
    exact htargetComm.trans hrightNormalized.symm
  have hprepost :
      pre ≫ FV.map φI ≫ FV.map dD ≫ eDJ.inv =
        pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv := by
    -- After the left and right normalizations, the remaining square is exactly `eTarget.hom.comm`.
    exact hleftNormalized.trans hprepostTail
  have hprefixIso : IsIso pre := by
    -- The precomposition morphism is a composite of fiber isomorphisms.
    have hγIIso : IsIso γI :=
      IsFibredInGroupoids.hom_isIso (p := T.p) I.Y γI
    letI : IsIso γI := hγIIso
    dsimp only [pre]
    infer_instance
  letI : IsIso pre := hprefixIso
  apply (cancel_mono eDJ.inv).1
  apply (cancel_epi pre).1
  calc
    pre ≫ (FV.map φI ≫ FV.map dD) ≫ eDJ.inv =
        pre ≫ FV.map φI ≫ FV.map dD ≫ eDJ.inv := by
        simp only [Category.assoc]
    _ = pre ≫ FV.map dX ≫ FV.map φJ ≫ eDJ.inv := hprepost
    _ = pre ≫ (FV.map dX ≫ FV.map φJ) ≫ eDJ.inv := by
        simp only [Category.assoc]

/- Domain-style sampling for Lemma 8.6.11:
- primary domain: stacks in groupoids over a site and the slice-pair presheaf attached to a
  morphism of categories fibred in groupoids;
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsStackInSetoids`,
  `FibredInGroupoidsMor.faithful_iff_fiberwise`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `isStackInSetoids_iff_isoClassPresheaf_isSheaf`;
- best owner abstraction: the source-facing conclusion remains the owner predicate
  `IsStackInGroupoids J X.p`, while the faithfulness hypothesis should use the canonical owner
  predicate `F.toBasedFunctor.Faithful` rather than duplicating its fiberwise reformulation; the
  slice hypothesis should be stated directly for the canonical slice base change
  `F.sliceTwoFibreProduct G`, with the owner-level stack-in-setoids reformulation on its
  projection kept as derived API;
- primitive data: the morphism `F : X ⟶ T` and the sheaf condition on the canonical
  iso-class presheaf of the canonical slice base change for each slice morphism `G : C/U ⟶ T`;
- derived API: the companion owner-level hypothesis
  `IsStackInSetoids (J.over U) (F.sliceTwoFibreProduct G).p` via Lemma `8.6.3`, and the
  resulting stack-in-groupoids structure on `X`, whose groupoid part is already ambient because
  `X : FibredInGroupoidsOver C`.

Source/core/bridge triage:
- `source-facing`: Lemma 8.6.11 itself;
- `core/canonical`: `IsStackInGroupoids J X.p`, `F.toBasedFunctor.Faithful`, and
  `IsStackInSetoids (J.over U) ((F.sliceTwoFibreProduct G).p)`;
- `bridge/view`: the textbook fibrewise-faithful hypothesis, recovered from
  `FibredInGroupoidsMor.faithful_iff_fiberwise`, together with the sheaf reformulation on
  `fiberIsoClassPresheaf ((F.sliceTwoFibreProduct G).p)` supplied by Lemma `8.6.3`. -/

-- Proof sketch: for each object `U`, use the faithful morphism `F : X ⟶ T` and the sheaf
-- condition on the canonical slice iso-class presheaf of `F.sliceTwoFibreProduct G` to show that
-- descent data in `X` is effective and morphisms descend uniquely after applying `F`. The stack
-- condition for `T` supplies the compatible target-side object and comparison isomorphisms, which
-- the sheaf hypothesis lifts back to `X`, yielding the stack condition on `X`.
/-- Chap08 Lemma 8 6 11: let `F : X ⟶ T` be a morphism of categories fibred in groupoids over the
site `(C, J)`. Assume that `T` is a stack in groupoids, that the underlying based functor
`F.toBasedFunctor` is faithful (equivalently, faithful on every fiber by Lemma `4.35.9`), and
that for every `U : C` and every slice morphism `G : C/U ⟶ T`, the canonical iso-class presheaf
of the slice base change `F.sliceTwoFibreProduct G` is a sheaf. Via Yoneda on `T_U`, this is the
source presheaf of isomorphism classes of pairs `(x, F(x) ≅ f^* y)`. Then `X` is a stack in
groupoids over `(C, J)`. -/
@[stacks 0CKJ]
theorem isStackInGroupoids_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isSheaf
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hSheaf :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ T),
        Presheaf.IsSheaf (J.over U) ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf)) :
    IsStackInGroupoids J X.p := by
  -- Use the coverwise criterion; faithfulness is already reflected from `T`, while fullness and
  -- effectivity are isolated in the two slice iso-class sheaf helpers above.
  have hCover :
      ∀ (U : C) (S : J.Cover U),
        ((canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
    intro U S
    let ΦX := (canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)
    have hFaithfulCover : ΦX.Faithful :=
      canonicalDescentFunctor_faithful_of_targetStack_and_faithful F hFaithful S
    have hFullCover : ΦX.Full :=
      canonicalDescentFunctor_full_of_sliceIsoClassSheaves
        F hFaithful hSheaf S
    have hEssCover : ΦX.EssSurj :=
      canonicalDescentFunctor_essSurj_of_sliceIsoClassSheaves
        F hFaithful hSheaf S
    -- The three fixed-cover properties assemble into equivalence of the canonical descent
    -- functor, which is the coverwise stack criterion for `X.p`.
    exact { faithful := hFaithfulCover, full := hFullCover, essSurj := hEssCover }
  have hStackOnSite : IsStackOnSite J X.p := by
    -- Apply the standard coverwise criterion after the fixed-cover equivalence is assembled.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
        (J := J) (p := X.p)).2 hCover
  -- Package the site-level stack condition with the ambient fibred-in-groupoids structure of `X`.
  exact
    { toIsStackOnSite := hStackOnSite
      toIsFibredInGroupoids := inferInstance }

/-- Companion owner-level reformulation: it is enough to assume that each canonical slice base
change is a stack in setoids over the slice site. The source-facing sheaf hypothesis of Lemma
`8.6.11` is then recovered from Lemma `8.6.3`. -/
theorem isStackInGroupoids_of_faithful_and_sliceTwoFibreProduct_isStackInSetoids
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hStack :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ T),
        IsStackInSetoids (J.over U) ((F.sliceTwoFibreProduct G).p)) :
    IsStackInGroupoids J X.p := by
  refine isStackInGroupoids_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isSheaf
    F hFaithful ?_
  intro U G
  exact
    (isStackInSetoids_iff_isoClassPresheaf_isSheaf (J.over U) (F.sliceTwoFibreProduct G).p).1
      (hStack G)

end FibredInGroupoidsMor

end

end CategoryTheory
