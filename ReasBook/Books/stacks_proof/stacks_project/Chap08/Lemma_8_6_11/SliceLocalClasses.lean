import StacksProject_2024.Chap08.Lemma_8_6_11.FaithfulSliceSetoids
import StacksProject_2024.Chap08.Lemma_8_6_11.SliceYonedaEvaluation

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FibredInGroupoidsOver C}
variable [IsStackInGroupoids J T.p]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

/-- Helper for Chap08 Lemma 8 6 11: package a source fiber object together with a target arrow
as the corresponding local object of the canonical slice two-fibre product. -/
noncomputable def sliceLocalObject
    (F : FibredInGroupoidsMor X T)
    {U : C} (y : T.p.Fiber U) (V : Over U)
    (x : X.p.Fiber V.left)
    (τ :
      (fiberFunctor (fiberObjectSliceMorphism T y) V.left).obj
          (⟨V, rfl⟩ : (Over.forget U).Fiber V.left) ⟶
        (fiberFunctor F V.left).obj x) :
    ((F.sliceTwoFibreProduct (fiberObjectSliceMorphism T y)).p).Fiber V :=
  (sliceTwoFibreProductStructuredArrowEquivFiber
    (G := FibredInGroupoidsMor.toBasedFunctor (fiberObjectSliceMorphism T y))
    (F := FibredInGroupoidsMor.toBasedFunctor F)
    (f := V)).functor.obj (StructuredArrow.mk τ)

/-- Helper for Chap08 Lemma 8 6 11: a one-arrow restriction of a local slice representative is
identified by an explicit source pullback isomorphism and the corresponding target square. -/
theorem sliceLocalClass_restrict_eq_of_sourceTargetSquare
    (F : FibredInGroupoidsMor X T)
    {U : C} (y : T.p.Fiber U) {W V : Over U} (a : W ⟶ V)
    (xV : X.p.Fiber V.left)
    (τV :
      (fiberFunctor (fiberObjectSliceMorphism T y) V.left).obj
          (⟨V, rfl⟩ : (Over.forget U).Fiber V.left) ⟶
        (fiberFunctor F V.left).obj xV)
    (xW : X.p.Fiber W.left)
    (τW :
      (fiberFunctor (fiberObjectSliceMorphism T y) W.left).obj
          (⟨W, rfl⟩ : (Over.forget U).Fiber W.left) ⟶
        (fiberFunctor F W.left).obj xW)
    (b : xW.1 ⟶ xV.1)
    (hb : X.p.IsHomLift a.left b)
    (hτ :
      (toBasedFunctor (fiberObjectSliceMorphism T y)).toFunctor.map a ≫ τV.1 =
        τW.1 ≫ (toBasedFunctor F).toFunctor.map b) :
    (((F.sliceTwoFibreProduct (fiberObjectSliceMorphism T y)).p).fiberIsoClassPresheaf).map a.op
        (Quotient.mk'' (sliceLocalObject F y V xV τV)) =
      Quotient.mk'' (sliceLocalObject F y W xW τW) := by
  -- Build the actual total morphism in the slice two-fibre product and use the general
  -- iso-class restriction formula for morphisms in a fibred groupoid.
  let G := fiberObjectSliceMorphism T y
  let p := (F.sliceTwoFibreProduct G).p
  let φ : (sliceLocalObject F y W xW τW).1 ⟶ (sliceLocalObject F y V xV τV).1 := by
    refine
      { base := a.left
        a := a
        a_over := ?_
        b := b
        b_over := hb
        comm := ?_ }
    · exact (show (Over.forget U).IsHomLift a.left a from
        (sliceHom_isStronglyCartesian a).toIsHomLift)
    · refine ⟨?_⟩
      exact hτ
  have hbase : p.map φ = a := by
    rfl
  have hclass :=
    fiberIsoClassPresheaf_map_mk_eq_of_hom (p := p) φ
  -- The constructed morphism has base `a`, so the owner-level formula is exactly the requested
  -- restriction equality.
  simpa [p, hbase] using hclass

/-- Helper for Chap08 Lemma 8 6 11: equality of the two global slice-pair classes recovers the
underlying source morphism whose target image is the prescribed target morphism. -/
theorem exists_source_hom_of_sliceLocalClass_eq
    (F : FibredInGroupoidsMor X T)
    {U : C} {x y : X.p.Fiber U}
    (β : (fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj y)
    (hEq :
      (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct
              (fiberObjectSliceMorphism T ((fiberFunctor F U).obj y))).p).Fiber
              (Over.mk (𝟙 U))))
          (sliceLocalObject F ((fiberFunctor F U).obj y) (Over.mk (𝟙 U)) x
            ((fiberObjectSliceMorphism_terminalEvaluationIso T ((fiberFunctor F U).obj y)).hom ≫
              inv β))) =
        (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct
              (fiberObjectSliceMorphism T ((fiberFunctor F U).obj y))).p).Fiber
              (Over.mk (𝟙 U))))
          (sliceLocalObject F ((fiberFunctor F U).obj y) (Over.mk (𝟙 U)) y
            (fiberObjectSliceMorphism_terminalEvaluationIso T ((fiberFunctor F U).obj y)).hom))) :
    ∃ α : x ⟶ y, (fiberFunctor F U).map α = β := by
  -- Move the equality of iso-classes back across the structured-arrow model of the slice fiber.
  let G := fiberObjectSliceMorphism T ((fiberFunctor F U).obj y)
  let eTerminal :=
    fiberObjectSliceMorphism_terminalEvaluationIso T ((fiberFunctor F U).obj y)
  let E :=
    sliceTwoFibreProductStructuredArrowEquivFiber
      (G := FibredInGroupoidsMor.toBasedFunctor G)
      (F := FibredInGroupoidsMor.toBasedFunctor F)
      (f := Over.mk (𝟙 U))
  let A :
      StructuredArrow
        ((fiberFunctor G U).obj (⟨Over.mk (𝟙 U), rfl⟩ : (Over.forget U).Fiber U))
        (fiberFunctor F U) :=
    StructuredArrow.mk (eTerminal.hom ≫ inv β)
  let B :
      StructuredArrow
        ((fiberFunctor G U).obj (⟨Over.mk (𝟙 U), rfl⟩ : (Over.forget U).Fiber U))
        (fiberFunctor F U) :=
    StructuredArrow.mk eTerminal.hom
  have hIsoSlice :
      Nonempty (E.functor.obj A ≅ E.functor.obj B) := by
    exact Quotient.exact' hEq
  obtain ⟨eSlice⟩ := hIsoSlice
  let eStructured : A ≅ B :=
    (E.unitIso.app A) ≪≫ E.inverse.mapIso eSlice ≪≫ (E.unitIso.app B).symm
  refine ⟨eStructured.hom.right, ?_⟩
  have hw :
      (eTerminal.hom ≫ inv β) ≫ (fiberFunctor F U).map eStructured.hom.right =
        eTerminal.hom := by
    simpa [A, B] using eStructured.hom.w.symm
  have hmap : (fiberFunctor F U).map eStructured.hom.right = β := by
    have hw'' := congrArg (fun k ↦ eTerminal.inv ≫ k) hw
    have hpre :
        inv β ≫ (fiberFunctor F U).map eStructured.hom.right =
          𝟙 ((fiberFunctor F U).obj y) := by
      have hpre₁ :
          inv β ≫ (fiberFunctor F U).map eStructured.hom.right =
            eTerminal.inv ≫ eTerminal.hom := by
        simpa only [Category.assoc, eTerminal.inv_hom_id_assoc] using hw''
      exact hpre₁.trans eTerminal.inv_hom_id
    simpa using (inv_comp_eq_id β).1 hpre
  exact hmap

/-- Helper for Chap08 Lemma 8 6 11: equality of two slice-pair iso-classes over the same
slice object gives an isomorphism of the source objects compatible with the target arrows. -/
theorem exists_source_iso_of_sliceLocalClass_eq
    (F : FibredInGroupoidsMor X T)
    {U : C} (y : T.p.Fiber U) (V : Over U)
    (x₁ x₂ : X.p.Fiber V.left)
    (τ₁ :
      (fiberFunctor (fiberObjectSliceMorphism T y) V.left).obj
          (⟨V, rfl⟩ : (Over.forget U).Fiber V.left) ⟶
        (fiberFunctor F V.left).obj x₁)
    (τ₂ :
      (fiberFunctor (fiberObjectSliceMorphism T y) V.left).obj
          (⟨V, rfl⟩ : (Over.forget U).Fiber V.left) ⟶
        (fiberFunctor F V.left).obj x₂)
    (hEq :
      (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct (fiberObjectSliceMorphism T y)).p).Fiber V))
          (sliceLocalObject F y V x₁ τ₁)) =
        (@Quotient.mk'' _
          (isIsomorphicSetoid
            (((F.sliceTwoFibreProduct (fiberObjectSliceMorphism T y)).p).Fiber V))
          (sliceLocalObject F y V x₂ τ₂))) :
    ∃ e : x₁ ≅ x₂, τ₁ ≫ (fiberFunctor F V.left).map e.hom = τ₂ := by
  -- Move the equality back through the structured-arrow model of the slice fiber.
  let G := fiberObjectSliceMorphism T y
  let E :=
    sliceTwoFibreProductStructuredArrowEquivFiber
      (G := FibredInGroupoidsMor.toBasedFunctor G)
      (F := FibredInGroupoidsMor.toBasedFunctor F)
      (f := V)
  let A :
      StructuredArrow
        ((fiberFunctor G V.left).obj (⟨V, rfl⟩ : (Over.forget U).Fiber V.left))
        (fiberFunctor F V.left) :=
    StructuredArrow.mk τ₁
  let B :
      StructuredArrow
        ((fiberFunctor G V.left).obj (⟨V, rfl⟩ : (Over.forget U).Fiber V.left))
        (fiberFunctor F V.left) :=
    StructuredArrow.mk τ₂
  have hIsoSlice :
      Nonempty (E.functor.obj A ≅ E.functor.obj B) := by
    exact Quotient.exact' hEq
  obtain ⟨eSlice⟩ := hIsoSlice
  let eStructured : A ≅ B :=
    (E.unitIso.app A) ≪≫ E.inverse.mapIso eSlice ≪≫ (E.unitIso.app B).symm
  let eSource : x₁ ≅ x₂ :=
    (StructuredArrow.proj
      ((fiberFunctor G V.left).obj (⟨V, rfl⟩ : (Over.forget U).Fiber V.left))
      (fiberFunctor F V.left)).mapIso eStructured
  refine ⟨eSource, ?_⟩
  -- The structured-arrow triangle is exactly the target compatibility of the source isomorphism.
  simpa [A, B, eSource] using eStructured.hom.w.symm

omit [IsStackInGroupoids J T.p] in
/-- Helper for Chap08 Lemma 8 6 11: restricting a terminal slice pair along a cover arrow gives
the expected pair formed from the canonical pullback of the source object. -/
theorem sliceLocalClass_terminal_restrict_eq
    (F : FibredInGroupoidsMor X T)
    {U : C} (S : J.Cover U) (y : T.p.Fiber U)
    (x : X.p.Fiber U)
    (τ :
      (fiberFunctor (fiberObjectSliceMorphism T y) U).obj (idSliceFiberObj U) ⟶
        (fiberFunctor F U).obj x)
    (I : S.Arrow) :
    let G := fiberObjectSliceMorphism T y
    let P := ((F.sliceTwoFibreProduct G).p).fiberIsoClassPresheaf
    let π : Over.mk I.f ⟶ Over.mk (𝟙 U) := Over.homMk I.f
    let eTerminal := fiberObjectSliceMorphism_terminalEvaluationIso T y
    let γ : y ⟶ (fiberFunctor F U).obj x := eTerminal.inv ≫ τ
    let ex := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f x
    let eCover := fiberObjectSliceMorphism_coverEvaluationIso T S y I
    P.map π.op
        (Quotient.mk''
          (sliceLocalObject F y (Over.mk (𝟙 U)) x τ)) =
      Quotient.mk''
        (sliceLocalObject F y (Over.mk I.f)
          ((((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x).obj I)
          (eCover.hom ≫
            (((canonicalFiberPseudofunctor T.p).toDescentData
              (fun I : S.Arrow ↦ I.f)).map γ).hom I ≫ ex.hom)) := by
  -- The restriction square is the same pullback-comparison calculation used for local slice
  -- classes: restrict the terminal target arrow and then compare the `F`-pullback.
  dsimp only
  let G := fiberObjectSliceMorphism T y
  let ΦT := (canonicalFiberPseudofunctor T.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let eTerminal := fiberObjectSliceMorphism_terminalEvaluationIso T y
  let γ : y ⟶ (fiberFunctor F U).obj x := eTerminal.inv ≫ τ
  let ex := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f x
  let eCover := fiberObjectSliceMorphism_coverEvaluationIso T S y I
  let τI := eCover.hom ≫ (ΦT.map γ).hom I ≫ ex.hom
  let πI : Over.mk I.f ⟶ Over.mk (𝟙 U) := Over.homMk I.f (by simp)
  have hb :
      X.p.IsHomLift (I.f) ((canonicalPullbackChoice X.p).map I.f x) := by
    simpa using ((canonicalPullbackChoice X.p).isStronglyCartesian I.f x).toIsHomLift
  have hrestrict := sliceLocalClass_restrict_eq_of_sourceTargetSquare
    (F := F) (y := y) (a := πI)
    (xV := x)
    (τV := τ)
    (xW := (((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x).obj I)
    (τW := τI)
    (b := (canonicalPullbackChoice X.p).map I.f x)
    (hb := hb)
    (hτ := by
      have hcover :=
        fiberObjectSliceMorphism_coverEvaluationIso_hom_postcompose
          (Y := T) (S := S) y I πI
      have hγpull :=
        canonical_pullbackFunctor_map_fac (p := T.p) (f := I.f) (φ := γ)
      have hexpost := FibredCategoryMor.pullbackComparison_hom_postcompose
        (toFibredCategoryMor F) I.f x
      have hcoverγ :
          (toBasedFunctor G).map πI ≫ τ.1 =
            eCover.hom.1 ≫
              ((canonicalPullbackChoice T.p).map I.f y ≫ γ.1) := by
        have hγeq : eTerminal.hom ≫ γ = τ := by
          simp [γ]
        calc
          (toBasedFunctor G).map πI ≫ τ.1 =
            (toBasedFunctor G).map πI ≫ (eTerminal.hom ≫ γ).1 := by
              exact congrArg (fun k ↦ (toBasedFunctor G).map πI ≫ k.1) hγeq.symm
          _ =
            ((toBasedFunctor G).map πI ≫ eTerminal.hom.1) ≫ γ.1 := by
              have hcomp : (eTerminal.hom ≫ γ).1 = eTerminal.hom.1 ≫ γ.1 := rfl
              rw [hcomp]
              exact (Category.assoc _ _ _).symm
          _ =
            (eCover.hom.1 ≫ (canonicalPullbackChoice T.p).map I.f y) ≫ γ.1 := by
              exact congrArg (fun k ↦ k ≫ γ.1) hcover
          _ =
            eCover.hom.1 ≫ ((canonicalPullbackChoice T.p).map I.f y ≫ γ.1) := by
              exact Category.assoc _ _ _
      have hγstep :
          eCover.hom.1 ≫
              ((canonicalPullbackChoice T.p).map I.f y ≫ γ.1) =
            eCover.hom.1 ≫
              (((ΦT.map γ).hom I).1 ≫
                (canonicalPullbackChoice T.p).map I.f ((fiberFunctor F U).obj x)) := by
        simpa only [Category.assoc, ΦT] using
          congrArg (fun k ↦ eCover.hom.1 ≫ k) hγpull.symm
      have hexstep :
          eCover.hom.1 ≫
              (((ΦT.map γ).hom I).1 ≫
                (canonicalPullbackChoice T.p).map I.f ((fiberFunctor F U).obj x)) =
            (eCover.hom.1 ≫ ((ΦT.map γ).hom I).1 ≫ ex.hom.1) ≫
              (toBasedFunctor F).map ((canonicalPullbackChoice X.p).map I.f x) := by
        simpa only [Category.assoc, ex] using
          congrArg
            (fun k ↦ eCover.hom.1 ≫ (((ΦT.map γ).hom I).1 ≫ k))
            hexpost.symm
      have hcalc := hcoverγ.trans (hγstep.trans hexstep)
      have hτI_val :
          τI.1 = eCover.hom.1 ≫ ((ΦT.map γ).hom I).1 ≫ ex.hom.1 := rfl
      simpa only [τI, hτI_val] using hcalc)
  simpa only [G, ΦT, τI, πI] using hrestrict

/-- Helper for Chap08 Lemma 8 6 11: the target stack makes its fixed-cover canonical descent
functor an equivalence. -/
theorem canonicalDescentFunctor_isEquivalence_of_stack
    (Y : FibredInGroupoidsOver C) [IsStackInGroupoids J Y.p]
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  -- Apply the owner coverwise stack criterion to the selected fixed cover.
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Y.p)).1 inferInstance U S

omit [IsStackInGroupoids J T.p] in
/-- Helper for Chap08 Lemma 8 6 11: the direct sheaf hypothesis makes every canonical slice
base change a stack on fixed covers. -/
theorem sliceTwoFibreProduct_coverwise_descent_isEquivalence_of_isoClassSheaf
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hSheaf :
      ∀ {V : C} (G : ofFunctor (Over.forget V) ⟶ T),
        Presheaf.IsSheaf (J.over V) ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf))
    {U : C} (G : ofFunctor (Over.forget U) ⟶ T)
    (V : Over U) (S : (J.over U).Cover V) :
    ((canonicalFiberPseudofunctor (F.sliceTwoFibreProduct G).p).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  -- First convert the iso-class sheaf condition to the owner stack-in-setoids structure, then
  -- apply the standard coverwise stack criterion on the slice site.
  letI : IsStackInSetoids (J.over U) (F.sliceTwoFibreProduct G).p :=
    sliceTwoFibreProduct_isStackInSetoids_of_isoClassPresheaf_isSheaf
      F hFaithful G (hSheaf G)
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J.over U) (p := (F.sliceTwoFibreProduct G).p)).1
      inferInstance V S
end FibredInGroupoidsMor

end

end CategoryTheory
