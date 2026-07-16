import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_42_5
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.TerminalCovers
import stacks_proof.stacks_project.Chap08.Definition_8_5_1
import stacks_proof.stacks_project.Chap08.Definition_8_6_1
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6.FixedCoverEquivalenceBridge
import stacks_proof.stacks_project.Chap08.Lemma_8_6_3

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FibredInGroupoidsOver C}
variable [IsStackInGroupoids J T.p]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

/-- Helper for Chap08 Lemma 8 6 11: the Yoneda inverse attached to a fiber object gives the
slice morphism over which source lifts will be descended. -/
noncomputable abbrev fiberObjectSliceMorphism
    (Y : FibredInGroupoidsOver C) {U : C} (y : Y.p.Fiber U) :
    ofFunctor (Over.forget U) ⟶ Y :=
  ofAmbientHom ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y)

/-- Helper for Chap08 Lemma 8 6 11: the identity slice object as an object of the fiber of
`Over.forget U` over `U`. -/
abbrev idSliceFiberObj (U : C) : (Over.forget U).Fiber U :=
  ⟨Over.mk (𝟙 U), rfl⟩

/-- Helper for Chap08 Lemma 8 6 11: the underlying total morphism of an identity in a functor
fiber is the identity morphism. -/
theorem fiberHom_id_val {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ C) {U : C}
    (x : p.Fiber U) :
    (𝟙 x : x ⟶ x).1 = 𝟙 x.1 := rfl

/-- Helper for Chap08 Lemma 8 6 11: evaluating the Yoneda-selected slice morphism at `id_U`
recovers the selected fiber object. -/
noncomputable def fiberObjectSliceMorphism_terminalEvaluationIso
    (Y : FibredInGroupoidsOver C) {U : C} (y : Y.p.Fiber U) :
    ((fiberFunctor (fiberObjectSliceMorphism Y y) U).obj (idSliceFiberObj U)) ≅ y := by
  -- This is exactly the counit of the Yoneda evaluation equivalence at the chosen fiber object.
  simpa [fiberObjectSliceMorphism, FibredInGroupoidsMor.fiberFunctor] using
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y

/-- Helper for Chap08 Lemma 8 6 11: a fibred-category morphism sends a hom-lift over a base arrow
to a hom-lift over the same base arrow. -/
theorem fibredCategoryMor_map_isHomLift_over_base
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} {a b : Y.S} {f : U ⟶ V} {ψ : a ⟶ b}
    (hψ : Y.p.IsHomLift f ψ) :
    Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map ψ) := by
  -- The based-functor compatibility of a fibred-category morphism transports the lift equation.
  letI : Y.p.IsHomLift f ψ := hψ
  exact (show Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map ψ) from inferInstance)

/-- Helper for Chap08 Lemma 8 6 11: a fibred-category morphism sends strongly cartesian arrows
to strongly cartesian arrows over the same displayed base arrow. -/
theorem fibredCategoryMor_map_stronglyCartesian_over_base
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} {a b : Y.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : Y.p.IsStronglyCartesian f φ) :
    Z.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map φ) := by
  -- Normalize the source strong-cartesian owner to the actual projected base morphism, map it,
  -- then rebase the target owner back to the external arrow `f`.
  have hφ' : Y.p.IsStronglyCartesian (Y.p.map φ) φ := by
    letI : Y.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift Y.p f φ
    simpa using hφ
  have hmap :
      Z.p.IsStronglyCartesian (Z.p.map ((FibredCategoryMor.toFunctor F).map φ))
        ((FibredCategoryMor.toFunctor F).map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  have hLift :
      Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) :=
    fibredCategoryMor_map_isHomLift_over_base (F := F) hφ.toIsHomLift
  letI : Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := hLift
  subst_hom_lift Z.p f ((FibredCategoryMor.toFunctor F).map φ)
  simpa using hmap

/-- Helper for Chap08 Lemma 8 6 11: every slice morphism is strongly cartesian for the slice
projection. -/
theorem sliceHom_isStronglyCartesian
    {U : C} {a b : Over U} (φ : a ⟶ b) :
    (Over.forget U).IsStronglyCartesian φ.left φ := by
  -- The slice projection is fibred in groupoids, so its morphisms are strongly cartesian.
  simpa using (show (Over.forget U).IsStronglyCartesian ((Over.forget U).map φ) φ from
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map φ)

/-- Helper for Chap08 Lemma 8 6 11: restricting the iso-class of the target of an actual
displayed morphism gives the iso-class of its source. -/
theorem fiberIsoClassPresheaf_map_mk_eq_of_hom
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered] [IsFibredInGroupoids p]
    {a b : S} (φ : a ⟶ b) :
    (p.fiberIsoClassPresheaf).map (p.map φ).op
        (Quotient.mk'' (⟨b, rfl⟩ : p.Fiber (p.obj b))) =
      Quotient.mk'' (⟨a, rfl⟩ : p.Fiber (p.obj a)) := by
  -- Compare the chosen pullback of `b` along `p.map φ` with the actual domain `a` of `φ`.
  let hc := canonicalPullbackChoice p
  letI : p.IsStronglyCartesian (p.map φ) (hc.map (p.map φ) ⟨b, rfl⟩) :=
    hc.isStronglyCartesian (p.map φ) ⟨b, rfl⟩
  letI : p.IsCartesian (p.map φ) (hc.map (p.map φ) ⟨b, rfl⟩) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := p) (f := p.map φ) (φ := hc.map (p.map φ) ⟨b, rfl⟩)
  letI : p.IsStronglyCartesian (p.map φ) φ :=
    (inferInstance : IsFibredInGroupoids p).isStronglyCartesian_map φ
  letI : p.IsCartesian (p.map φ) φ :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := p) (f := p.map φ) (φ := φ)
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (p.obj a)))
        (((canonicalPullbackChoice p).pullbackFunctor (p.map φ)).obj ⟨b, rfl⟩) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (p.obj a))) ⟨a, rfl⟩
  let e := Functor.IsCartesian.domainUniqueUpToIso p (p.map φ)
    (hc.map (p.map φ) ⟨b, rfl⟩) φ
  have hInvLift : p.IsHomLift (𝟙 (p.obj a)) e.inv := by
    change p.IsHomLift (𝟙 (p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso p (p.map φ)
        (hc.map (p.map φ) ⟨b, rfl⟩) φ).inv)
    infer_instance
  have hHomLift : p.IsHomLift (𝟙 (p.obj a)) e.hom := by
    change p.IsHomLift (𝟙 (p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso p (p.map φ)
        (hc.map (p.map φ) ⟨b, rfl⟩) φ).hom)
    infer_instance
  let eFiber :
      (((canonicalPullbackChoice p).pullbackFunctor (p.map φ)).obj ⟨b, rfl⟩) ≅
        ⟨a, rfl⟩ :=
    { hom := ⟨e.inv, hInvLift⟩
      inv := ⟨e.hom, hHomLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id }
  -- Passing to the quotient records the cartesian uniqueness isomorphism as equality of classes.
  rw [Quotient.eq'']
  exact ⟨eFiber⟩

/-- Helper for Chap08 Lemma 8 6 11: evaluating a slice morphism at an object of `C/U` is
isomorphic to the chosen pullback of its value at `id_U`. -/
theorem yonedaEvaluation_sliceObjectIsoPullback_exists
    (Y : FibredInGroupoidsOver C) {U : C}
    (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver)
    (a : Over U) :
    ∃ e :
      (FibredCategoryMor.fiberFunctor F a.left).obj
          (⟨a, rfl⟩ : (Over.forget U).Fiber a.left) ≅
        ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.obj
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F),
      e.hom.1 ≫
          (canonicalPullbackChoice Y.p).map a.hom
            ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F) =
        (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) := by
  -- Compare the actual arrow `F(a) ⟶ F(id_U)` with the chosen pullback arrow; both are
  -- cartesian over `a.hom`, so their domains are uniquely isomorphic over `a.left`.
  let φa : a ⟶ Over.mk (𝟙 U) := Over.homMk a.hom
  let hActual :
      Y.p.IsStronglyCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) := by
    exact fibredCategoryMor_map_stronglyCartesian_over_base
      (Y := FibredCategoryOver.ofFunctor (Over.forget U))
      (Z := Y.toFibredCategoryOver)
      (F := F)
      (sliceHom_isStronglyCartesian φa)
  let hChosen :
      Y.p.IsStronglyCartesian a.hom
        ((canonicalPullbackChoice Y.p).map a.hom
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F)) :=
    (canonicalPullbackChoice Y.p).isStronglyCartesian a.hom
      ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F)
  let hActualCart :
      Y.p.IsCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := Y.p) (f := a.hom) (φ := (FibredCategoryMor.toFunctor F).map φa)
  let hChosenCart :
      Y.p.IsCartesian a.hom
        ((canonicalPullbackChoice Y.p).map a.hom
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F)) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := Y.p) (f := a.hom)
      (φ := (canonicalPullbackChoice Y.p).map a.hom
        ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F))
  let e :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ Y.p _ _ _ _ a.hom
      ((canonicalPullbackChoice Y.p).map a.hom
        ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F))
      hChosenCart
      _
      ((FibredCategoryMor.toFunctor F).map φa)
      hActualCart
  have hHomLift :
      Y.p.IsHomLift (𝟙 a.left) e.hom := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
        Y.p _ _ _ _ a.hom
        ((canonicalPullbackChoice Y.p).map a.hom
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F))
        hChosenCart
        _
        ((FibredCategoryMor.toFunctor F).map φa)
        hActualCart)
  have hInvLift :
      Y.p.IsHomLift (𝟙 a.left) e.inv := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
        Y.p _ _ _ _ a.hom
        ((canonicalPullbackChoice Y.p).map a.hom
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F))
        hChosenCart
        _
        ((FibredCategoryMor.toFunctor F).map φa)
        hActualCart)
  let eFiber :
      (FibredCategoryMor.fiberFunctor F a.left).obj
          (⟨a, rfl⟩ : (Over.forget U).Fiber a.left) ≅
        ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.obj
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F) :=
    { hom := ⟨e.hom, hHomLift⟩
      inv := ⟨e.inv, hInvLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  refine ⟨eFiber, ?_⟩
  -- The comparison isomorphism is the cartesian uniqueness map, so postcomposition recovers
  -- the actual slice restriction arrow.
  change e.hom ≫
      (canonicalPullbackChoice Y.p).map a.hom
        ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F) =
    (FibredCategoryMor.toFunctor F).map φa
  simpa [e] using
    (Functor.IsCartesian.domainUniqueUpToIso_hom Y.p a.hom
      ((canonicalPullbackChoice Y.p).map a.hom
        ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F))
      ((FibredCategoryMor.toFunctor F).map φa))

/-- Helper for Chap08 Lemma 8 6 11: the concrete evaluated-slice comparison is the chosen
isomorphism supplied by cartesian uniqueness. -/
noncomputable def yonedaEvaluation_sliceObjectIsoPullback
    (Y : FibredInGroupoidsOver C) {U : C}
    (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver)
    (a : Over U) :
    (FibredCategoryMor.fiberFunctor F a.left).obj
        (⟨a, rfl⟩ : (Over.forget U).Fiber a.left) ≅
      ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.obj
        ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F) :=
  Classical.choose (yonedaEvaluation_sliceObjectIsoPullback_exists Y F a)

/-- Helper for Chap08 Lemma 8 6 11: the evaluated-slice comparison composes with the chosen
cartesian pullback arrow to the actual restriction map in the slice. -/
theorem yonedaEvaluation_sliceObjectIsoPullback_hom_postcompose
    (Y : FibredInGroupoidsOver C) {U : C}
    (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver)
    (a : Over U) :
    (yonedaEvaluation_sliceObjectIsoPullback Y F a).hom.1 ≫
        (canonicalPullbackChoice Y.p).map a.hom
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F) =
      (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) :=
  Classical.choose_spec (yonedaEvaluation_sliceObjectIsoPullback_exists Y F a)

/-- Helper for Chap08 Lemma 8 6 11: evaluating the Yoneda-selected slice morphism at an arbitrary
slice object is the canonical pullback of the selected fiber object along that slice arrow. -/
noncomputable def fiberObjectSliceMorphism_evaluationIso
    (Y : FibredInGroupoidsOver C) {U : C} (y : Y.p.Fiber U) (a : Over U) :
    ((fiberFunctor (fiberObjectSliceMorphism Y y) a.left).obj
        (⟨a, rfl⟩ : (Over.forget U).Fiber a.left)) ≅
      ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.obj y :=
  -- The general evaluation comparison is the Yoneda pullback comparison followed by the pulled
  -- counit identifying the evaluated value at `id_U` with `y`.
  let F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y
  let e₁ := yonedaEvaluation_sliceObjectIsoPullback Y F a
  let e₂ := ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.mapIso
    ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y)
  e₁ ≪≫ e₂

/-- Helper for Chap08 Lemma 8 6 11: the arbitrary slice-evaluation comparison composes with the
chosen pullback arrow to the actual restriction of the terminal evaluation map. -/
theorem fiberObjectSliceMorphism_evaluationIso_hom_postcompose
    (Y : FibredInGroupoidsOver C) {U : C} (y : Y.p.Fiber U)
    (a : Over U) (φ : a ⟶ Over.mk (𝟙 U)) :
    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map φ ≫
        (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 =
      (fiberObjectSliceMorphism_evaluationIso Y y a).hom.1 ≫
        (canonicalPullbackChoice Y.p).map a.hom y := by
  -- First normalize the displayed arrow to the unique map from `a` to the terminal slice object.
  have hφ : φ = Over.homMk a.hom := by
    ext
    simpa using (Over.w φ)
  subst φ
  let F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y
  let y₀ : Y.p.Fiber U :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F
  let e₁ := yonedaEvaluation_sliceObjectIsoPullback Y F a
  let e₂ := ((canonicalFiberPseudofunctor Y.p).map a.hom.op.toLoc).toFunctor.mapIso
    ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y)
  have he₁ :
      e₁.hom.1 ≫ (canonicalPullbackChoice Y.p).map a.hom y₀ =
        (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) := by
    simpa [F, y₀, e₁] using
      yonedaEvaluation_sliceObjectIsoPullback_hom_postcompose Y F a
  have he₂ :
      e₂.hom.1 ≫ (canonicalPullbackChoice Y.p).map a.hom y =
        (canonicalPullbackChoice Y.p).map a.hom y₀ ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
    simpa [e₂, y₀] using
      canonical_pullbackFunctor_map_fac (p := Y.p) (f := a.hom)
        (φ := ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom)
  have hpost :
      (fiberObjectSliceMorphism_evaluationIso Y y a).hom.1 ≫
          (canonicalPullbackChoice Y.p).map a.hom y =
        (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
    change (e₁.hom.1 ≫ e₂.hom.1) ≫
          (canonicalPullbackChoice Y.p).map a.hom y =
        (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1
    have hstep :
        (e₁.hom.1 ≫ e₂.hom.1) ≫ (canonicalPullbackChoice Y.p).map a.hom y =
          e₁.hom.1 ≫
            ((canonicalPullbackChoice Y.p).map a.hom y₀ ≫
              ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1) := by
      simpa only [Category.assoc] using congrArg (fun k ↦ e₁.hom.1 ≫ k) he₂
    have hlast :
        e₁.hom.1 ≫
            ((canonicalPullbackChoice Y.p).map a.hom y₀ ≫
              ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1) =
          (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) ≫
            ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
      simpa only [← Category.assoc] using
        congrArg
          (fun k ↦ k ≫
            ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1)
          he₁
    exact hstep.trans hlast
  -- The terminal evaluation is the same Yoneda counit in the fiber over `U`.
  simpa [fiberObjectSliceMorphism, F, FibredInGroupoidsMor.fiberFunctor] using hpost.symm

/-- Helper for Chap08 Lemma 8 6 11: evaluating the Yoneda-selected slice morphism at a cover
arrow is the canonical pullback of the selected fiber object along that cover arrow. -/
noncomputable def fiberObjectSliceMorphism_coverEvaluationIso
    (Y : FibredInGroupoidsOver C) {U : C} (S : J.Cover U)
    (y : Y.p.Fiber U) (I : S.Arrow) :
    ((fiberFunctor (fiberObjectSliceMorphism Y y) I.Y).obj
        (⟨Over.mk I.f, rfl⟩ : (Over.forget U).Fiber I.Y)) ≅
      ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y :=
  -- The evaluated Yoneda inverse first compares to the pullback of its value at `id_U`; the
  -- counit then identifies that value with the selected object `y`.
  let F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y
  let e₁ := yonedaEvaluation_sliceObjectIsoPullback Y F (Over.mk I.f)
  let e₂ := ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso
    ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y)
  e₁ ≪≫ e₂

/-- Helper for Chap08 Lemma 8 6 11: the cover-evaluation comparison composes with the chosen
pullback arrow to the actual restriction of the terminal evaluation map. -/
theorem fiberObjectSliceMorphism_coverEvaluationIso_hom_postcompose
    (Y : FibredInGroupoidsOver C) {U : C} (S : J.Cover U)
    (y : Y.p.Fiber U) (I : S.Arrow)
    (a : Over.mk I.f ⟶ Over.mk (𝟙 U)) :
    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
        (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 =
      (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 ≫
        (canonicalPullbackChoice Y.p).map I.f y := by
  -- Reduce to the underlying total-category equality: the two comparison isomorphisms were chosen
  -- by cartesian uniqueness and functoriality of the canonical pullback.
  have ha : a = Over.homMk I.f := by
    ext
    simpa using (Over.w a)
  subst a
  let F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ Y.toFibredCategoryOver :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y
  let y₀ : Y.p.Fiber U :=
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).obj F
  let e₁ := yonedaEvaluation_sliceObjectIsoPullback Y F (Over.mk I.f)
  let e₂ := ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.mapIso
    ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y)
  have he₁ :
      e₁.hom.1 ≫ (canonicalPullbackChoice Y.p).map I.f y₀ =
        (FibredCategoryMor.toFunctor F).map (Over.homMk I.f) := by
    simpa [F, y₀, e₁] using
      yonedaEvaluation_sliceObjectIsoPullback_hom_postcompose Y F (Over.mk I.f)
  have he₂ :
      e₂.hom.1 ≫ (canonicalPullbackChoice Y.p).map I.f y =
        (canonicalPullbackChoice Y.p).map I.f y₀ ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
    simpa [e₂, y₀] using
      canonical_pullbackFunctor_map_fac (p := Y.p) (f := I.f)
        (φ := ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom)
  have hcover :
      (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 ≫
          (canonicalPullbackChoice Y.p).map I.f y =
        (FibredCategoryMor.toFunctor F).map (Over.homMk I.f) ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
    change (e₁.hom.1 ≫ e₂.hom.1) ≫
          (canonicalPullbackChoice Y.p).map I.f y =
        (FibredCategoryMor.toFunctor F).map (Over.homMk I.f) ≫
          ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1
    have hstep :
        (e₁.hom.1 ≫ e₂.hom.1) ≫ (canonicalPullbackChoice Y.p).map I.f y =
          e₁.hom.1 ≫
            ((canonicalPullbackChoice Y.p).map I.f y₀ ≫
              ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1) := by
      simpa only [Category.assoc] using congrArg (fun k ↦ e₁.hom.1 ≫ k) he₂
    have hlast :
        e₁.hom.1 ≫
            ((canonicalPullbackChoice Y.p).map I.f y₀ ≫
              ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1) =
          (FibredCategoryMor.toFunctor F).map (Over.homMk I.f) ≫
            ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1 := by
      simpa only [← Category.assoc] using
        congrArg
          (fun k ↦ k ≫
            ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y).hom.1)
          he₁
    exact hstep.trans hlast
  simpa [fiberObjectSliceMorphism, F, FibredInGroupoidsMor.fiberFunctor] using hcover.symm

/-- Helper for Chap08 Lemma 8 6 11: restricting the cover-evaluation comparison along one
slice arrow agrees with the arbitrary slice evaluation after the canonical composition
comparison. -/
theorem fiberObjectSliceMorphism_coverEvaluationIso_restrict_hom
    (Y : FibredInGroupoidsOver C) {U : C} (S : J.Cover U)
    (y : Y.p.Fiber U) (I : S.Arrow) {Z : Over U}
    (a : Z ⟶ Over.mk I.f) :
    let ha : a.left ≫ I.f = Z.hom := by simpa using (Over.w a)
    let c := (canonicalFiberPseudofunctor Y.p).mapComp'
      I.f.op.toLoc a.left.op.toLoc Z.hom.op.toLoc
      (comp_toLoc_eq I.f a.left Z.hom ha)
    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
        (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 =
      (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
        (c.hom.toNatTrans.app y).1 ≫
        (canonicalPullbackChoice Y.p).map a.left
          (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y) := by
  -- Both arrows are over the slice map `a.left`; postcompose with the chosen pullback along
  -- `I.f` and use the terminal-evaluation formulas for the cover and arbitrary slice.
  dsimp only
  let ha : a.left ≫ I.f = Z.hom := by
    simpa using (Over.w a)
  let c := (canonicalFiberPseudofunctor Y.p).mapComp'
    I.f.op.toLoc a.left.op.toLoc Z.hom.op.toLoc
    (comp_toLoc_eq I.f a.left Z.hom ha)
  let left :=
    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
      (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1
  let right :=
    (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
      (c.hom.toNatTrans.app y).1 ≫
      (canonicalPullbackChoice Y.p).map a.left
        (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y)
  have hleftLift : Y.p.IsHomLift a.left left := by
    -- The restriction map is over `a.left`, followed by a vertical cover-evaluation component.
    let eCover := fiberObjectSliceMorphism_coverEvaluationIso Y S y I
    have hmap :
        Y.p.IsHomLift a.left ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map a) := by
      exact
        (BasedFunctor.isHomLift_iff (toBasedFunctor (fiberObjectSliceMorphism Y y)) a.left a).2
          (sliceHom_isStronglyCartesian a).toIsHomLift
    have hcover :
        Y.p.IsHomLift (𝟙 I.Y)
          (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 :=
      (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.2
    letI : Y.p.IsHomLift a.left ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map a) := hmap
    letI :
        Y.p.IsHomLift (𝟙 I.Y)
          (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 := hcover
    simpa [left, eCover] using
      (@IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        a.left ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map a) hmap I.Y
        (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 hcover)
  have hrightLift : Y.p.IsHomLift a.left right := by
    -- The arbitrary evaluation and composition-comparison components are vertical, followed by
    -- the chosen pullback over `a.left`.
    let tail :=
      (canonicalPullbackChoice Y.p).map a.left
        (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y)
    have heval : Y.p.IsHomLift (𝟙 Z.left) (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 :=
      (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.2
    have hcomp : Y.p.IsHomLift (𝟙 Z.left) (c.hom.toNatTrans.app y).1 :=
      (c.hom.toNatTrans.app y).2
    have htail : Y.p.IsHomLift a.left tail := by
      exact
        ((canonicalPullbackChoice Y.p).isStronglyCartesian a.left
          (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y)).toIsHomLift
    letI : Y.p.IsHomLift (𝟙 Z.left) (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 := heval
    letI : Y.p.IsHomLift (𝟙 Z.left) (c.hom.toNatTrans.app y).1 := hcomp
    have hhead :
        Y.p.IsHomLift (𝟙 Z.left)
          ((fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
            (c.hom.toNatTrans.app y).1) := by
      exact
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          (𝟙 Z.left) (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 heval Z.left
          (c.hom.toNatTrans.app y).1 hcomp
    letI :
        Y.p.IsHomLift (𝟙 Z.left)
          ((fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
            (c.hom.toNatTrans.app y).1) := hhead
    letI : Y.p.IsHomLift a.left tail := htail
    have hright' :
        Y.p.IsHomLift a.left
          (((fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
              (c.hom.toNatTrans.app y).1) ≫ tail) := by
      exact
        @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
          Z.left
          ((fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
            (c.hom.toNatTrans.app y).1)
          hhead _ _ a.left tail htail
    simpa [right, tail, Category.assoc] using hright'
  letI : Y.p.IsHomLift a.left left := hleftLift
  letI : Y.p.IsHomLift a.left right := hrightLift
  change left = right
  have hpost :
      left ≫ (canonicalPullbackChoice Y.p).map I.f y =
        right ≫ (canonicalPullbackChoice Y.p).map I.f y := by
    let terminalArrow : Over.mk I.f ⟶ Over.mk (𝟙 U) :=
      Over.homMk (U := Over.mk I.f) (V := Over.mk (𝟙 U)) I.f (by simp)
    have hcover :=
      fiberObjectSliceMorphism_coverEvaluationIso_hom_postcompose
        (Y := Y) (S := S) y I terminalArrow
    have heval :=
      fiberObjectSliceMorphism_evaluationIso_hom_postcompose
        (Y := Y) y Z (a ≫ terminalArrow)
    have hcomp :=
      canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Y.p) I.f a.left Z.hom ha y
    calc
      ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
            (fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1) ≫
          (canonicalPullbackChoice Y.p).map I.f y =
        (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
          ((fiberObjectSliceMorphism_coverEvaluationIso Y S y I).hom.1 ≫
            (canonicalPullbackChoice Y.p).map I.f y) := by
            rw [Category.assoc]
      _ =
        (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
          ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map terminalArrow ≫
            (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1) := by
            exact congrArg
              (fun k ↦ (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫ k)
              hcover.symm
      _ =
        (toBasedFunctor (fiberObjectSliceMorphism Y y)).map (a ≫ terminalArrow) ≫
          (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 := by
            have hmap :
                (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
                    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map terminalArrow =
                  (toBasedFunctor (fiberObjectSliceMorphism Y y)).map (a ≫ terminalArrow) := by
              exact ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map_comp a terminalArrow).symm
            calc
              (toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
                    (toBasedFunctor (fiberObjectSliceMorphism Y y)).map terminalArrow ≫
                    (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 =
                  ((toBasedFunctor (fiberObjectSliceMorphism Y y)).map a ≫
                      (toBasedFunctor (fiberObjectSliceMorphism Y y)).map terminalArrow) ≫
                    (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 := by
                    exact (Category.assoc _ _ _).symm
              _ =
                  (toBasedFunctor (fiberObjectSliceMorphism Y y)).map (a ≫ terminalArrow) ≫
                    (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1 := by
                    exact congrArg
                      (fun k ↦ k ≫ (fiberObjectSliceMorphism_terminalEvaluationIso Y y).hom.1)
                      hmap
      _ =
        (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
          (canonicalPullbackChoice Y.p).map Z.hom y := by
            exact heval
      _ =
        ((fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫
            (c.hom.toNatTrans.app y).1 ≫
            (canonicalPullbackChoice Y.p).map a.left
              (((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor.obj y)) ≫
          (canonicalPullbackChoice Y.p).map I.f y := by
            simpa only [c, Category.assoc] using
              (congrArg
                (fun k ↦ (fiberObjectSliceMorphism_evaluationIso Y y Z).hom.1 ≫ k)
                hcomp).symm
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      I.f ((canonicalPullbackChoice Y.p).map I.f y)
      ((canonicalPullbackChoice Y.p).isStronglyCartesian I.f y)
      _ _ a.left left right hleftLift hrightLift hpost
end FibredInGroupoidsMor

end

end CategoryTheory
