import StacksProject_2024.Chap08.Lemma_8_8_5.InertiaCartesian

universe u v

namespace CategoryTheory

open CategoryOver FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] uliftCategory

/-- Helper for Chap08 Lemma 8 8 5: the Hom-presheaf `W` field of a stackification transports
across an owner isomorphism of morphisms with the same stack target. -/
private theorem morphismPresheafMap_W_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y)) :
    ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y) := by
  intro U x y
  -- The owner isomorphism conjugates the target Hom presheaf by fiberwise isomorphisms.
  let τ :=
    (fiberHomPresheafIso (Y := D.toFibredCategoryOver)
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x)
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y)).hom
  have hfac :
      FibredCategoryMor.fibredMorphismPresheafMap G x y =
        FibredCategoryMor.fibredMorphismPresheafMap F x y ≫ τ := by
    ext W δ
    exact fibredMorphismPresheafMap_natural_of_ownerIso_app α x y W δ
  have hIso : MorphismProperty.isomorphisms _ τ := by
    infer_instance
  -- Postcomposition by an isomorphism does not change membership in the local class.
  rw [hfac]
  exact
    (((GrothendieckTopology.W (J := J.over U) (A := Type _)).postcomp_iff
      (W' := MorphismProperty.isomorphisms _)
      (FibredCategoryMor.fibredMorphismPresheafMap F x y)
      τ hIso).2 (hF U x y))

/-- Helper for Chap08 Lemma 8 8 5: local essential surjectivity transports across an owner
isomorphism of morphisms with the same stack target. -/
private theorem locallyEssentiallySurjectiveOnObjects_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J F) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J G := by
  intro U y
  -- Reuse the cover and source objects for `F`; the fiberwise component of `α` changes the image.
  obtain ⟨S, hS⟩ := hF U y
  refine ⟨S, ?_⟩
  intro I
  obtain ⟨x, ⟨ηF⟩⟩ := hS I
  let ηα :=
    basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) I.Y x
  exact ⟨x, ⟨ηα.symm ≪≫ ηF⟩⟩

/-- Helper for Chap08 Lemma 8 8 5: being a stackification is invariant under owner isomorphism
of the comparison morphism. -/
theorem isStackification_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : FibredCategoryMor.IsStackification F) :
    FibredCategoryMor.IsStackification G := by
  constructor
  · -- Transport the Hom-presheaf local equivalence field through the owner isomorphism.
    exact morphismPresheafMap_W_of_ownerIso α hF.morphismPresheafMap_W
  · -- Transport the local object-image field through the same fiberwise isomorphism.
    exact locallyEssentiallySurjectiveOnObjects_of_ownerIso α
      hF.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 5: precomposing a stackification with a source equivalence over
the base preserves the stackification condition. -/
theorem isStackification_comp_left_of_isEquivalenceOverBase
    {A B : FibredCategoryOver C} {D : StackOver J}
    (E : A ⟶ B)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : B ⟶ D)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (E ≫ G) := by
  refine ⟨?_, ?_⟩
  · intro U x y
    -- The composite Hom-presheaf map factors through an isomorphism induced by the source
    -- equivalence and then through the stackification map for `G`.
    rw [fibredMorphismPresheafMap_comp E G x y]
    have hIso : IsIso (fibredMorphismPresheafMap E x y) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase E hE x y
    let _ : IsIso (fibredMorphismPresheafMap E x y) := hIso
    exact
      (J.over U).W.comp_mem _ _
        ((J.over U).W.of_isIso (fibredMorphismPresheafMap E x y))
        (hG.morphismPresheafMap_W U
          ((FibredCategoryMor.fiberFunctor E U).obj x)
          ((FibredCategoryMor.fiberFunctor E U).obj y))
  · -- Local essential surjectivity is stable under precomposition by a source equivalence.
    exact
      locallyEssentiallySurjectiveOnObjects_comp_left_of_isEquivalenceOverBase
        E hE G hG.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 5: if postcomposition with a target equivalence over the base is
a stackification, then the original morphism is already a stackification. -/
theorem isStackification_of_comp_right_isEquivalenceOverBase
    {A : FibredCategoryOver C} {D E : StackOver J}
    (F : A ⟶ D)
    (H : D.toFibredCategoryOver ⟶ E)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H)
    (hFH : FibredCategoryMor.IsStackification (F ≫ H)) :
    FibredCategoryMor.IsStackification F := by
  constructor
  · intro U x y
    -- Reflect the Hom-presheaf `W` condition through the isomorphism induced by `H`.
    have hcomp := hFH.morphismPresheafMap_W U x y
    rw [fibredMorphismPresheafMap_comp F H x y] at hcomp
    have hIso : IsIso (fibredMorphismPresheafMap H
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase H hH
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)
    let τ := fibredMorphismPresheafMap H
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)
    let _ : IsIso τ := hIso
    have hIsoProp : MorphismProperty.isomorphisms _ τ := by
      infer_instance
    have hcomp' :
        (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y ≫ τ) := by
      exact hcomp
    exact
      (((GrothendieckTopology.W (J := J.over U) (A := Type _)).postcomp_iff
        (W' := MorphismProperty.isomorphisms _)
        (FibredCategoryMor.fibredMorphismPresheafMap F x y)
        τ hIsoProp).1 hcomp')
  · intro U y
    -- Lift the image of `y` locally through the composite, then reflect the resulting fiber
    -- isomorphism back through the fully faithful fiber functor of the equivalence `H`.
    obtain ⟨S, hS⟩ := hFH.locallyEssentiallySurjectiveOnObjects U
      ((FibredCategoryMor.fiberFunctor H U).obj y)
    refine ⟨S, ?_⟩
    intro I
    obtain ⟨x, ⟨ηFH⟩⟩ := hS I
    have hFiberEquiv : (FibredCategoryMor.fiberFunctor H I.Y).IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        (FibredCategoryMor.toBasedFunctor H) hH I.Y
    let Φ := FibredCategoryMor.fiberFunctor H I.Y
    let _ : Φ.IsEquivalence := hFiberEquiv
    have hFF : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
    let ηTarget :
        Φ.obj ((FibredCategoryMor.fiberFunctor F I.Y).obj x) ≅
          Φ.obj (I.f ^*[canonicalPullbackChoice D.p] y) := by
      change (FibredCategoryMor.fiberFunctor (F ≫ H) I.Y).obj x ≅
          Φ.obj (I.f ^*[canonicalPullbackChoice D.p] y)
      exact ηFH ≪≫ (FibredCategoryMor.pullbackComparison H I.f y)
    exact ⟨x, ⟨hFF.preimageIso ηTarget⟩⟩

end CategoryTheory
