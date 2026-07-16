import stacks_proof.stacks_project.Chap08.Lemma_8_12_8.UnitSourceCharts

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

-- Proof sketch: the base-compatibility of `G` identifies `G ⋙ Y.p` with the projection of
-- `uₚ X`, and the previous theorem identifies the unit `X ⥤ uₚ X` followed by that projection
-- with `X.p ⋙ u`.
/-- The square determined by a based functor `uₚ X ⥤ T` commutes with the projections to `D`
after precomposing with the canonical unit `X ⥤ uₚ X`. -/
theorem pushforwardPullbackComparisonSquare_comm
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (FibredCategoryOver.pushforward u X).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    ((Functor.whiskeringRight X.S C D).obj u).obj X.p =
      ((Functor.whiskeringRight X.S Y.S D).obj Y.p).obj
        (pushforwardFibredCategoryUnit u X ⋙ G.toFunctor) := by
  -- First replace the unit followed by the pushforward projection by `X.p ⋙ u`,
  -- then use the based-functor square for `G` to move from `(FibredCategoryOver.pushforward u X).p` to `G ⋙ Y.p`.
  calc
    ((Functor.whiskeringRight X.S C D).obj u).obj X.p = X.p ⋙ u := by
      rfl
    _ = pushforwardFibredCategoryUnit u X ⋙ (FibredCategoryOver.pushforward u X).p :=
      (pushforwardFibredCategoryUnit_comp_projection u X).symm
    _ = pushforwardFibredCategoryUnit u X ⋙ (G.toFunctor ⋙ Y.p) := by
      rw [G.w]
    _ = (pushforwardFibredCategoryUnit u X ⋙ G.toFunctor) ⋙ Y.p := by
      simp [pushforwardFibredCategoryUnit, Functor.assoc]
    _ = ((Functor.whiskeringRight X.S Y.S D).obj Y.p).obj
        (pushforwardFibredCategoryUnit u X ⋙ G.toFunctor) := by
      simp [pushforwardFibredCategoryUnit, Functor.assoc]

/-- The commutative square over `u` and `Y.p` obtained from a based functor `uₚ X ⥤ T` by
precomposing with the canonical unit `X ⥤ uₚ X`. -/
noncomputable abbrev pushforwardPullbackComparisonSquare
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (FibredCategoryOver.pushforward u X).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    CategoricalPullback.CatCommSqOver u Y.p X.S :=
  { fst := X.p
    snd := pushforwardFibredCategoryUnit u X ⋙ G.toFunctor
    iso := eqToIso (pushforwardPullbackComparisonSquare_comm u X Y G) }

/-- The ambient based-functor category of functors `uₚ X ⥤ Y`. -/
abbrev pushforwardPullbackSourceBasedFunctorCategory
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :=
  (FibredCategoryOver.pushforward u X).toBasedCategory ⥤ᵇ Y.toBasedCategory

/-- The based functor `X ⥤ uᵖ Y` corresponding to a based functor `uₚ X ⥤ Y`. -/
noncomputable abbrev pushforwardPullbackComparisonFunctorObj
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : pushforwardPullbackSourceBasedFunctorCategory u X Y) :
    X.toBasedCategory ⥤ᵇ (u ᵖ Y).toBasedCategory where
  toFunctor :=
    (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback u Y.p X.S).obj
      (pushforwardPullbackComparisonSquare u X Y G)

-- Proof sketch: the source and target pullback objects have the same `C`-component `X.p.obj x`.
-- The first component of the morphism is therefore the identity, and the square-compatibility of
-- the second component is exactly the commutativity condition for `τ` over the base `D`.
/-- The second component of the pullback comparison morphism is compatible with the pullback
structure isomorphisms. -/
theorem pushforwardPullbackComparisonFunctorMapApp_w
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    u.map (𝟙 (X.p.obj x)) ≫ ((pushforwardPullbackComparisonFunctorObj u X Y G₂).obj x).iso.hom =
      ((pushforwardPullbackComparisonFunctorObj u X Y G₁).obj x).iso.hom ≫
        Y.p.map (τ.app ((pushforwardFibredCategoryUnit u X).obj x)) := by
  -- The pullback object stores the based-functor projection square, and the component of
  -- `τ` is vertical over the corresponding identity in the pushforward base.
  have hτ :=
    (IsHomLift.fac' Y.p
      (𝟙 ((FibredCategoryOver.pushforward u X).p.obj ((pushforwardFibredCategoryUnit u X).obj x)))
      (τ.app ((pushforwardFibredCategoryUnit u X).obj x))).symm
  simp only [CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_snd,
    Functor.comp_obj, Functor.map_id,
    CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_fst,
    CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_iso_hom,
    eqToIso.hom, eqToHom_app, Category.id_comp]
  simp only [pushforwardFibredCategoryUnit, pushforwardFibredCategoryUnitPrelocalized,
    Functor.comp_obj, Category.id_comp] at hτ
  rw [← hτ]
  simp

/-- The component at `x` of the natural transformation induced on pullback objects by a
transformation `τ : G₁ ⟶ G₂`. -/
noncomputable abbrev pushforwardPullbackComparisonFunctorMapApp
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    (pushforwardPullbackComparisonFunctorObj u X Y G₁).toFunctor.obj x ⟶
      (pushforwardPullbackComparisonFunctorObj u X Y G₂).toFunctor.obj x :=
  { fst := 𝟙 (X.p.obj x)
    snd := τ.app ((pushforwardFibredCategoryUnit u X).obj x)
    w := pushforwardPullbackComparisonFunctorMapApp_w u X Y τ x }

/-- Helper for Lemma 8.12.8: the `Y`-component of a comparison-map component is the original
based natural transformation component at the pushforward-unit object. -/
@[simp] theorem pushforwardPullbackComparisonFunctorMapApp_snd
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    (pushforwardPullbackComparisonFunctorMapApp u X Y τ x).snd =
      τ.app ((pushforwardFibredCategoryUnit u X).obj x) := by
  -- The comparison component was defined with this morphism as its second projection.
  rfl

-- Proof sketch: naturality of `τ` after precomposition with the unit `X ⥤ uₚ X` gives the
-- naturality of the second component, while the first component is the identity on the base
-- object `X.p.obj x`.
/-- The pullback comparison morphisms induced from a based natural transformation are natural in
the source object of `X`. -/
theorem pushforwardPullbackComparisonFunctor_map_naturality
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) :
    ∀ {x y : X.S} (f : x ⟶ y),
      (pushforwardPullbackComparisonFunctorObj u X Y G₁).toFunctor.map f ≫
          pushforwardPullbackComparisonFunctorMapApp u X Y τ y =
        pushforwardPullbackComparisonFunctorMapApp u X Y τ x ≫
          (pushforwardPullbackComparisonFunctorObj u X Y G₂).toFunctor.map f := by
  intro x y f
  -- Naturality in the pullback is checked on the base component and on the `Y`-component.
  apply CategoricalPullback.hom_ext
  · change X.p.map f ≫ 𝟙 (X.p.obj y) = 𝟙 (X.p.obj x) ≫ X.p.map f
    simp
  · change
      G₁.toFunctor.map ((pushforwardFibredCategoryUnit u X).map f) ≫
          τ.app ((pushforwardFibredCategoryUnit u X).obj y) =
        τ.app ((pushforwardFibredCategoryUnit u X).obj x) ≫
          G₂.toFunctor.map ((pushforwardFibredCategoryUnit u X).map f)
    exact τ.naturality ((pushforwardFibredCategoryUnit u X).map f)

-- Proof sketch: each component of the induced transformation in the pullback category has first
-- component the identity on `X.p.obj x`, so it is vertical over the identity morphism in `C`.
/-- The pullback comparison component lies over the identity on the base object `X.p.obj x`. -/
theorem pushforwardPullbackComparisonFunctorMapApp_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    (u ᵖ Y).p.IsHomLift (𝟙 (X.p.obj x))
      (pushforwardPullbackComparisonFunctorMapApp u X Y τ x) := by
  -- Normalize the pullback projection to `π₁`; the first component of the constructed map is the
  -- identity on the base object of `x`.
  rw [FibredCategoryOver.pullback_p]
  refine IsHomLift.of_fac' (CategoricalPullback.π₁ u Y.p) (𝟙 (X.p.obj x))
    (pushforwardPullbackComparisonFunctorMapApp u X Y τ x) rfl rfl ?_
  simp [pushforwardPullbackComparisonFunctorMapApp]

/-- The based natural transformation between the pullback comparison functors induced by
`τ : G₁ ⟶ G₂`. -/
noncomputable abbrev pushforwardPullbackComparisonFunctorMap
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) :
    pushforwardPullbackComparisonFunctorObj u X Y G₁ ⟶
      pushforwardPullbackComparisonFunctorObj u X Y G₂ where
  toNatTrans :=
    { app := fun x ↦ pushforwardPullbackComparisonFunctorMapApp u X Y τ x
      naturality := fun {_ _} f ↦
        pushforwardPullbackComparisonFunctor_map_naturality u X Y τ f }
  isHomLift' := pushforwardPullbackComparisonFunctorMapApp_isHomLift u X Y τ

/-- Helper for Lemma 8.12.8: equality of comparison maps gives equality of the original
components on pushforward-unit objects. -/
theorem pushforwardPullbackComparisonFunctorMap_unit_app_eq_of_eq
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    {τ σ : G₁ ⟶ G₂}
    (hτσ :
      pushforwardPullbackComparisonFunctorMap u X Y τ =
        pushforwardPullbackComparisonFunctorMap u X Y σ)
    (x : X.S) :
    τ.app ((pushforwardFibredCategoryUnit u X).obj x) =
      σ.app ((pushforwardFibredCategoryUnit u X).obj x) := by
  -- Project the equality in the pullback comparison to its `Y`-component at the unit object.
  have hUnitPullback := congrArg (fun η ↦ η.toNatTrans.app x) hτσ
  have hUnit := congrArg CategoricalPullback.Hom.snd hUnitPullback
  simpa only [pushforwardPullbackComparisonFunctorMapApp_snd] using hUnit

-- Proof sketch: the map on morphisms is defined componentwise from the identity vertical
-- transformation and the given based natural transformation `τ`. Identity components remain
-- identity after passing to the pullback category.
/-- The pullback comparison construction preserves identity `2`-morphisms. -/
theorem pushforwardPullbackBasedFunctor_map_id
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ∀ G : pushforwardPullbackSourceBasedFunctorCategory u X Y,
      pushforwardPullbackComparisonFunctorMap u X Y (𝟙 G) =
        𝟙 (pushforwardPullbackComparisonFunctorObj u X Y G) := by
  intro G
  -- Reduce equality of based natural transformations to equality of their pullback components.
  apply BasedNatTrans.ext
  ext x
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

-- Proof sketch: both sides are defined objectwise; the second component is the vertical
-- composition of the components of `τ` and `σ` after precomposition with the unit `X ⥤ uₚ X`,
-- while the first component stays the identity on the base.
/-- The pullback comparison construction preserves composition of `2`-morphisms. -/
theorem pushforwardPullbackBasedFunctor_map_comp
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ∀ {G₁ G₂ G₃ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
      (τ : G₁ ⟶ G₂) (σ : G₂ ⟶ G₃),
      pushforwardPullbackComparisonFunctorMap u X Y (τ ≫ σ) =
        pushforwardPullbackComparisonFunctorMap u X Y τ ≫
          pushforwardPullbackComparisonFunctorMap u X Y σ := by
  intro G₁ G₂ G₃ τ σ
  -- The comparison map is defined objectwise, so composition is checked on the two
  -- pullback projections at every object of `X`.
  apply BasedNatTrans.ext
  ext x
  apply CategoricalPullback.hom_ext
  · change 𝟙 (X.p.obj x) = 𝟙 (X.p.obj x) ≫ 𝟙 (X.p.obj x)
    simp
  · change
      τ.app ((pushforwardFibredCategoryUnit u X).obj x) ≫
          σ.app ((pushforwardFibredCategoryUnit u X).obj x) =
        (pushforwardPullbackComparisonFunctorMapApp u X Y τ x ≫
          pushforwardPullbackComparisonFunctorMapApp u X Y σ x).snd
    rfl

/-- The ambient functor sending a based functor `uₚ X ⥤ T` to the induced based functor
`X ⥤ uᵖ T`. -/
noncomputable abbrev pushforwardPullbackBasedFunctor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    pushforwardPullbackSourceBasedFunctorCategory u X Y ⥤
      (X.toBasedCategory ⥤ᵇ (u ᵖ Y).toBasedCategory) where
  obj G := pushforwardPullbackComparisonFunctorObj u X Y G
  map τ := pushforwardPullbackComparisonFunctorMap u X Y τ
  map_id := pushforwardPullbackBasedFunctor_map_id u X Y
  map_comp := pushforwardPullbackBasedFunctor_map_comp u X Y

-- Proof sketch: if `G : uₚ X ⟶ Y` preserves strongly cartesian morphisms, then after
-- precomposing with the unit `X ⥤ uₚ X` the induced functor to `Y` sends strongly cartesian
-- arrows in `X` to strongly cartesian arrows in `Y`. Since the pullback fibred category `uᵖ Y`
-- detects strong cartesianness on the `Y`-component, the induced functor `X ⟶ uᵖ Y` is again a
-- morphism of fibred categories.
/-- The pullback comparison construction sends morphisms of fibred categories `uₚ X ⟶ Y` to
morphisms of fibred categories `X ⟶ uᵖ Y`. -/
theorem pushforwardPullbackBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (FibredCategoryOver.pushforward u X) ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (((((fibredCategoryOverSubTwoCategory D).hom (FibredCategoryOver.pushforward u X) Y).inclusion) ⋙
        pushforwardPullbackBasedFunctor u X Y).obj G) := by
  intro a b φ hφ
  -- Strong cartesianness in the pullback is detected by the `Y`-component, and this component is
  -- obtained by applying `G` to the canonical pushforward-unit lift.
  refine pullbackProjection_isStronglyCartesian_of_snd u Y.p _ ?_
  exact FibredCategoryMor.map_stronglyCartesian G
    ((pushforwardFibredCategoryUnit u X).map φ)
    (pushforwardFibredCategoryUnit_preservesStronglyCartesian u X φ hφ)

/-- Helper for Lemma 8.12.8: forgetting a morphism of fibred categories to its underlying based
functor and repackaging it with the same preservation proof leaves the morphism unchanged. -/
theorem fibredCategoryMor_ofBasedFunctor_toBasedFunctor
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    FibredCategoryMor.ofBasedFunctor (FibredCategoryMor.toBasedFunctor F) F.obj.property = F := by
  -- This is definitional for the owner hom-category.
  rfl

/-- Helper for Lemma 8.12.8: an isomorphism of underlying based functors induces an isomorphism
of the corresponding owner morphisms of fibred categories. -/
noncomputable def fibredCategoryMorIsoOfBasedFunctorIso
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Helper for Lemma 8.12.8: the owner functor from admissible based functors to morphisms of
fibred categories is an equivalence of hom categories. -/
theorem fibredCategoryMorOfObjectProperty_isEquivalence
    (X Y : FibredCategoryOver C) :
    (FibredCategoryMor.ofObjectProperty X Y).IsEquivalence := by
  let P : ObjectProperty (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :=
    FibredCategoryMor.objectProperty X Y
  let F : P.FullSubcategory ⥤ (X ⟶ Y) :=
    FibredCategoryMor.ofObjectProperty X Y
  let G :
      (X ⟶ Y) ⥤
        (FibredCategoryMor.objectProperty X Y).FullSubcategory :=
    wideSubcategoryInclusion ((fibredCategoryOverSubTwoCategory C).hom₂ X Y)
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- On admissible based functors, packaging and then forgetting the owner wrapper changes only
    -- proof fields.
    refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact ObjectProperty.isoMk (P := P) (X := A) (Y := (F ⋙ G).obj A) (Iso.refl A.obj)
    · intro A B η
      apply ObjectProperty.hom_ext
      apply BasedNatTrans.ext
      ext a
      change η.hom.app a ≫ 𝟙 _ = 𝟙 _ ≫ η.hom.app a
      rw [Category.comp_id, Category.id_comp]
  · -- On owner morphisms, forgetting to the admissible based functor and repackaging is
    -- definitionally the identity.
    refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact
        fibredCategoryMorIsoOfBasedFunctorIso
          (F := (G ⋙ F).obj A) (G := A)
          (Iso.refl (FibredCategoryMor.toBasedFunctor A))
    · intro A B η
      apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      apply BasedNatTrans.ext
      ext a
      change η.hom.hom.app a ≫ 𝟙 _ = 𝟙 _ ≫ η.hom.hom.app a
      rw [Category.comp_id, Category.id_comp]

noncomputable abbrev pushforwardPullbackFibredMorphismLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :=
  (FibredCategoryMor.objectProperty X (u ᵖ Y)).lift
    ((((fibredCategoryOverSubTwoCategory D).hom (FibredCategoryOver.pushforward u X) Y).inclusion) ⋙
      pushforwardPullbackBasedFunctor u X Y)
    (fun G : (FibredCategoryOver.pushforward u X) ⟶ Y ↦
      show BasedFunctor.PreservesStronglyCartesian
          (((((fibredCategoryOverSubTwoCategory D).hom (FibredCategoryOver.pushforward u X) Y).inclusion) ⋙
            pushforwardPullbackBasedFunctor u X Y).obj G) from
        pushforwardPullbackBasedFunctor_preservesStronglyCartesian u X Y G)
end Pushforward

end

end CategoryTheory
