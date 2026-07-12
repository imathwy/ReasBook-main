import StacksProject_2024.Chap07.Lemma_7_28_5.TypeSheafification

open CategoryTheory
open CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃ t w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

/-- Helper for Lemma 7.28.5: formal universe bridge for the source proof.

The source statement only needs the inverse-image square `j_V^{-1} (u')^{-1} ≅ u^{-1} j^{-1}`
on set-valued sheaves. The current formal proof transports that square through an auxiliary
`ULift` universe; this helper is exactly the required `W = local bijectivity` bridge in that
auxiliary universe, not an extra mathematical hypothesis of Lemma 7.28.5. -/
theorem large_type_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max t w))]
    [UnivLE.{max u₃ v₃, max t w}] :
    L.WEqualsLocallyBijective (Type (max t w)) := by
  let T := Type (max t w)
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ forget T)
    -- Route correction: the concrete plus-plus proof only applies when the target type universe
    -- contains the site shapes; the explicit `UnivLE` side condition records that private bridge.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (L := L) (P := P ⋙ forget T)
    -- The same comparison transfers local surjectivity from the concrete sheafification unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  -- Package unitwise local bijectivity into the canonical `W = locally bijective` class.
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := T)

/-- Helper for Lemma 7.28.5: when the small `Type t` universe already has the concrete
plus-plus shapes needed by the sheafification owner, the `ULift` functor preserves
sheafification by the standard concrete-category criterion. -/
theorem uliftFunctor_preservesSheafification_type_of_small_shapes
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [UnivLE.{max u₃ v₃, max t w}]
    [∀ (M : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan M) (Type t)]
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  let _ :
      ∀ (M : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
        Limits.HasLimitsOfShape (Limits.WalkingMulticospan M) Ts := by
    intro M
    infer_instance
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ Ts := by
    intro X
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ F := by
    intro X
    infer_instance
  let _ :
      ∀ (X : E) (S : L.Cover X) (P : Eᵒᵖ ⥤ Type t),
        Limits.PreservesLimit (S.index P).multicospan F := by
    intro X S P
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget (Type t)) := by
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget Ts) := by
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t)) := by
    intro X
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget Ts) := by
    intro X
    infer_instance
  let _ : (forget (Type t)).ReflectsIsomorphisms := by
    infer_instance
  let _ : (forget Ts).ReflectsIsomorphisms := by
    infer_instance
  -- With all concrete plus-plus owners named, the standard preservation instance applies
  -- without broad instance search through unrelated universe-transport paths.
  simpa [F, Ts] using
    (CategoryTheory.GrothendieckTopology.instPreservesSheafification
      (J := L) (F := F))

/-- Helper for Lemma 7.28.5: the fixed `ULift` functor on types preserves sheafification for any
site once the small and large sheafification units are known to be locally bijective. -/
theorem uliftFunctor_preservesSheafification_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [UnivLE.{max u₃ v₃, t}]
    [UnivLE.{max u₃ v₃, max t w}] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) := by
  let _ : L.WEqualsLocallyBijective (Type t) :=
    @type_WEqualsLocallyBijective_of_hasWeakSheafify.{u₃, v₃, t}
      E _ L inferInstance inferInstance
  let _ : L.WEqualsLocallyBijective (Type (max t w)) :=
    @type_WEqualsLocallyBijective_of_hasWeakSheafify.{u₃, v₃, max t w}
      E _ L inferInstance inferInstance
  -- Once both Type universes identify `W` with local bijectivity, `ULift` preserves
  -- sheafification by the explicit local-bijectivity transport theorem.
  exact
    @uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective.{u₃, v₃, t, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.28.5: once the small sheafification unit is locally bijective, its
`ULift`-whiskering is already a `W`-morphism in the larger target universe. -/
theorem whiskered_toSheafify_W_for_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [UnivLE.{max u₃ v₃, t}]
    [UnivLE.{max u₃ v₃, max t w}]
    (P : Eᵒᵖ ⥤ Type t) :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  let hPres : L.PreservesSheafification F :=
    @uliftFunctor_preservesSheafification_type.{u₃, v₃, t, w} E _ L inferInstance inferInstance
      inferInstance inferInstance
  let hW : L.WEqualsLocallyBijective Ts :=
    @large_type_WEqualsLocallyBijective.{u₃, v₃, t, w} E _ L inferInstance inferInstance
  let _ : L.WEqualsLocallyBijective Ts := hW
  have hLargeInj :
      Presheaf.IsLocallyInjective L (toSheafify L (P ⋙ F)) := by
    exact ((L.W_iff_isLocallyBijective (toSheafify L (P ⋙ F))).1 (L.W_toSheafify (P ⋙ F))).1
  have hLargeSurj :
      Presheaf.IsLocallySurjective L (toSheafify L (P ⋙ F)) := by
    exact ((L.W_iff_isLocallyBijective (toSheafify L (P ⋙ F))).1 (L.W_toSheafify (P ⋙ F))).2
  rcases
      small_type_toSheafify_isLocallyBijective_for_site (L := L) P hPres hLargeInj hLargeSurj with
    ⟨hSmallInj, hSmallSurj⟩
  let _ : Presheaf.IsLocallyInjective L (toSheafify L P) := hSmallInj
  let _ : Presheaf.IsLocallySurjective L (toSheafify L P) := hSmallSurj
  -- Once the small unit is locally bijective, its `ULift`-whiskering is in `W`.
  exact
    whiskered_toSheafify_W_of_small_unit_local_bijectivity (L := L) P hW

/-- Helper for Lemma 7.28.5: for any site, the `ULift` sheafification comparison component is an
isomorphism because the whiskered sheafification unit is locally bijective upstairs. -/
theorem ulift_sheafComposeNatTrans_app_isIso_for_site
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [UnivLE.{max u₃ v₃, t}]
    [UnivLE.{max u₃ v₃, max t w}]
    (P : Eᵒᵖ ⥤ Type t) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))
          (sheafificationAdjunction L (Type t))
          (sheafificationAdjunction L (Type (max t w)))).app P) := by
  -- Route correction: first reduce the comparison component to the source-faithful `W`-statement
  -- for the whiskered sheafification unit, then close that `W`-goal via local bijectivity.
  rw [ulift_sheafComposeNatTrans_app_isIso_iff_whiskered_toSheafify_W (L := L) (P := P)]
  -- The explicit `W`-bridge isolates the only universe-sensitive step.
  exact whiskered_toSheafify_W_for_ulift (L := L) P

/-- Helper for Lemma 7.28.5: under a universe inequality, a function between small type
carriers transports to their `Shrink` models. -/
@[implicit_reducible] noncomputable def typeShrinkMap
    [UnivLE.{t, w}] {X Y : Type t} (f : X ⟶ Y) :
    Shrink.{w} X → Shrink.{w} Y :=
  fun x => equivShrink Y (f ((equivShrink X).symm x))

/-- Helper for Lemma 7.28.5: shrink transport respects identity maps. -/
theorem typeShrinkMap_id
    [UnivLE.{t, w}] (X : Type t) :
    typeShrinkMap (𝟙 X) = id := by
  funext x
  change equivShrink X ((𝟙 X) ((equivShrink X).symm x)) = x
  simp

/-- Helper for Lemma 7.28.5: shrink transport respects composition of maps. -/
theorem typeShrinkMap_comp
    [UnivLE.{t, w}] {X Y Z : Type t} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typeShrinkMap (f ≫ g) = typeShrinkMap g ∘ typeShrinkMap f := by
  funext x
  change equivShrink Z (g (f ((equivShrink X).symm x))) =
    equivShrink Z (g ((equivShrink Y).symm (equivShrink Y (f ((equivShrink X).symm x)))))
  simp

/-- Helper for Lemma 7.28.5: shrink-transported functions can be unshrunk to ordinary maps. -/
@[implicit_reducible] noncomputable def shrinkHom
    [UnivLE.{t, w}] (X Y : Type t) : Type w :=
  Shrink.{w} X → Shrink.{w} Y

/-- Helper for Lemma 7.28.5: shrink-transported maps are function-like. -/
instance shrinkHomFunLike [UnivLE.{t, w}] (X Y : Type t) :
    FunLike (shrinkHom.{t, w} X Y) (Shrink.{w} X) (Shrink.{w} Y) where
  coe f := f
  coe_injective' := by
    intro f g h
    funext x
    exact congrFun h x

/-- Helper for Lemma 7.28.5: unshrinking a map of shrink carriers gives an ordinary function. -/
@[implicit_reducible] noncomputable def shrinkHomToFunction
    [UnivLE.{t, w}] {X Y : Type t} (f : shrinkHom.{t, w} X Y) : X ⟶ Y :=
  fun x => (equivShrink Y).symm (f (equivShrink X x))

/-- Helper for Lemma 7.28.5: shrinking after unshrinking recovers a shrink-carrier map. -/
theorem typeShrinkMap_shrinkHomToFunction
    [UnivLE.{t, w}] {X Y : Type t} (f : shrinkHom.{t, w} X Y) :
    typeShrinkMap (shrinkHomToFunction f) = f := by
  funext x
  simp [typeShrinkMap, shrinkHomToFunction]

/-- Helper for Lemma 7.28.5: unshrinking after shrinking recovers the original function. -/
theorem shrinkHomToFunction_typeShrinkMap
    [UnivLE.{t, w}] {X Y : Type t} (f : X ⟶ Y) :
    shrinkHomToFunction (typeShrinkMap f) = f := by
  funext x
  simp [typeShrinkMap, shrinkHomToFunction]

/-- Helper for Lemma 7.28.5: shrink transport fixes identity maps pointwise. -/
theorem typeShrinkMap_id_apply [UnivLE.{t, w}] {X : Type t}
    (x : Shrink.{w} X) :
    typeShrinkMap (𝟙 X) x = x := by
  simpa using congrFun (typeShrinkMap_id (X := X)) x

/-- Helper for Lemma 7.28.5: shrink transport computes on composites pointwise. -/
theorem typeShrinkMap_comp_apply
    [UnivLE.{t, w}] {X Y Z : Type t} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Shrink.{w} X) :
    typeShrinkMap (f ≫ g) x = typeShrinkMap g (typeShrinkMap f x) := by
  simpa using congrFun (typeShrinkMap_comp (f := f) (g := g)) x

/-- Helper for Lemma 7.28.5: `Type t` is concrete over resized `Shrink` carriers. -/
@[implicit_reducible]
noncomputable def shrinkConcreteCategory [UnivLE.{t, w}] :
    ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) where
  hom f := typeShrinkMap f
  ofHom f := shrinkHomToFunction f
  hom_ofHom f := typeShrinkMap_shrinkHomToFunction f
  ofHom_hom f := shrinkHomToFunction_typeShrinkMap f
  id_apply x := typeShrinkMap_id_apply x
  comp_apply f g x := typeShrinkMap_comp_apply f g x

/-- Helper for Lemma 7.28.5: the shrink-valued forgetful functor for `Type t`. -/
@[implicit_reducible] noncomputable def shrinkForget [UnivLE.{t, w}] :
    Type t ⥤ Type w :=
  letI : ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) := shrinkConcreteCategory
  CategoryTheory.forget (Type t)

/-- Helper for Lemma 7.28.5: the shrink-valued forgetful functor computes by
`typeShrinkMap`. -/
theorem shrinkForget_map_apply [UnivLE.{t, w}] {X Y : Type t}
    (f : X ⟶ Y) (x : Shrink.{w} X) :
    (shrinkForget.{t, w}).map f x = typeShrinkMap f x := by
  -- The concrete `forget` functor is defined through the chosen shrink concrete structure.
  rfl

/-- Helper for Lemma 7.28.5: the shrink-valued forgetful functor reflects isomorphisms. -/
theorem shrinkForget_reflectsIsomorphisms [UnivLE.{t, w}] :
    (shrinkForget.{t, w}).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    -- An isomorphism after applying `shrinkForget` is a bijection between shrink carriers.
    have hfBij : Function.Bijective (typeShrinkMap f : Shrink.{w} X → Shrink.{w} Y) := by
      rw [← isIso_iff_bijective]
      change IsIso ((shrinkForget.{t, w}).map f)
      exact hf
    have hfInj : Function.Injective f := by
      intro x y hxy
      apply (equivShrink X).injective
      exact hfBij.1 (by simpa [typeShrinkMap] using congrArg (equivShrink Y) hxy)
    have hfSurj : Function.Surjective f := by
      intro y
      rcases hfBij.2 (equivShrink Y y) with ⟨sx, hsx⟩
      refine ⟨(equivShrink X).symm sx, ?_⟩
      apply (equivShrink Y).injective
      simpa [typeShrinkMap] using hsx
    -- Type-valued maps are isomorphisms exactly when they are bijections.
    rw [isIso_iff_bijective]
    exact ⟨hfInj, hfSurj⟩

/-- Helper for Lemma 7.28.5: a `Type t` sheaf remains a sheaf after replacing its values by
resized `Shrink` carriers. -/
theorem shrinkForget_isSheaf
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E]
    {L : GrothendieckTopology E} {P : Eᵒᵖ ⥤ Type t}
    (hP : Presheaf.IsSheaf L P) :
    Presheaf.IsSheaf L (P ⋙ shrinkForget.{t, w}) := by
  -- Transport the type-valued sheaf condition along the objectwise equivalence `equivShrink`.
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (e := fun X => equivShrink (P.obj (Opposite.op X))) (he := ?_) ?_
  · intro X Y f x
    change equivShrink (P.obj (Opposite.op X)) (P.map f.op x) =
      (shrinkForget.{t, w}).map (P.map f.op)
        (equivShrink (P.obj (Opposite.op Y)) x)
    rw [shrinkForget_map_apply]
    simp [typeShrinkMap]
  · exact (isSheaf_iff_isSheaf_of_type L P).1 hP

/-- Helper for Lemma 7.28.5: sheaf composition is available for the shrink-valued forgetful
functor. -/
theorem shrinkForget_hasSheafCompose
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose (shrinkForget.{t, w}) where
  isSheaf P hP := by
    -- The owner field is exactly the sheaf-transport lemma above.
    exact shrinkForget_isSheaf (L := L) hP

/-- Helper for Lemma 7.28.5: local injectivity survives whiskering by the resized
shrink-valued forgetful functor. -/
theorem isLocallyInjective_whisker_shrinkForget
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L (Functor.whiskerRight η (shrinkForget.{t, w})) where
  equalizerSieve_mem {X} xs ys hxy := by
    -- Unshrink the equal pair, apply the ordinary local-injectivity cover, then shrink the
    -- resulting equalizer relation back to the whiskered morphism.
    change (shrinkForget.{t, w}).map (η.app X) xs =
      (shrinkForget.{t, w}).map (η.app X) ys at hxy
    rw [shrinkForget_map_apply, shrinkForget_map_apply] at hxy
    let x : P.obj X := (equivShrink (P.obj X)).symm xs
    let y : P.obj X := (equivShrink (P.obj X)).symm ys
    have hxyOrd : η.app X x = η.app X y := by
      apply (equivShrink (Q.obj X)).injective
      simpa only [typeShrinkMap, x, y] using hxy
    let SOrd : Sieve X.unop :=
      { arrows := fun Y f => P.map f.op x = P.map f.op y
        downward_closed := by
          intro Y Z f hf g
          simpa [op_comp] using congrArg (P.map g.op) hf }
    have hSOrd : SOrd ∈ L X.unop := by
      let _ : Presheaf.IsLocallyInjective L η := hη
      simpa [SOrd, Presheaf.equalizerSieve] using
        (Presheaf.equalizerSieve_mem L η x y hxyOrd)
    refine L.superset_covering ?_ hSOrd
    intro Y f hf
    dsimp [SOrd] at hf
    change (shrinkForget.{t, w}).map (P.map f.op) xs =
      (shrinkForget.{t, w}).map (P.map f.op) ys
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change typeShrinkMap (P.map f.op) xs = typeShrinkMap (P.map f.op) ys
    simpa [typeShrinkMap, x, y] using congrArg (equivShrink (P.obj (Opposite.op Y))) hf

/-- Helper for Lemma 7.28.5: local surjectivity survives whiskering by the resized
shrink-valued forgetful functor. -/
theorem isLocallySurjective_whisker_shrinkForget
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallySurjective L η) :
    Presheaf.IsLocallySurjective L (Functor.whiskerRight η (shrinkForget.{t, w})) where
  imageSieve_mem {X} xs := by
    -- Unshrink the target section, use the ordinary local-preimage cover, and shrink the chosen
    -- preimages back to the whiskered image sieve.
    let x : Q.obj (Opposite.op X) := (equivShrink (Q.obj (Opposite.op X))).symm xs
    let SOrd : Sieve X :=
      { arrows := fun Y f => ∃ y : P.obj (Opposite.op Y),
          η.app (Opposite.op Y) y = Q.map f.op x
        downward_closed := by
          intro Y Z f hf g
          rcases hf with ⟨y, hy⟩
          refine ⟨P.map g.op y, ?_⟩
          calc
            η.app (Opposite.op Z) (P.map g.op y)
                = Q.map g.op (η.app (Opposite.op Y) y) :=
                  FunctorToTypes.naturality _ _ η g.op y
            _ = Q.map g.op (Q.map f.op x) := by rw [hy]
            _ = (Q.map f.op ≫ Q.map g.op) x := rfl
            _ = Q.map (f.op ≫ g.op) x := by rw [Q.map_comp]
            _ = Q.map (g ≫ f).op x := by rw [op_comp] }
    have hSOrd : SOrd ∈ L X := by
      let _ : Presheaf.IsLocallySurjective L η := hη
      simpa [SOrd, Presheaf.imageSieve] using
        (Presheaf.imageSieve_mem L η x)
    refine L.superset_covering ?_ hSOrd
    intro Y f hf
    dsimp [SOrd] at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨equivShrink (P.obj (Opposite.op Y)) y, ?_⟩
    change (shrinkForget.{t, w}).map (η.app (Opposite.op Y))
        (equivShrink (P.obj (Opposite.op Y)) y) =
      (shrinkForget.{t, w}).map (Q.map f.op) xs
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change typeShrinkMap (η.app (Opposite.op Y)) (equivShrink (P.obj (Opposite.op Y)) y) =
      typeShrinkMap (Q.map f.op) xs
    simpa [typeShrinkMap, x] using
      congrArg (equivShrink (Q.obj (Opposite.op Y))) hy

/-- Helper for Lemma 7.28.5: once `W` is local bijectivity in the source and shrink target
universes, the shrink-valued forgetful functor preserves sheafification. -/
theorem shrinkForget_preservesSheafification_of_WEqualsLocallyBijective
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [HasWeakSheafify L (Type w)]
    [L.WEqualsLocallyBijective (Type t)] [L.WEqualsLocallyBijective (Type w)] :
    L.PreservesSheafification (shrinkForget.{t, w}) where
  le P Q η hη := by
    -- Convert the source `W`-hypothesis to local bijectivity and transport both halves through
    -- the shrink-valued forgetful functor.
    let hBij := (L.W_iff_isLocallyBijective η).1 hη
    let _ : Presheaf.IsLocallyInjective L
        (Functor.whiskerRight η (shrinkForget.{t, w})) :=
      isLocallyInjective_whisker_shrinkForget (L := L) η hBij.1
    let _ : Presheaf.IsLocallySurjective L
        (Functor.whiskerRight η (shrinkForget.{t, w})) :=
      isLocallySurjective_whisker_shrinkForget (L := L) η hBij.2
    -- The target `W =` local-bijectivity instance turns the transported local data back into a
    -- `W`-morphism, which is exactly preservation of sheafification.
    exact
      GrothendieckTopology.W_of_isLocallyBijective
        (J := L) (f := Functor.whiskerRight η (shrinkForget.{t, w}))

/-- Helper for Lemma 7.28.5: local injectivity computed on resized carriers reflects to the
ordinary type-valued concrete structure. -/
theorem locallyInjective_of_shrink
    [UnivLE.{t, w}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    (hη :
      letI : ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) := shrinkConcreteCategory
      Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y hxy := by
    let xs : Shrink.{w} (P.obj X) := equivShrink (P.obj X) x
    let ys : Shrink.{w} (P.obj X) := equivShrink (P.obj X) y
    have hxyShrink : typeShrinkMap (η.app X) xs = typeShrinkMap (η.app X) ys := by
      simpa [typeShrinkMap, xs, ys] using hxy
    letI : ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) := shrinkConcreteCategory
    have hS : Presheaf.equalizerSieve (F := P) xs ys ∈ L X.unop :=
      Presheaf.equalizerSieve_mem L η xs ys hxyShrink
    -- Unshrink the local equalizer relation back to the ordinary carrier.
    refine L.superset_covering ?_ hS
    intro Y f hf
    change typeShrinkMap (P.map f.op) xs = typeShrinkMap (P.map f.op) ys at hf
    change P.map f.op x = P.map f.op y
    apply (equivShrink (P.obj (Opposite.op Y))).injective
    simpa [typeShrinkMap, xs, ys] using hf

/-- Helper for Lemma 7.28.5: if `W` already agrees with local bijectivity in `Type t`, then the
abstract sheafification unit is locally injective. -/
theorem toSheafify_isLocallyInjective_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [L.WEqualsLocallyBijective (Type t)]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  -- The sheafification unit is always a `W`-morphism, and the local-bijective package reads its
  -- injective half as the desired equalizer-sieve condition.
  exact (L.W_toSheafify P).isLocallyInjective

/-- Helper for Lemma 7.28.5: equality after the sheafification unit is the same as equality after
every map from the presheaf into a type-valued sheaf. -/
theorem toSheafify_app_eq_iff_forall_sheaf_maps_eq
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] {P : Eᵒᵖ ⥤ Type t} {X : Eᵒᵖ}
    (x y : P.obj X) :
    (toSheafify L P).app X x = (toSheafify L P).app X y ↔
      ∀ (Q : Eᵒᵖ ⥤ Type t), Presheaf.IsSheaf L Q →
        ∀ f : P ⟶ Q, f.app X x = f.app X y := by
  constructor
  · intro h Q hQ f
    have hf : toSheafify L P ≫ sheafifyLift L f hQ = f :=
      toSheafify_sheafifyLift (J := L) f hQ
    have hmap :
        (sheafifyLift L f hQ).app X ((toSheafify L P).app X x) =
          (sheafifyLift L f hQ).app X ((toSheafify L P).app X y) :=
      congrArg ((sheafifyLift L f hQ).app X) h
    -- Factor the map to a sheaf through the reflector unit and transport the unit equality.
    have hcomp :
        (toSheafify L P ≫ sheafifyLift L f hQ).app X x =
          (toSheafify L P ≫ sheafifyLift L f hQ).app X y := by
      change
        (sheafifyLift L f hQ).app X ((toSheafify L P).app X x) =
          (sheafifyLift L f hQ).app X ((toSheafify L P).app X y)
      exact hmap
    simpa [hf] using hcomp
  · intro h
    -- Testing against the sheafification target recovers the original unit equality.
    exact h (sheafify L P) (((presheafToSheaf L (Type t)).obj P).property) (toSheafify L P)

end CategoryTheory
