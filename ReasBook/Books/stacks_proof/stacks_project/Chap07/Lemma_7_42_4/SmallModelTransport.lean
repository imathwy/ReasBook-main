import StacksProject_2024.Chap07.Lemma_7_42_4.TypeLocalBijectivity

open CategoryTheory Opposite CategoryTheory.GrothendieckTopology.Plus

universe u₁ u₂ u₃ v₁ v₂ v₃ w r

namespace CategoryTheory.Functor

/-- Helper for Lemma 7.42.4: in the complementary universe branch `UnivLE.{w, max u₃ v₃}`, the
canonical small-model transport theorem would recover `W =` local bijectivity on `Type w` once
the two remaining owner-level instances are available. -/
theorem small_type_WEqualsLocallyBijective_of_small_model_transport
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : Eᵒᵖ,
      Limits.HasLimitsOfShape
        (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op) (Type w)]
    [GrothendieckTopology.WEqualsLocallyBijective
      ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L) (Type w)] :
    L.WEqualsLocallyBijective (Type w) := by
  let _ : CategoryTheory.EssentiallySmall.{max u₃ v₃} E :=
    CategoryTheory.essentiallySmallSelf (C := E)
  -- Transport `W =` local bijectivity back from the canonical `max u₃ v₃`-small model.
  simpa using
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (J := L) (A := Type w) :
        L.WEqualsLocallyBijective (Type w))

/-- Helper for Lemma 7.42.4: if `G.op` is right adjoint, then every structured-arrow category on
`G.op` has an initial object, so `Type w`-valued diagrams on it admit limits. -/
theorem right_adjoint_op_structuredArrow_hasLimits_type
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : A ⥤ B) [G.op.IsRightAdjoint] (X : Bᵒᵖ) :
    Limits.HasLimitsOfShape (StructuredArrow X G.op) (Type w) := by
  -- A right adjoint gives the source proof's canonical initial object in each structured-arrow
  -- category.
  let _ : Limits.HasInitial (StructuredArrow X G.op) := by
    exact (CategoryTheory.mkInitialOfLeftAdjoint G.op
      (Adjunction.ofIsRightAdjoint G.op) X).hasInitial
  -- Any diagram indexed by a category with an initial object has a limit.
  exact ⟨fun F ↦ by infer_instance⟩

/-- Helper for Lemma 7.42.4: the inverse side of the canonical small-model equivalence satisfies
the structured-arrow limit owner needed by `WEqualsLocallyBijective.ofEssentiallySmall`. -/
theorem small_model_structuredArrow_hasLimits_type
    {E : Type u₃} [Category.{v₃} E] (X : Eᵒᵖ) :
    Limits.HasLimitsOfShape
      (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op) (Type w) := by
  -- The inverse of an equivalence remains a right adjoint after taking opposites.
  exact right_adjoint_op_structuredArrow_hasLimits_type
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse) X

/-- Helper for Lemma 7.42.4: weak sheafification on `Type w` transports from the original site to
the induced topology on the canonical small model. -/
theorem small_model_inducedTopology_hasWeakSheafify_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] :
    HasWeakSheafify
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  let e := CategoryTheory.equivSmallModel.{max u₃ v₃} E
  let _ : ∀ X : (SmallModel.{max u₃ v₃, v₃, u₃} E)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X e.functor.op) (Type w) := by
    intro X
    -- The forward equivalence functor is also right adjoint after taking opposites.
    exact right_adjoint_op_structuredArrow_hasLimits_type e.functor X
  let _ :
      (e.functor.sheafPushforwardContinuous (Type w) L (e.inverse.inducedTopology L)).IsEquivalence := by
    infer_instance
  -- Transport weak sheafification across the dense-subsite equivalence to the induced topology.
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    L (e.inverse.inducedTopology L) e.functor (Type w)

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, composing
`Type w`-valued sheaves with the identity functor still preserves the sheaf condition. -/
theorem small_model_inducedTopology_hasSheafCompose_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L).HasSheafCompose
      (𝟭 (Type w)) := by
  -- The identity-on-types functor has the same sheaf-composition owner on every site.
  exact inferInstance

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, the identity
functor on `Type w` preserves sheafification tautologically. -/
theorem small_model_inducedTopology_preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    GrothendieckTopology.PreservesSheafification
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (𝟭 (Type w)) := by
  -- The source and target weak-sheafification units are unchanged under the identity functor.
  exact preservesSheafification_id_type
    (L := (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)

/-- Helper for Lemma 7.42.4: under a universe inequality `UnivLE.{w, r}`, a function between
`Type w` objects transports to their `Shrink` models in `Type r`. -/
@[implicit_reducible] noncomputable def type_shrink_map
    [UnivLE.{w, r}] {X Y : Type w} (f : X ⟶ Y) :
    Shrink.{r} X → Shrink.{r} Y :=
  fun x => equivShrink Y (f ((equivShrink X).symm x))

/-- Helper for Lemma 7.42.4: `type_shrink_map` respects identities. -/
theorem type_shrink_map_id
    [UnivLE.{w, r}] (X : Type w) :
    type_shrink_map (𝟙 X) = id := by
  -- The shrink/unshrink transport cancels on identity maps.
  funext x
  change equivShrink X ((𝟙 X) ((equivShrink X).symm x)) = x
  simp

/-- Helper for Lemma 7.42.4: `type_shrink_map` respects composition. -/
theorem type_shrink_map_comp
    [UnivLE.{w, r}] {X Y Z : Type w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    type_shrink_map (f ≫ g) = type_shrink_map g ∘ type_shrink_map f := by
  -- The shrink transport is functorial because `equivShrink` is an equivalence on each object.
  funext x
  change equivShrink Z (g (f ((equivShrink X).symm x))) =
    equivShrink Z (g ((equivShrink Y).symm (equivShrink Y (f ((equivShrink X).symm x)))))
  simp

/-- Helper for Lemma 7.42.4: transporting functions to shrink models is injective on morphisms. -/
theorem type_shrink_map_injective
    [UnivLE.{w, r}] {X Y : Type w} :
    Function.Injective
      (fun f : X ⟶ Y => (type_shrink_map f : Shrink.{r} X → Shrink.{r} Y)) := by
  -- Evaluate the transported maps on the shrink image of each original point.
  intro f g h
  funext x
  have hx := congrFun h (equivShrink X x)
  simpa [type_shrink_map] using hx

/-- Helper for Lemma 7.42.4: bundled morphisms between resized `Shrink` carriers for
`Type w`. -/
@[implicit_reducible] noncomputable def shrinkHom
    [UnivLE.{w, r}] (X Y : Type w) : Type r :=
  Shrink.{r} X → Shrink.{r} Y

/-- Helper for Lemma 7.42.4: `shrinkHom` is a function-like bundled morphism type. -/
instance shrinkHomFunLike [UnivLE.{w, r}] (X Y : Type w) :
    FunLike (shrinkHom.{w, r} X Y) (Shrink.{r} X) (Shrink.{r} Y) where
  coe f := f
  coe_injective' := by
    intro f g h
    funext x
    exact congrFun h x

/-- Helper for Lemma 7.42.4: unshrink a bundled map of shrink carriers back to a function. -/
@[implicit_reducible] noncomputable def shrinkHomToFunction
    [UnivLE.{w, r}] {X Y : Type w} (f : shrinkHom.{w, r} X Y) : X ⟶ Y :=
  fun x => (equivShrink Y).symm (f (equivShrink X x))

/-- Helper for Lemma 7.42.4: shrink transport followed by unshrinking a bundled map is the
original bundled map. -/
theorem type_shrink_map_shrinkHomToFunction
    [UnivLE.{w, r}] {X Y : Type w} (f : shrinkHom.{w, r} X Y) :
    type_shrink_map (shrinkHomToFunction f) = f := by
  -- The shrink/unshrink equivalence cancels after transporting a bundled shrink map.
  funext x
  simp [type_shrink_map, shrinkHomToFunction]

/-- Helper for Lemma 7.42.4: unshrinking the shrink transport of a function gives the original
function. -/
theorem shrinkHomToFunction_type_shrink_map
    [UnivLE.{w, r}] {X Y : Type w} (f : X ⟶ Y) :
    shrinkHomToFunction (type_shrink_map f) = f := by
  -- Evaluating on original points turns the shrink transport into the original function.
  funext x
  simp [type_shrink_map, shrinkHomToFunction]

/-- Helper for Lemma 7.42.4: the shrink transport of an identity fixes every shrink point. -/
theorem type_shrink_map_id_apply [UnivLE.{w, r}] {X : Type w}
    (x : Shrink.{r} X) :
    type_shrink_map (𝟙 X) x = x := by
  -- Identities are transported by the previously named shrink computation lemma.
  simpa using congrFun (type_shrink_map_id (X := X)) x

/-- Helper for Lemma 7.42.4: the shrink transport of a composite acts pointwise as a composite. -/
theorem type_shrink_map_comp_apply
    [UnivLE.{w, r}] {X Y Z : Type w} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Shrink.{r} X) :
    type_shrink_map (f ≫ g) x = type_shrink_map g (type_shrink_map f x) := by
  -- Composition is transported by the corresponding shrink computation lemma.
  simpa using congrFun (type_shrink_map_comp (f := f) (g := g)) x

/-- Helper for Lemma 7.42.4: `Type w` is concrete over resized `Shrink` carriers. -/
@[implicit_reducible]
noncomputable def shrinkConcreteCategory [UnivLE.{w, r}] :
    ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) where
  hom f := type_shrink_map f
  ofHom f := shrinkHomToFunction f
  hom_ofHom f := type_shrink_map_shrinkHomToFunction f
  ofHom_hom f := shrinkHomToFunction_type_shrink_map f
  id_apply x := type_shrink_map_id_apply x
  comp_apply f g x := type_shrink_map_comp_apply f g x

/-- Helper for Lemma 7.42.4: the shrink-valued forgetful functor for `Type w`. -/
@[implicit_reducible] noncomputable def shrinkForget [UnivLE.{w, r}] :
    Type w ⥤ Type r :=
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  CategoryTheory.forget (Type w)

/-- Helper for Lemma 7.42.4: the shrink forgetful functor computes by
`type_shrink_map`. -/
theorem shrinkForget_map_apply [UnivLE.{w, r}] {X Y : Type w}
    (f : X ⟶ Y) (x : Shrink.{r} X) :
    (shrinkForget.{w, r}).map f x = type_shrink_map f x := by
  -- The concrete `forget` functor is defined through `ConcreteCategory.hom`.
  rfl

/-- Helper for Lemma 7.42.4: the shrink-valued forgetful functor reflects isomorphisms. -/
theorem shrink_forget_reflectsIsomorphisms [UnivLE.{w, r}] :
    (shrinkForget.{w, r}).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    -- A shrink-transported isomorphism is a bijection of shrink carriers, and the objectwise
    -- equivalences `equivShrink` transfer that bijection back to the original function.
    rw [CategoryTheory.isIso_iff_bijective]
    have hfBij : Function.Bijective (type_shrink_map f : Shrink.{r} X → Shrink.{r} Y) := by
      rw [← CategoryTheory.isIso_iff_bijective]
      simpa [shrinkForget_map_apply] using hf
    constructor
    · intro x y hxy
      apply (equivShrink X).injective
      apply hfBij.1
      simpa [type_shrink_map] using congrArg (equivShrink Y) hxy
    · intro y
      obtain ⟨sx, hsx⟩ := hfBij.2 (equivShrink Y y)
      refine ⟨(equivShrink X).symm sx, ?_⟩
      apply (equivShrink Y).injective
      simpa [type_shrink_map] using hsx

/-- Helper for Lemma 7.42.4: the shrink concrete-category forgetful functor preserves sheaves. -/
theorem shrink_forget_isSheaf
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E]
    {L : GrothendieckTopology E} {P : Eᵒᵖ ⥤ Type w}
    (hP : Presheaf.IsSheaf L P) :
    Presheaf.IsSheaf L (P ⋙ shrinkForget.{w, r}) := by
  -- Convert the arbitrary-category sheaf predicate to the type-valued one, then transport it
  -- across the objectwise equivalence `equivShrink`.
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (e := fun X => equivShrink (P.obj (op X))) (he := ?_) ?_
  · intro X Y f x
    -- The objectwise equivalence is natural because the shrink forgetful map is
    -- `type_shrink_map`.
    change equivShrink (P.obj (op X)) (P.map f.op x) =
      (shrinkForget.{w, r}).map (P.map f.op) (equivShrink (P.obj (op Y)) x)
    rw [shrinkForget_map_apply]
    simp [type_shrink_map]
  · exact (isSheaf_iff_isSheaf_of_type L P).1 hP

/-- Helper for Lemma 7.42.4: sheaves remain sheaves after the shrink forgetful functor. -/
theorem shrink_forget_hasSheafCompose
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose (shrinkForget.{w, r}) where
  isSheaf P hP := by
    -- This is the packaged owner used by the local-bijectivity criterion.
    exact shrink_forget_isSheaf (L := L) hP

/-- Helper for Lemma 7.42.4: local injectivity for ordinary `Type w` sections remains local
injectivity after replacing carriers by their resized `Shrink` models. -/
theorem isLocallyInjective_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallyInjective L η) :
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    Presheaf.IsLocallyInjective L η := by
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  refine ⟨fun {X} xs ys hxy => ?_⟩
  -- Unshrink the two sections, apply ordinary local injectivity, then shrink the resulting
  -- equalizer condition back to the resized carrier.
  change type_shrink_map (η.app X) xs = type_shrink_map (η.app X) ys at hxy
  let x : P.obj X := (equivShrink (P.obj X)).symm xs
  let y : P.obj X := (equivShrink (P.obj X)).symm ys
  have hxyOrd : η.app X x = η.app X y := by
    apply (equivShrink (Q.obj X)).injective
    simpa [type_shrink_map, x, y] using hxy
  let SOrd : Sieve X.unop :=
    { arrows := fun Y f => P.map f.op x = P.map f.op y
      downward_closed := by
        intro Y Z f hf g
        simpa [op_comp] using congrArg (P.map g.op) hf }
  have hSOrd : SOrd ∈ L X.unop := by
    letI : ConcreteCategory (Type w) (fun X Y : Type w => X ⟶ Y) := Types.instConcreteCategory
    let _ : Presheaf.IsLocallyInjective L η := hη
    simpa [SOrd, Presheaf.equalizerSieve] using
      (Presheaf.equalizerSieve_mem L η x y hxyOrd)
  refine L.superset_covering ?_ hSOrd
  intro Y f hf
  dsimp [SOrd] at hf
  change type_shrink_map (P.map f.op) xs = type_shrink_map (P.map f.op) ys
  simpa [type_shrink_map, x, y] using congrArg (equivShrink (P.obj (op Y))) hf

/-- Helper for Lemma 7.42.4: local surjectivity for ordinary `Type w` sections remains local
surjectivity after replacing carriers by their resized `Shrink` models. -/
theorem isLocallySurjective_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallySurjective L η) :
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    Presheaf.IsLocallySurjective L η := by
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  refine ⟨fun {X} xs => ?_⟩
  -- Unshrink the target section, use the ordinary local preimage, and shrink the resulting
  -- local section back to the resized carrier.
  let x : Q.obj (op X) := (equivShrink (Q.obj (op X))).symm xs
  let SOrd : Sieve X :=
    { arrows := fun Y f => ∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x
      downward_closed := by
        intro Y Z f hf g
        rcases hf with ⟨y, hy⟩
        refine ⟨P.map g.op y, ?_⟩
        calc
          η.app (op Z) (P.map g.op y)
              = Q.map g.op (η.app (op Y) y) := FunctorToTypes.naturality _ _ η g.op y
          _ = Q.map g.op (Q.map f.op x) := by rw [hy]
          _ = (Q.map f.op ≫ Q.map g.op) x := rfl
          _ = Q.map (f.op ≫ g.op) x := by rw [Q.map_comp]
          _ = Q.map (g ≫ f).op x := by rw [op_comp] }
  have hSOrd : SOrd ∈ L X := by
    letI : ConcreteCategory (Type w) (fun X Y : Type w => X ⟶ Y) := Types.instConcreteCategory
    let _ : Presheaf.IsLocallySurjective L η := hη
    simpa [SOrd, Presheaf.imageSieve] using
      (Presheaf.imageSieve_mem L η x)
  refine L.superset_covering ?_ hSOrd
  intro Y f hf
  dsimp [SOrd] at hf
  rcases hf with ⟨y, hy⟩
  refine ⟨equivShrink (P.obj (op Y)) y, ?_⟩
  change type_shrink_map (η.app (op Y)) (equivShrink (P.obj (op Y)) y) =
    type_shrink_map (Q.map f.op) xs
  simpa [type_shrink_map, x] using congrArg (equivShrink (Q.obj (op Y))) hy

/-- Helper for Lemma 7.42.4: local injectivity computed on resized `Shrink` carriers reflects
to the ordinary concrete structure on `Type w`. -/
theorem locallyInjective_of_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη :
      letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
      Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y hxy := by
    let xs : Shrink.{r} (P.obj X) := equivShrink (P.obj X) x
    let ys : Shrink.{r} (P.obj X) := equivShrink (P.obj X) y
    have hxyShrink : type_shrink_map (η.app X) xs = type_shrink_map (η.app X) ys := by
      -- Transfer the equality of ordinary images to equality after shrinking the target.
      simpa [type_shrink_map, xs, ys] using hxy
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    have hS : Presheaf.equalizerSieve (F := P) xs ys ∈ L X.unop :=
      Presheaf.equalizerSieve_mem L η xs ys hxyShrink
    -- Any arrow that equalizes the shrink sections equalizes the original sections.
    refine L.superset_covering ?_ hS
    intro Y f hf
    change type_shrink_map (P.map f.op) xs = type_shrink_map (P.map f.op) ys at hf
    change P.map f.op x = P.map f.op y
    apply (equivShrink (P.obj (op Y))).injective
    simpa [type_shrink_map, xs, ys] using hf

/-- Helper for Lemma 7.42.4: local surjectivity computed on resized `Shrink` carriers reflects
to the ordinary concrete structure on `Type w`. -/
theorem locallySurjective_of_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη :
      letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
      Presheaf.IsLocallySurjective L η) :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    let xs : Shrink.{r} (Q.obj (op X)) := equivShrink (Q.obj (op X)) x
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    have hS : Presheaf.imageSieve η xs ∈ L X :=
      Presheaf.imageSieve_mem L η xs
    -- A shrink-local preimage unshrinks to an ordinary local preimage.
    refine L.superset_covering ?_ hS
    intro Y f hf
    rcases hf with ⟨y, hy⟩
    refine ⟨(equivShrink (P.obj (op Y))).symm y, ?_⟩
    -- Descend the shrink equality to the ordinary carrier.
    have hyShrink :
        type_shrink_map (η.app (op Y)) y = type_shrink_map (Q.map f.op) xs := by
      simpa only using hy
    have hyOrd :
        (equivShrink (Q.obj (op Y))).symm (type_shrink_map (η.app (op Y)) y) =
          (equivShrink (Q.obj (op Y))).symm (type_shrink_map (Q.map f.op) xs) := by
      exact
        congrArg
          (fun z : Shrink.{r} (Q.obj (op Y)) => (equivShrink (Q.obj (op Y))).symm z)
          hyShrink
    simpa [type_shrink_map, xs] using hyOrd

/-- Helper for Lemma 7.42.4: local injectivity survives whiskering by the resized shrink-valued
forgetful functor. -/
theorem isLocallyInjective_whisker_shrinkForget
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L (Functor.whiskerRight η (shrinkForget.{w, r})) where
  equalizerSieve_mem {X} xs ys hxy := by
    -- Translate equality after the shrink-valued map back to equality of ordinary sections.
    change (shrinkForget.{w, r}).map (η.app X) xs =
      (shrinkForget.{w, r}).map (η.app X) ys at hxy
    rw [shrinkForget_map_apply, shrinkForget_map_apply] at hxy
    let x : P.obj X := (equivShrink.{r, w} (P.obj X)).symm xs
    let y : P.obj X := (equivShrink.{r, w} (P.obj X)).symm ys
    have hxyShrink :
        equivShrink.{r, w} (Q.obj X) (η.app X x) =
          equivShrink.{r, w} (Q.obj X) (η.app X y) := by
      simpa only [type_shrink_map, x, y] using hxy
    have hxyOrd : η.app X x = η.app X y := by
      exact (Equiv.apply_eq_iff_eq (equivShrink.{r, w} (Q.obj X))).1 hxyShrink
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
    -- Shrink the ordinary local equalizer relation back to the whiskered equalizer sieve.
    change (shrinkForget.{w, r}).map (P.map f.op) xs =
      (shrinkForget.{w, r}).map (P.map f.op) ys
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change type_shrink_map (P.map f.op) xs = type_shrink_map (P.map f.op) ys
    simpa [type_shrink_map, x, y] using
      congrArg (equivShrink.{r, w} (P.obj (op Y))) hf

/-- Helper for Lemma 7.42.4: local surjectivity survives whiskering by the resized shrink-valued
forgetful functor. -/
theorem isLocallySurjective_whisker_shrinkForget
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallySurjective L η) :
    Presheaf.IsLocallySurjective L (Functor.whiskerRight η (shrinkForget.{w, r})) where
  imageSieve_mem {X} xs := by
    -- Unshrink the target section and use ordinary local surjectivity to obtain local preimages.
    let x : Q.obj (op X) := (equivShrink.{r, w} (Q.obj (op X))).symm xs
    let SOrd : Sieve X :=
      { arrows := fun Y f => ∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x
        downward_closed := by
          intro Y Z f hf g
          rcases hf with ⟨y, hy⟩
          refine ⟨P.map g.op y, ?_⟩
          calc
            η.app (op Z) (P.map g.op y)
                = Q.map g.op (η.app (op Y) y) := FunctorToTypes.naturality _ _ η g.op y
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
    refine ⟨equivShrink.{r, w} (P.obj (op Y)) y, ?_⟩
    -- Shrink the chosen ordinary preimage and verify the whiskered image equation.
    change (shrinkForget.{w, r}).map (η.app (op Y))
        (equivShrink.{r, w} (P.obj (op Y)) y) =
      (shrinkForget.{w, r}).map (Q.map f.op) xs
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change type_shrink_map (η.app (op Y)) (equivShrink.{r, w} (P.obj (op Y)) y) =
      type_shrink_map (Q.map f.op) xs
    simpa [type_shrink_map, x] using
      congrArg (equivShrink.{r, w} (Q.obj (op Y))) hy

/-- Helper for Lemma 7.42.4: once `W` is local bijectivity in the source and shrink target
universes, the shrink-valued forgetful functor preserves sheafification. -/
theorem shrink_forget_preservesSheafification_of_WEqualsLocallyBijective
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [HasWeakSheafify L (Type r)]
    [L.WEqualsLocallyBijective (Type w)] [L.WEqualsLocallyBijective (Type r)] :
    L.PreservesSheafification (shrinkForget.{w, r}) where
  le P Q η hη := by
    -- Convert the source `W`-hypothesis to local bijectivity and transport both halves.
    let hBij := (L.W_iff_isLocallyBijective η).1 hη
    let _ : Presheaf.IsLocallyInjective L
        (Functor.whiskerRight η (shrinkForget.{w, r})) :=
      isLocallyInjective_whisker_shrinkForget (L := L) η hBij.1
    let _ : Presheaf.IsLocallySurjective L
        (Functor.whiskerRight η (shrinkForget.{w, r})) :=
      isLocallySurjective_whisker_shrinkForget (L := L) η hBij.2
    -- The target `W =` local-bijectivity instance turns the transported local data into `W`.
    exact
      GrothendieckTopology.W_of_isLocallyBijective
        (J := L) (f := Functor.whiskerRight η (shrinkForget.{w, r}))

/-- Helper for Lemma 7.42.4: the ordinary forgetful functor from `Type w` still reflects
isomorphisms on the induced topology site. -/
theorem small_model_inducedTopology_forget_reflectsIsomorphisms_type
    {E : Type u₃} [Category.{v₃} E] :
    (CategoryTheory.forget (Type w)).ReflectsIsomorphisms := by
  -- This is the standard `Type`-valued reflection of isomorphisms.
  infer_instance

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, the generic
concrete-category criterion upgrades weak sheafification to `W =` local bijectivity as soon as a
resized concrete-category forgetful functor on `Type w` is available and preserves sheafification.
-/
theorem small_model_inducedTopology_WEqualsLocallyBijective_type_of_resized_forget
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {FD : Type w → Type w → Type*} {CD : Type w → Type (max u₃ v₃)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{max u₃ v₃} (Type w) FD]
    [HasWeakSheafify (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (Type w)]
    [(((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)).HasSheafCompose
      (forget (Type w))]
    [GrothendieckTopology.PreservesSheafification
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (forget (Type w))]
    [(CategoryTheory.forget (Type w)).ReflectsIsomorphisms] :
    GrothendieckTopology.WEqualsLocallyBijective
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  -- The induced topology is now in the exact situation of the standard `Type`-valued criterion.
  infer_instance

/-- Helper for Lemma 7.42.4: the abstract `Type w` sheafification unit is locally injective once
the corresponding `W =` local-bijectivity owner is available.  The complementary
`UnivLE.{w, r}` branch supplies resized carriers, but does not by itself provide the concrete
plus-plus owner instances for `Type w`. -/
theorem toSheafify_isLocallyInjective_shrinkConcrete
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  exact (L.W_toSheafify P).isLocallyInjective

/-- Helper for Lemma 7.42.4: the induced topology on the canonical small model has
`W =` local bijectivity for `Type w` in the complementary universe branch once the injective
half of the sheafification-unit owner is supplied. -/
theorem small_model_inducedTopology_WEqualsLocallyBijective_type_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [UnivLE.{w, max u₃ v₃}]
    (hInj :
      ∀ [HasWeakSheafify
          (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
          (Type w)]
        (P : (SmallModel.{max u₃ v₃, v₃, u₃} E)ᵒᵖ ⥤ Type w),
        Presheaf.IsLocallyInjective
          (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
          (toSheafify
            (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) P)) :
    GrothendieckTopology.WEqualsLocallyBijective
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  let J :=
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)
  let _ : HasWeakSheafify J (Type w) :=
    small_model_inducedTopology_hasWeakSheafify_type (L := L)
  -- It suffices to show the sheafification unit is locally bijective.  Local injectivity is the
  -- remaining owner supplied by the caller; local surjectivity follows from the sheafified-image
  -- argument for type-valued weak sheafification.
  refine small_type_WEqualsLocallyBijective_of_unit_local_bijectivity (L := J) ?_ ?_
  · intro P
    exact hInj P
  · intro P
    exact toSheafify_isLocallySurjective_type_of_hasWeakSheafify (L := J) P

end CategoryTheory.Functor
