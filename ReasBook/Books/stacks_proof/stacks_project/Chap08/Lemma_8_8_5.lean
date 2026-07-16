import stacks_proof.stacks_project.Chap08.Lemma_8_8_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] uliftCategory

/-- Helper for Chap08 Lemma 8 8 5: based functors are equal when their underlying functors
are equal. -/
private theorem basedFunctor_eq_of_toFunctor_eq
    {X : BasedCategory C} {Y : BasedCategory C}
    {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  -- The compatibility with the base is proof data, so equality reduces to the underlying functor.
  cases F
  cases G
  simpa [BasedFunctor.mk.injEq] using h

/-- Helper for Chap08 Lemma 8 8 5: equality isomorphisms of based functors have object
components given by equality morphisms of the corresponding object equalities. -/
private theorem basedFunctor_eqToIso_hom_app
    {X : BasedCategory C} {Y : BasedCategory C}
    {F G : X ⥤ᵇ Y} (h : F = G) (x : X.obj) :
    ((eqToIso h).hom.app x) =
      eqToHom (congrArg (fun H : X ⥤ᵇ Y ↦ H.toFunctor.obj x) h) := by
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 8 5: inverse equality isomorphisms of based functors have object
components given by equality morphisms of the reversed object equalities. -/
private theorem basedFunctor_eqToIso_inv_app
    {X : BasedCategory C} {Y : BasedCategory C}
    {F G : X ⥤ᵇ Y} (h : F = G) (x : X.obj) :
    ((eqToIso h).inv.app x) =
      eqToHom (congrArg (fun H : X ⥤ᵇ Y ↦ H.toFunctor.obj x) h.symm) := by
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 8 5: fibred morphisms are equal when their underlying ordinary
functors are equal. -/
private theorem fibredCategoryMor_eq_of_toFunctor_eq
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    {F G : FibredCategoryMor X Y}
    (h : FibredCategoryMor.toFunctor F = FibredCategoryMor.toFunctor G) :
    F = G := by
  -- Peel off the fibred and based wrappers; only the ordinary functor field remains.
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  exact basedFunctor_eq_of_toFunctor_eq h

/-- Helper for Chap08 Lemma 8 8 5: converting a based-functor isomorphism to a fibred owner
isomorphism and back preserves the forward based natural transformation. -/
private theorem basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_hom
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    {F G : FibredCategoryMor X Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso
      (FibredCategoryMor.ownerIsoOfBasedFunctorIso e)).hom = e.hom := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: converting a based-functor isomorphism to a fibred owner
isomorphism and back preserves the inverse based natural transformation. -/
private theorem basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_inv
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    {F G : FibredCategoryMor X Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso
      (FibredCategoryMor.ownerIsoOfBasedFunctorIso e)).inv = e.inv := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: equality morphisms in an explicit two-fibre product have
the expected component equality morphisms. -/
private theorem explicitTwoFibreProduct_eqToHom_components
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : ExplicitTwoFibreProductObject F G} (h : P = Q) :
    ((eqToHom h : P ⟶ Q).a =
        eqToHom (congrArg (fun R : ExplicitTwoFibreProductObject F G ↦ R.obj.fst.1) h)) ∧
      ((eqToHom h : P ⟶ Q).b =
        eqToHom (congrArg (fun R : ExplicitTwoFibreProductObject F G ↦ R.obj.snd.1) h)) := by
  -- Equality morphisms in the explicit pullback category are componentwise equality morphisms.
  cases h
  constructor
  · rfl
  · rfl

/-- Helper for Chap08 Lemma 8 8 5: the left component of a composite in an explicit
two-fibre product is the composite of the left components. -/
private theorem explicitTwoFibreProductHom_comp_a
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).a = φ.a ≫ ψ.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the right component of a composite in an explicit
two-fibre product is the composite of the right components. -/
private theorem explicitTwoFibreProductHom_comp_b
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).b = φ.b ≫ ψ.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the left component of a triple composite in an explicit
two-fibre product is the triple composite of the left components. -/
private theorem explicitTwoFibreProductHom_comp_comp_a
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q R T : ExplicitTwoFibreProductObject F G}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) (χ : R ⟶ T) :
    (φ ≫ ψ ≫ χ).a = φ.a ≫ ψ.a ≫ χ.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the right component of a triple composite in an explicit
two-fibre product is the triple composite of the right components. -/
private theorem explicitTwoFibreProductHom_comp_comp_b
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q R T : ExplicitTwoFibreProductObject F G}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) (χ : R ⟶ T) :
    (φ ≫ ψ ≫ χ).b = φ.b ≫ ψ.b ≫ χ.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: transporting a morphism between equal explicit
two-fibre-product objects transports its left component by the induced endpoint equalities. -/
private theorem explicitTwoFibreProductHom_transport_a
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q P' Q' : ExplicitTwoFibreProductObject F G}
    (hP : P = P') (hQ : Q = Q') (φ : P' ⟶ Q') :
    (eqToHom hP ≫ φ ≫ eqToHom hQ.symm).a =
      eqToHom (congrArg (fun R ↦ R.obj.fst.1) hP) ≫ φ.a ≫
        eqToHom (congrArg (fun R ↦ R.obj.fst.1) hQ.symm) := by
  cases hP
  cases hQ
  rfl

/-- Helper for Chap08 Lemma 8 8 5: transporting a morphism between equal explicit
two-fibre-product objects transports its right component by the induced endpoint equalities. -/
private theorem explicitTwoFibreProductHom_transport_b
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q P' Q' : ExplicitTwoFibreProductObject F G}
    (hP : P = P') (hQ : Q = Q') (φ : P' ⟶ Q') :
    (eqToHom hP ≫ φ ≫ eqToHom hQ.symm).b =
      eqToHom (congrArg (fun R ↦ R.obj.snd.1) hP) ≫ φ.b ≫
        eqToHom (congrArg (fun R ↦ R.obj.snd.1) hQ.symm) := by
  cases hP
  cases hQ
  rfl

/-- Helper for Chap08 Lemma 8 8 5: two morphisms in equal explicit two-fibre-product Hom
types are heterogeneously equal when their endpoint components are. -/
private theorem explicitTwoFibreProductHom_heq_of_components
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q P' Q' : ExplicitTwoFibreProductObject F G}
    (hP : P = P') (hQ : Q = Q')
    (φ : P ⟶ Q) (ψ : P' ⟶ Q')
    (ha : φ.a ≍ ψ.a) (hb : φ.b ≍ ψ.b) :
    φ ≍ ψ := by
  cases hP
  cases hQ
  exact heq_of_eq (ExplicitTwoFibreProductHom.ext F G φ ψ (HEq.eq ha) (HEq.eq hb))

/-- Helper for Chap08 Lemma 8 8 5: a relative-diagonal object has identity comparison. -/
private theorem relativeDiagonalOver_obj_comparison
    {X Y : CategoryOver C} (F : X ⥤ᵇ Y) (x : X.obj) :
    ((F.relativeDiagonalOver.toFunctor.obj x).comparison) = 𝟙 (F.toFunctor.obj x) := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the left endpoint of a relative-diagonal object is the
source object. -/
private theorem relativeDiagonalOver_obj_fst
    {X Y : CategoryOver C} (F : X ⥤ᵇ Y) (x : X.obj) :
    ((F.relativeDiagonalOver.toFunctor.obj x).obj.fst.1) = x := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the right endpoint of a relative-diagonal object is the
source object. -/
private theorem relativeDiagonalOver_obj_snd
    {X Y : CategoryOver C} (F : X ⥤ᵇ Y) (x : X.obj) :
    ((F.relativeDiagonalOver.toFunctor.obj x).obj.snd.1) = x := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the structure functor of a fibred category to the base
preserves strongly cartesian morphisms. -/
private theorem toBaseBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    BasedFunctor.PreservesStronglyCartesian X.toBasedCategory.toBase := by
  intro a b φ hφ
  -- In the identity projection on the base every arrow is strongly cartesian.
  simpa [BasedCategory.toBase] using
    (inferInstance : IsFibredInGroupoids (𝟭 C)).isStronglyCartesian_map (X.p.map φ)

/-- Helper for Chap08 Lemma 8 8 5: the lifted base projection is the identity projection viewed
in the owner universe used by saturated fibred categories. -/
private abbrev uliftBaseProjection : ULift.{max u v, u} C ⥤ C :=
  ULift.downFunctor

/-- Helper for Chap08 Lemma 8 8 5: the identity projection composed with the lifted-base
inclusion is unchanged. -/
private theorem upFunctor_comp_uliftBaseProjection :
    ULift.upFunctor ⋙ (uliftBaseProjection (C := C)) = 𝟭 C :=
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base projection is unchanged after composing with
the identity projection on the base. -/
private theorem uliftBaseProjection_comp_id :
    (uliftBaseProjection (C := C)) ⋙ 𝟭 C = uliftBaseProjection (C := C) :=
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the base identity maps to its lifted owner model over `C`. -/
private abbrev baseToULiftBase :
    BasedCategory.ofFunctor (𝟭 C) ⥤ᵇ
      BasedCategory.ofFunctor (uliftBaseProjection (C := C)) where
  toFunctor := ULift.upFunctor
  w := upFunctor_comp_uliftBaseProjection

/-- Helper for Chap08 Lemma 8 8 5: the lifted base owner model maps back to the base identity. -/
private abbrev uliftBaseToBase :
    BasedCategory.ofFunctor (uliftBaseProjection (C := C)) ⥤ᵇ
      BasedCategory.ofFunctor (𝟭 C) where
  toFunctor := uliftBaseProjection (C := C)
  w := uliftBaseProjection_comp_id

/-- Helper for Chap08 Lemma 8 8 5: the universe-lifted inclusion of the base category. -/
private abbrev baseULiftUpFunctor : C ⥤ ULift.{max u v, u} C :=
  ULift.upFunctor

/-- Helper for Chap08 Lemma 8 8 5: compose a projection with the universe-lifted base
inclusion. -/
private abbrev projectionToULiftBase
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    S ⥤ ULift.{max u v, u} C :=
  p ⋙ baseULiftUpFunctor

/-- Helper for Chap08 Lemma 8 8 5: an absolute-inertia object also satisfies the lifted-base
identity condition. -/
private theorem relativeInertiaBaseLiftUp_map_hom_eq_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    (projectionToULiftBase p).map X.α.hom =
      𝟙 ((projectionToULiftBase p).obj X.x) := by
  simpa [projectionToULiftBase, baseULiftUpFunctor, Functor.comp_map, Functor.comp_obj,
    ULift.upFunctor] using X.map_hom_eq_id

/-- Helper for Chap08 Lemma 8 8 5: a lifted-base inertia object also satisfies the ordinary
absolute-inertia identity condition. -/
private theorem relativeInertiaBaseLiftDown_map_hom_eq_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    p.map X.α.hom = 𝟙 (p.obj X.x) := by
  simpa [projectionToULiftBase, baseULiftUpFunctor, Functor.comp_map, Functor.comp_obj,
    ULift.upFunctor] using X.map_hom_eq_id

/-- Helper for Chap08 Lemma 8 8 5: send an absolute-inertia object to the corresponding
lifted-base relative-inertia object. -/
private abbrev relativeInertiaBaseLiftUpObj
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    RelativeInertiaObject (projectionToULiftBase p) where
  x := X.x
  α := X.α
  map_hom_eq_id := relativeInertiaBaseLiftUp_map_hom_eq_id p X

/-- Helper for Chap08 Lemma 8 8 5: forget the lifted-base proof condition on an inertia object. -/
private abbrev relativeInertiaBaseLiftDownObj
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    RelativeInertiaObject p where
  x := X.x
  α := X.α
  map_hom_eq_id := relativeInertiaBaseLiftDown_map_hom_eq_id p X

/-- Helper for Chap08 Lemma 8 8 5: morphisms of absolute-inertia objects are unchanged after
lifting the base identity condition. -/
private abbrev relativeInertiaBaseLiftUpHom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y : RelativeInertiaObject p} (φ : X ⟶ Y) :
    relativeInertiaBaseLiftUpObj p X ⟶ relativeInertiaBaseLiftUpObj p Y where
  φ := φ.φ
  comm := φ.comm

/-- Helper for Chap08 Lemma 8 8 5: morphisms of lifted-base inertia objects are unchanged after
forgetting the lifted proof condition. -/
private abbrev relativeInertiaBaseLiftDownHom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y : RelativeInertiaObject (projectionToULiftBase p)} (φ : X ⟶ Y) :
    relativeInertiaBaseLiftDownObj p X ⟶ relativeInertiaBaseLiftDownObj p Y where
  φ := φ.φ
  comm := φ.comm

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base inertia functor preserves identities. -/
private theorem relativeInertiaBaseLiftUpHom_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    relativeInertiaBaseLiftUpHom p (𝟙 X) =
      𝟙 (relativeInertiaBaseLiftUpObj p X) := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base inertia functor preserves composition. -/
private theorem relativeInertiaBaseLiftUpHom_comp
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y Z : RelativeInertiaObject p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    relativeInertiaBaseLiftUpHom p (φ ≫ ψ) =
      relativeInertiaBaseLiftUpHom p φ ≫ relativeInertiaBaseLiftUpHom p ψ := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base proof-forgetting functor preserves
identities. -/
private theorem relativeInertiaBaseLiftDownHom_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    relativeInertiaBaseLiftDownHom p (𝟙 X) =
      𝟙 (relativeInertiaBaseLiftDownObj p X) := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base proof-forgetting functor preserves
composition. -/
private theorem relativeInertiaBaseLiftDownHom_comp
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y Z : RelativeInertiaObject (projectionToULiftBase p)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    relativeInertiaBaseLiftDownHom p (φ ≫ ψ) =
      relativeInertiaBaseLiftDownHom p φ ≫ relativeInertiaBaseLiftDownHom p ψ := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the functor from absolute inertia to lifted-base inertia. -/
private abbrev relativeInertiaBaseLiftUpFunctor
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    RelativeInertiaObject p ⥤ RelativeInertiaObject (projectionToULiftBase p) where
  obj := relativeInertiaBaseLiftUpObj p
  map := relativeInertiaBaseLiftUpHom p
  map_id := relativeInertiaBaseLiftUpHom_id p
  map_comp := relativeInertiaBaseLiftUpHom_comp p

/-- Helper for Chap08 Lemma 8 8 5: the functor from lifted-base inertia back to absolute
inertia. -/
private abbrev relativeInertiaBaseLiftDownFunctor
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    RelativeInertiaObject (projectionToULiftBase p) ⥤ RelativeInertiaObject p where
  obj := relativeInertiaBaseLiftDownObj p
  map := relativeInertiaBaseLiftDownHom p
  map_id := relativeInertiaBaseLiftDownHom_id p
  map_comp := relativeInertiaBaseLiftDownHom_comp p

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base inertia functor lies over the same base
projection. -/
private theorem relativeInertiaBaseLiftUpFunctor_w
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    relativeInertiaBaseLiftUpFunctor p ⋙ relativeInertiaProjection (projectionToULiftBase p) p =
      relativeInertiaProjection p p :=
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the lifted-base proof-forgetting functor lies over the same
base projection. -/
private theorem relativeInertiaBaseLiftDownFunctor_w
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    relativeInertiaBaseLiftDownFunctor p ⋙ relativeInertiaProjection p p =
      relativeInertiaProjection (projectionToULiftBase p) p :=
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the based functor from absolute inertia to lifted-base
inertia. -/
private abbrev relativeInertiaBaseLiftUpBased
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    BasedCategory.ofFunctor (relativeInertiaProjection p p) ⥤ᵇ
      BasedCategory.ofFunctor (relativeInertiaProjection (projectionToULiftBase p) p) where
  toFunctor := relativeInertiaBaseLiftUpFunctor p
  w := relativeInertiaBaseLiftUpFunctor_w p

/-- Helper for Chap08 Lemma 8 8 5: the based functor from lifted-base inertia back to absolute
inertia. -/
private abbrev relativeInertiaBaseLiftDownBased
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    BasedCategory.ofFunctor (relativeInertiaProjection (projectionToULiftBase p) p) ⥤ᵇ
      BasedCategory.ofFunctor (relativeInertiaProjection p p) where
  toFunctor := relativeInertiaBaseLiftDownFunctor p
  w := relativeInertiaBaseLiftDownFunctor_w p

/-- Helper for Chap08 Lemma 8 8 5: forgetting after lifting gives the original inertia object. -/
private theorem relativeInertiaBaseLiftDownUpObj_eq
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    relativeInertiaBaseLiftDownObj p (relativeInertiaBaseLiftUpObj p X) = X := by
  cases X
  simp [relativeInertiaBaseLiftUpObj, relativeInertiaBaseLiftDownObj]

/-- Helper for Chap08 Lemma 8 8 5: lifting after forgetting gives the lifted-base inertia
object. -/
private theorem relativeInertiaBaseLiftUpDownObj_eq
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    relativeInertiaBaseLiftUpObj p (relativeInertiaBaseLiftDownObj p X) = X := by
  cases X
  simp [relativeInertiaBaseLiftUpObj, relativeInertiaBaseLiftDownObj]

/-- Helper for Chap08 Lemma 8 8 5: the unit component for the lifted-base inertia equivalence
lies over the identity. -/
private theorem relativeInertiaBaseLift_unit_isHomLift
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    (relativeInertiaProjection p p).IsHomLift (𝟙 ((relativeInertiaProjection p p).obj X))
      (eqToHom (relativeInertiaBaseLiftDownUpObj_eq p X).symm) := by
  simpa [relativeInertiaProjection, relativeInertiaBaseLiftDownUpObj_eq]
    using
      (IsHomLift.id (p := relativeInertiaProjection p p) rfl :
        (relativeInertiaProjection p p).IsHomLift
          (𝟙 ((relativeInertiaProjection p p).obj X)) (𝟙 X))

/-- Helper for Chap08 Lemma 8 8 5: the counit component for the lifted-base inertia equivalence
lies over the identity. -/
private theorem relativeInertiaBaseLift_counit_isHomLift
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    (relativeInertiaProjection (projectionToULiftBase p) p).IsHomLift
      (𝟙 ((relativeInertiaProjection (projectionToULiftBase p) p).obj X))
      (eqToHom (relativeInertiaBaseLiftUpDownObj_eq p X)) := by
  simpa [relativeInertiaProjection, relativeInertiaBaseLiftUpDownObj_eq]
    using
      (IsHomLift.id (p := relativeInertiaProjection (projectionToULiftBase p) p) rfl :
        (relativeInertiaProjection (projectionToULiftBase p) p).IsHomLift
          (𝟙 ((relativeInertiaProjection (projectionToULiftBase p) p).obj X)) (𝟙 X))

/-- Helper for Chap08 Lemma 8 8 5: absolute inertia and lifted-base inertia are equivalent over
the base. -/
private theorem relativeInertiaBaseLiftUpBased_isEquivalenceOverBase
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    (relativeInertiaBaseLiftUpBased p).IsEquivalenceOverBase := by
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime (relativeInertiaBaseLiftDownBased p) ?_ ?_
  · refine BasedNatIso.mkNatIso ?_ ?_
    · refine NatIso.ofComponents (fun X ↦ eqToIso (relativeInertiaBaseLiftDownUpObj_eq p X).symm) ?_
      intro X Y φ
      apply RelativeInertiaHom.ext
      change φ.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ φ.φ
      simp
    · intro X
      exact relativeInertiaBaseLift_unit_isHomLift p X
  · refine BasedNatIso.mkNatIso ?_ ?_
    · refine NatIso.ofComponents (fun X ↦ eqToIso (relativeInertiaBaseLiftUpDownObj_eq p X)) ?_
      intro X Y φ
      apply RelativeInertiaHom.ext
      change φ.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ φ.φ
      simp
    · intro X
      exact relativeInertiaBaseLift_counit_isHomLift p X

/-- Helper for Chap08 Lemma 8 8 5: the lifted base owner model is equivalent over the base to
the identity projection. -/
private theorem baseToULiftBase_isEquivalenceOverBase :
    (baseToULiftBase (C := C)).IsEquivalenceOverBase := by
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime (uliftBaseToBase (C := C)) ?_ ?_
  · refine BasedNatIso.mkNatIso ?_ ?_
    · exact (ULift.equivalence : C ≌ ULift.{max u v, u} C).unitIso
    · intro a
      simpa [baseToULiftBase, uliftBaseToBase, BasedCategory.ofFunctor] using
        (IsHomLift.id (p := 𝟭 C) rfl : (𝟭 C).IsHomLift (𝟙 a) (𝟙 a))
  · refine BasedNatIso.mkNatIso ?_ ?_
    · exact (ULift.equivalence : C ≌ ULift.{max u v, u} C).counitIso
    · intro a
      simpa [baseToULiftBase, uliftBaseToBase, uliftBaseProjection, BasedCategory.ofFunctor,
        ULift.upFunctor, ULift.downFunctor] using
        (IsHomLift.id (p := uliftBaseProjection (C := C)) rfl :
          (uliftBaseProjection (C := C)).IsHomLift (𝟙 a.down) (𝟙 a.down))

/-- Helper for Chap08 Lemma 8 8 5: morphisms in the lifted base projection are strongly
cartesian over their image. -/
private theorem uliftBaseProjection_isStronglyCartesian
    {R T : ULift.{max u v, u} C} (f : R ⟶ T) :
    (uliftBaseProjection (C := C)).IsStronglyCartesian
      ((uliftBaseProjection (C := C)).map f) f := by
  cases R with
  | up R =>
    cases T with
    | up T =>
      -- After splitting the lifted objects, this is the identity projection on the base arrow.
      refine { toIsHomLift := ?_, universal_property' := ?_ }
      · infer_instance
      · intro a' g ψ hψ
        cases a' with
        | up A =>
          let γ : (ULift.up A : ULift.{max u v, u} C) ⟶ ULift.up R := g
          have hg : (uliftBaseProjection (C := C)).IsHomLift g γ := by
            refine IsHomLift.of_fac (uliftBaseProjection (C := C)) g γ rfl rfl ?_
            simp [γ, ULift.downFunctor]
          refine ⟨γ, ?_, ?_⟩
          · constructor
            · exact hg
            · have hψeq :=
                @IsHomLift.eq_of_isHomLift _ _ _ _ (uliftBaseProjection (C := C)) _ _
                  (g ≫ (uliftBaseProjection (C := C)).map f) ψ hψ
              simpa [γ, uliftBaseProjection, ULift.downFunctor] using hψeq
          · intro χ hχ
            have hχeq :=
              @IsHomLift.eq_of_isHomLift _ _ _ _ (uliftBaseProjection (C := C)) _ _ g χ hχ.1
            simpa [γ, uliftBaseProjection, ULift.downFunctor] using hχeq.symm

/-- Helper for Chap08 Lemma 8 8 5: the lifted structure morphism from a fibred category to the
base preserves strongly cartesian morphisms. -/
private theorem toULiftBase_preservesStronglyCartesian
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    BasedFunctor.PreservesStronglyCartesian
      (BasedFunctor.comp X.toBasedCategory.toBase (baseToULiftBase (C := C))) := by
  intro a b φ hφ
  simpa [BasedCategory.toBase, baseToULiftBase, uliftBaseProjection] using
    uliftBaseProjection_isStronglyCartesian (C := C) (X.p.map φ)

/-- Helper for Chap08 Lemma 8 8 5: every two objects in a fiber of the identity projection are
equal. -/
private theorem identityFiberObj_eq {U : C} (X Y : (𝟭 C).Fiber U) : X = Y := by
  apply Subtype.ext
  exact X.2.trans Y.2.symm

/-- Helper for Chap08 Lemma 8 8 5: every two morphisms in a fiber of the identity projection are
equal. -/
private theorem identityFiberHom_eq {U : C} {X Y : (𝟭 C).Fiber U} (f g : X ⟶ Y) :
    f = g := by
  apply Functor.Fiber.hom_ext
  change f.1 = g.1
  letI : (𝟭 C).IsHomLift (𝟙 U) f.1 := f.2
  letI : (𝟭 C).IsHomLift (𝟙 U) g.1 := g.2
  have hf : (𝟭 C).map f.1 =
      eqToHom (IsHomLift.domain_eq (𝟭 C) (𝟙 U) f.1) ≫
        𝟙 U ≫ eqToHom (IsHomLift.codomain_eq (𝟭 C) (𝟙 U) f.1).symm := by
    exact IsHomLift.fac' (𝟭 C) (𝟙 U) f.1
  have hg : (𝟭 C).map g.1 =
      eqToHom (IsHomLift.domain_eq (𝟭 C) (𝟙 U) g.1) ≫
        𝟙 U ≫ eqToHom (IsHomLift.codomain_eq (𝟭 C) (𝟙 U) g.1).symm := by
    exact IsHomLift.fac' (𝟭 C) (𝟙 U) g.1
  simpa using hf.trans hg.symm

/-- Helper for Chap08 Lemma 8 8 5: fibers of the identity projection are contractible
categories. -/
private abbrev identityFiberIso {U : C} (X Y : (𝟭 C).Fiber U) : X ≅ Y :=
  eqToIso (identityFiberObj_eq X Y)

/-- Helper for Chap08 Lemma 8 8 5: descent for the identity projection over the base is
contractible on every cover. -/
private theorem identityFunctor_descentData_isEquivalence
    {ι : Type*} {U : C} {Xc : ι → C} (f : ∀ i, Xc i ⟶ U) :
    ((canonicalFiberPseudofunctor (𝟭 C)).toDescentData f).IsEquivalence := by
  let F := (canonicalFiberPseudofunctor (𝟭 C)).toDescentData f
  letI : F.Faithful := by
    constructor
    intro M N φ ψ h
    exact identityFiberHom_eq φ ψ
  letI : F.Full := by
    constructor
    intro M N η
    refine ⟨(identityFiberIso M N).hom, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact identityFiberHom_eq _ _
  letI : F.EssSurj := by
    constructor
    intro D
    let M : (canonicalFiberPseudofunctor (𝟭 C)).obj (.mk (Opposite.op U)) :=
      ⟨U, rfl⟩
    refine ⟨M, ⟨?_⟩⟩
    refine Pseudofunctor.DescentData.isoMk (fun i ↦ ?_) ?_
    · exact identityFiberIso _ _
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      exact identityFiberHom_eq _ _
  exact Functor.IsEquivalence.mk (F := F) inferInstance inferInstance inferInstance

/-- Helper for Chap08 Lemma 8 8 5: the identity projection of the base category is a stack for
any topology on the base. -/
private theorem identityFunctor_isStackOnSite : IsStackOnSite J (𝟭 C) := by
  refine (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J (𝟭 C)).2 ?_
  intro U S
  exact identityFunctor_descentData_isEquivalence (fun I : S.Arrow ↦ I.f)

/-- Helper for Chap08 Lemma 8 8 5: the lifted base projection is a stack over the site. -/
private theorem uliftBaseProjection_isStackOnSite :
    IsStackOnSite J (uliftBaseProjection (C := C)) := by
  exact
    (isStackOnSite_iff_of_equivalence_over_base J (𝟭 C)
      (uliftBaseProjection (C := C)) (baseToULiftBase (C := C))
      baseToULiftBase_isEquivalenceOverBase).1 identityFunctor_isStackOnSite

/-- Helper for Chap08 Lemma 8 8 5: the lifted base projection is fibered over the base. -/
private instance uliftBaseProjection_isFibered :
    (uliftBaseProjection (C := C)).IsFibered := by
  rw [Functor.isFibered_iff_exists_isStronglyCartesian]
  intro x V f
  cases x with
  | up U =>
    exact ⟨ULift.up V, f, uliftBaseProjection_isStronglyCartesian (C := C) f⟩

/-- Helper for Chap08 Lemma 8 8 5: the bundled identity projection carries the stack
structure of the identity functor. -/
private theorem baseStack_isStackOnSite :
    IsStackOnSite J
      ((FibredCategoryOver.ofFunctor (uliftBaseProjection (C := C)) :
        FibredCategoryOver.{u, v, max u v, v} C).p) := by
  simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
    (uliftBaseProjection_isStackOnSite (J := J) (C := C))

/-- Helper for Chap08 Lemma 8 8 5: the identity projection over the base, viewed as a stack. -/
private noncomputable abbrev baseStack : StackOver J :=
  ⟨(FibredCategoryOver.ofFunctor (uliftBaseProjection (C := C)) :
      FibredCategoryOver.{u, v, max u v, v} C), baseStack_isStackOnSite (J := J)⟩

/-- Helper for Chap08 Lemma 8 8 5: the lifted structure functor, with target spelled as the
underlying based category of the base stack. -/
private noncomputable abbrev toBaseBasedFunctor
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    X.toBasedCategory ⥤ᵇ (baseStack (J := J)).toFibredCategoryOver.toBasedCategory :=
  BasedFunctor.comp X.toBasedCategory.toBase (baseToULiftBase (C := C))

/-- Helper for Chap08 Lemma 8 8 5: the target-spelled lifted structure functor preserves
strongly cartesian morphisms. -/
private theorem toBaseBasedFunctor_preservesStronglyCartesian'
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    BasedFunctor.PreservesStronglyCartesian (toBaseBasedFunctor (J := J) X) := by
  simpa [toBaseBasedFunctor] using toULiftBase_preservesStronglyCartesian (C := C) X

/-- Helper for Chap08 Lemma 8 8 5: the structure functor to the base, rebundled as a morphism of
fibred categories. -/
private noncomputable abbrev toBaseFibredMap
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    X ⟶ (baseStack (J := J)).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (toBaseBasedFunctor (J := J) X)
    (toBaseBasedFunctor_preservesStronglyCartesian' (J := J) X)

/-- Helper for Chap08 Lemma 8 8 5: the structure morphism from a stack to the base stack. -/
private noncomputable abbrev toBaseStackMor
    (Y : StackOver.{u, v, max u v, v} J) :
    Y ⟶ baseStack (J := J) :=
  InducedCategory.Hom.ofFibredCategoryMor (toBaseFibredMap (J := J) Y.toFibredCategoryOver)

/-- Helper for Chap08 Lemma 8 8 5: the self-`2`-fibre product of a fibred category over the
base. -/
private noncomputable abbrev basePairTarget
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryOver.{u, v, max u v, v} C :=
  FibredCategoryOver.twoFibreProduct (toBaseFibredMap (J := J) X) (toBaseFibredMap (J := J) X)

/-- Helper for Chap08 Lemma 8 8 5: the target self-pair over the lifted base of a stack is again
a stack. -/
private theorem basePairStackTarget_isStackOnSite
    (Y : StackOver.{u, v, max u v, v} J) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct
        (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y))
        (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y))).p := by
  infer_instance

/-- Helper for Chap08 Lemma 8 8 5: the self-`2`-fibre product of a stack over the base, viewed as
a stack. -/
private noncomputable abbrev basePairStack
    (Y : StackOver.{u, v, max u v, v} J) :
    StackOver J :=
  ⟨FibredCategoryOver.twoFibreProduct
      (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y))
      (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y)),
    basePairStackTarget_isStackOnSite Y⟩

/-- Helper for Chap08 Lemma 8 8 5: the compatibility between a morphism to a stack and the
structure maps to the base. -/
private theorem baseCompatibility_eq
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    i ≫ InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor X') =
      toBaseFibredMap (J := J) X ≫ (𝟙 (baseStack (J := J)).toFibredCategoryOver) := by
  -- Both sides are the same based functor to the identity projection after unfolding the wrappers.
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  change
    ({ toFunctor := (FibredCategoryMor.toFunctor i ⋙ X'.toFibredCategoryOver.p) ⋙
        baseULiftUpFunctor (C := C), w := _ } :
      X.toBasedCategory ⥤ᵇ (baseStack (J := J)).toFibredCategoryOver.toBasedCategory) =
      { toFunctor := X.p ⋙ baseULiftUpFunctor (C := C), w := _ }
  simpa [BasedFunctor.mk.injEq, Category.assoc] using
    congrArg (fun F ↦ F ⋙ baseULiftUpFunctor (C := C)) (FibredCategoryMor.comm i)

/-- Helper for Chap08 Lemma 8 8 5: the base-compatibility isomorphism used by the first
`2`-fibre-product stackification. -/
private noncomputable abbrev baseCompatibilityIso
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    i ≫ InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor X') ≅
      toBaseFibredMap (J := J) X ≫ (𝟙 (baseStack (J := J)).toFibredCategoryOver) :=
  eqToIso (baseCompatibility_eq i)

/-- Helper for Chap08 Lemma 8 8 5: the source `2`-fibre-product square transported to the
chosen target morphisms. -/
private noncomputable def stackificationPullbackSquare
    {X Y Z : FibredCategoryOver.{u, v, max u v, v} C}
    {X' Y' Z' : StackOver.{u, v, max u v, v} J}
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X'.toFibredCategoryOver)
    (j : FibredCategoryMor Y Y'.toFibredCategoryOver)
    (k : FibredCategoryMor Z Z'.toFibredCategoryOver)
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    BicategoricalTwoCommutativeSquare fF gF :=
  (((FibredCategoryOver.twoFibreProductSquare f g).postcompose β.symm).symm.postcomposeRight
    α.symm).symm

/-- Helper for Chap08 Lemma 8 8 5: the terminal comparison for a pullback of stackification
morphisms, using the locally rebuilt transported square. -/
private noncomputable abbrev stackificationPullbackComparisonHom
    {X Y Z : FibredCategoryOver.{u, v, max u v, v} C}
    {X' Y' Z' : StackOver.{u, v, max u v, v} J}
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X'.toFibredCategoryOver)
    (j : FibredCategoryMor Y Y'.toFibredCategoryOver)
    (k : FibredCategoryMor Z Z'.toFibredCategoryOver)
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ InducedCategory.Hom.toFibredCategoryMor f' ≅ f ≫ j)
    (β : k ≫ InducedCategory.Hom.toFibredCategoryMor g' ≅ g ≫ j) :
    FibredCategoryMor
      (FibredCategoryOver.twoFibreProduct f g)
      (FibredCategoryOver.twoFibreProduct
        (InducedCategory.Hom.toFibredCategoryMor f')
        (InducedCategory.Hom.toFibredCategoryMor g')) :=
  let fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver :=
    InducedCategory.Hom.toFibredCategoryMor f'
  let gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver :=
    InducedCategory.Hom.toFibredCategoryMor g'
  let P := stackificationPullbackSquare f g i j k fF gF α β
  (FibredCategoryOver.twoFibreProduct_terminalLift fF gF P).hom

/-- Helper for Chap08 Lemma 8 8 5: an isomorphism of morphisms between `2`-commutative squares
induces an isomorphism of their apex morphisms. -/
private noncomputable def squareHomApexIso
    {X Y Z : FibredCategoryOver.{u, v, max u v, v} C}
    {f : X ⟶ Z} {g : Y ⟶ Z}
    {P Q : BicategoricalTwoCommutativeSquare f g}
    {u v : P ⟶ Q} (e : u ≅ v) :
    u.hom ≅ v.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by
    exact congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.hom_inv_id
  inv_hom_id := by
    exact congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.inv_hom_id

/-- Helper for Chap08 Lemma 8 8 5: the morphism from the source self-pair over the base to the
target self-pair induced by a stackification morphism. -/
private noncomputable abbrev basePairMap
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    basePairTarget (J := J) X ⟶ (basePairStack X').toFibredCategoryOver :=
  show basePairTarget (J := J) X ⟶ (basePairStack X').toFibredCategoryOver from
    twoFibreProductOfStackificationsHom
      (toBaseFibredMap (J := J) X) (toBaseFibredMap (J := J) X)
      i (𝟙 (baseStack (J := J)).toFibredCategoryOver) i
      (toBaseStackMor X') (toBaseStackMor X')
      (baseCompatibilityIso i) (baseCompatibilityIso i)

/-- Helper for Chap08 Lemma 8 8 5: the induced map on self-pairs over the base is a
stackification. -/
private theorem basePairMap_isStackification
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J}
    (i : X ⟶ X')
    (hi : FibredCategoryMor.IsStackification i) :
    FibredCategoryMor.IsStackification (basePairMap i) := by
  -- Apply Lemma 8.8.4 to the two structure maps and the identity stackification of the base.
  have hCanonical :=
    twoFibreProduct_of_stackifications_isStackification
      (J := J)
      (f := toBaseFibredMap (J := J) X) (g := toBaseFibredMap (J := J) X)
      (i := i) (j := (𝟙 (baseStack (J := J)).toFibredCategoryOver)) (k := i)
      (f' := toBaseStackMor X') (g' := toBaseStackMor X')
      (α := baseCompatibilityIso i) (β := baseCompatibilityIso i)
      hi (stack_identity_isStackification (J := J) (baseStack (J := J))) hi
  exact hCanonical

/-- Helper for Chap08 Lemma 8 8 5: the canonical relative diagonal, rebundled as a morphism of
fibred categories. -/
private noncomputable abbrev relativeDiagonalFibredMap
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    X ⟶ basePairTarget (J := J) X :=
  show X ⟶ basePairTarget (J := J) X from
    FibredCategoryMor.ofBasedFunctor
      (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor (toBaseFibredMap (J := J) X)))
      (relativeDiagonalOver_preserves_strongly_cartesian (toBaseFibredMap (J := J) X))

/-- Helper for Chap08 Lemma 8 8 5: the fibred relative diagonal has source object as its left
endpoint. -/
private theorem relativeDiagonalFibredMap_obj_fst
    (X : FibredCategoryOver.{u, v, max u v, v} C) (x : X.S) :
    (((SubTwoCategory.Hom.toHom (relativeDiagonalFibredMap (J := J) X)).obj x).obj.fst.1) =
      x := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the fibred relative diagonal has source object as its right
endpoint. -/
private theorem relativeDiagonalFibredMap_obj_snd
    (X : FibredCategoryOver.{u, v, max u v, v} C) (x : X.S) :
    (((SubTwoCategory.Hom.toHom (relativeDiagonalFibredMap (J := J) X)).obj x).obj.snd.1) =
      x := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the relative diagonal of a stack as a stack morphism. -/
private noncomputable abbrev relativeDiagonalStackMor
    (Y : StackOver.{u, v, max u v, v} J) :
    Y ⟶ basePairStack Y :=
  InducedCategory.Hom.ofFibredCategoryMor
    (show Y.toFibredCategoryOver ⟶ (basePairStack Y).toFibredCategoryOver from
      FibredCategoryMor.ofBasedFunctor
        (BasedFunctor.relativeDiagonalOver
          (FibredCategoryMor.toBasedFunctor
            (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y))))
        (relativeDiagonalOver_preserves_strongly_cartesian
          (InducedCategory.Hom.toFibredCategoryMor (toBaseStackMor Y))))

/-- Helper for Chap08 Lemma 8 8 5: the comparison field in the base-pair image of a relative
diagonal object has the same normal form as the target relative diagonal comparison. -/
private theorem basePairMap_relativeDiagonal_obj_comparison
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    (((FibredCategoryMor.toFunctor
      (i ≫ InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor X'))).obj
        x).comparison) ≍
      (((FibredCategoryMor.toFunctor (relativeDiagonalFibredMap X ≫ basePairMap i)).obj
        x).comparison) := by
  -- TODO(replan): prove the staged comparison-field normal form for `basePairMap` applied to a
  -- relative diagonal object. The endpoint object fields reduce definitionally; the remaining
  -- field is the comparison stored by `twoFibreProductOfStackificationsHom`.
  dsimp [relativeDiagonalStackMor, basePairMap]
  erw [twoFibreProductOfStackificationsHom_obj_comparison]
  apply heq_of_eq
  let θ := FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)
  have hθ := congrArg (fun η ↦ η.app x) θ.hom_inv_id
  erw [relativeDiagonalOver_obj_comparison]
  erw [relativeDiagonalOver_obj_comparison]
  have hmap : (FibredCategoryMor.toFunctor (𝟙 (baseStack (J := J)).toFibredCategoryOver)).map
      (𝟙 ((FibredCategoryMor.toBasedFunctor (toBaseFibredMap (J := J) X)).obj x)) =
    𝟙 ((FibredCategoryMor.toBasedFunctor
      (toBaseFibredMap (J := J) X ≫ 𝟙 (baseStack (J := J)).toFibredCategoryOver)).obj x) := rfl
  erw [hmap]
  have hfst := relativeDiagonalFibredMap_obj_fst (J := J) X x
  have hsnd := relativeDiagonalFibredMap_obj_snd (J := J) X x
  convert hθ.symm
  · cases hfst
    cases hsnd
    change (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).hom.app x ≫
        𝟙 ((FibredCategoryMor.toBasedFunctor
          (toBaseFibredMap (J := J) X ≫ 𝟙 (baseStack (J := J)).toFibredCategoryOver)).obj x) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).inv.app x =
      (θ.hom ≫ θ.inv).app x
    calc
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).hom.app x ≫
            𝟙 ((FibredCategoryMor.toBasedFunctor
              (toBaseFibredMap (J := J) X ≫
                𝟙 (baseStack (J := J)).toFibredCategoryOver)).obj x) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).inv.app x
          =
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).hom.app x ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).inv.app x := by
            exact congrArg
              (fun f ↦
                (FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).hom.app x ≫ f)
              (Category.id_comp
                ((FibredCategoryMor.basedFunctorIsoOfOwnerIso (baseCompatibilityIso i)).inv.app x))
      _ = (θ.hom ≫ θ.inv).app x := rfl

/-- Helper for Chap08 Lemma 8 8 5: objectwise, the base-pair image of the source relative
diagonal is the target relative diagonal after applying `i`. -/
private theorem basePairMap_relativeDiagonal_obj
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    (FibredCategoryMor.toFunctor
      (i ≫ InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor X'))).obj x =
      (FibredCategoryMor.toFunctor (relativeDiagonalFibredMap X ≫ basePairMap i)).obj x := by
  -- Compare explicit pullback objects by base, endpoints, and the staged comparison field.
  apply explicitTwoFibreProductObject_ext_underlying
  · exact Functor.congr_obj (FibredCategoryMor.comm i) x
  · rfl
  · rfl
  · exact basePairMap_relativeDiagonal_obj_comparison i x

/-- Helper for Chap08 Lemma 8 8 5: the relative diagonal naturality comparison at the ordinary
functor level. -/
private theorem diagonalNaturality_toFunctor_eq
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    FibredCategoryMor.toFunctor
        (i ≫ InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor X')) =
      FibredCategoryMor.toFunctor (relativeDiagonalFibredMap X ≫ basePairMap i) := by
  -- Objectwise the two diagonal routes agree; on morphisms it is enough to compare the two
  -- endpoint components heterogeneously.
  refine Functor.hext (fun x ↦ basePairMap_relativeDiagonal_obj i x) ?_
  intro x y f
  refine explicitTwoFibreProductHom_heq_of_components
    (basePairMap_relativeDiagonal_obj i x) (basePairMap_relativeDiagonal_obj i y) _ _ ?_ ?_
  · apply heq_of_eq
    erw [twoFibreProductOfStackificationsHom_map_a]
    rfl
  · apply heq_of_eq
    erw [twoFibreProductOfStackificationsHom_map_b]
    rfl

/-- Helper for Chap08 Lemma 8 8 5: the relative diagonal is natural for the explicit base-pair
comparison induced by a morphism to a stack. -/
private theorem diagonalNaturality_eq
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    i ≫ InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor X') =
      relativeDiagonalFibredMap X ≫ basePairMap i := by
  -- Reduce the fibred-morphism equality to the ordinary-functor naturality helper.
  exact fibredCategoryMor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq i)

/-- Helper for Chap08 Lemma 8 8 5: the owner isomorphism expressing naturality of the relative
diagonal. -/
private noncomputable abbrev diagonalNaturalityIso
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    i ≫ InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor X') ≅
      relativeDiagonalFibredMap X ≫ basePairMap i :=
  FibredCategoryMor.ownerIsoOfBasedFunctorIso
    (eqToIso (basedFunctor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq i)))

/-- Helper for Chap08 Lemma 8 8 5: the forward relative-diagonal naturality isomorphism has
identity left endpoint component. -/
private theorem diagonalNaturalityIso_hom_app_a
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    ((FibredCategoryMor.basedFunctorIsoOfOwnerIso (diagonalNaturalityIso (J := J) i)).hom.app
        x).a =
      𝟙 ((FibredCategoryMor.toFunctor i).obj x) := by
  let hbf := basedFunctor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq (J := J) i)
  let hobj := congrArg
    (fun F : X.toBasedCategory ⥤ᵇ
        (basePairStack (J := J) X').toFibredCategoryOver.toBasedCategory ↦
      F.toFunctor.obj x)
    hbf
  have hcomp := explicitTwoFibreProduct_eqToHom_components hobj
  rw [diagonalNaturalityIso]
  rw [basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_hom]
  change ((eqToIso hbf).hom.app x).a = 𝟙 ((FibredCategoryMor.toFunctor i).obj x)
  rw [basedFunctor_eqToIso_hom_app]
  exact hcomp.1

/-- Helper for Chap08 Lemma 8 8 5: the forward relative-diagonal naturality isomorphism has
identity right endpoint component. -/
private theorem diagonalNaturalityIso_hom_app_b
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    ((FibredCategoryMor.basedFunctorIsoOfOwnerIso (diagonalNaturalityIso (J := J) i)).hom.app
        x).b =
      𝟙 ((FibredCategoryMor.toFunctor i).obj x) := by
  let hbf := basedFunctor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq (J := J) i)
  let hobj := congrArg
    (fun F : X.toBasedCategory ⥤ᵇ
        (basePairStack (J := J) X').toFibredCategoryOver.toBasedCategory ↦
      F.toFunctor.obj x)
    hbf
  have hcomp := explicitTwoFibreProduct_eqToHom_components hobj
  rw [diagonalNaturalityIso]
  rw [basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_hom]
  change ((eqToIso hbf).hom.app x).b = 𝟙 ((FibredCategoryMor.toFunctor i).obj x)
  rw [basedFunctor_eqToIso_hom_app]
  exact hcomp.2

/-- Helper for Chap08 Lemma 8 8 5: the inverse relative-diagonal naturality isomorphism has
identity left endpoint component. -/
private theorem diagonalNaturalityIso_inv_app_a
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    ((FibredCategoryMor.basedFunctorIsoOfOwnerIso (diagonalNaturalityIso (J := J) i)).inv.app
        x).a =
      𝟙 ((FibredCategoryMor.toFunctor i).obj x) := by
  let hbf := basedFunctor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq (J := J) i)
  let hobj := congrArg
    (fun F : X.toBasedCategory ⥤ᵇ
        (basePairStack (J := J) X').toFibredCategoryOver.toBasedCategory ↦
      F.toFunctor.obj x)
    hbf.symm
  have hcomp := explicitTwoFibreProduct_eqToHom_components hobj
  rw [diagonalNaturalityIso]
  rw [basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_inv]
  change ((eqToIso hbf).inv.app x).a = 𝟙 ((FibredCategoryMor.toFunctor i).obj x)
  rw [basedFunctor_eqToIso_inv_app]
  exact hcomp.1

/-- Helper for Chap08 Lemma 8 8 5: the inverse relative-diagonal naturality isomorphism has
identity right endpoint component. -/
private theorem diagonalNaturalityIso_inv_app_b
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') (x : X.S) :
    ((FibredCategoryMor.basedFunctorIsoOfOwnerIso (diagonalNaturalityIso (J := J) i)).inv.app
        x).b =
      𝟙 ((FibredCategoryMor.toFunctor i).obj x) := by
  let hbf := basedFunctor_eq_of_toFunctor_eq (diagonalNaturality_toFunctor_eq (J := J) i)
  let hobj := congrArg
    (fun F : X.toBasedCategory ⥤ᵇ
        (basePairStack (J := J) X').toFibredCategoryOver.toBasedCategory ↦
      F.toFunctor.obj x)
    hbf.symm
  have hcomp := explicitTwoFibreProduct_eqToHom_components hobj
  rw [diagonalNaturalityIso]
  rw [basedFunctorIsoOfOwnerIso_ownerIsoOfBasedFunctorIso_inv]
  change ((eqToIso hbf).inv.app x).b = 𝟙 ((FibredCategoryMor.toFunctor i).obj x)
  rw [basedFunctor_eqToIso_inv_app]
  exact hcomp.2

/-- Helper for Chap08 Lemma 8 8 5: the diagonal self-pullback model of absolute inertia. -/
private noncomputable abbrev absoluteDiagonalTarget
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryOver.{u, v, max u v, v} C :=
  FibredCategoryOver.twoFibreProduct
    (relativeDiagonalFibredMap (J := J) X) (relativeDiagonalFibredMap (J := J) X)

/-- Helper for Chap08 Lemma 8 8 5: the diagonal self-pullback model of a stack is again a
stack. -/
private theorem absoluteDiagonalTarget_isStackOnSite
    (Y : StackOver.{u, v, max u v, v} J) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct
        (InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor Y))
        (InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor Y))).p := by
  infer_instance

/-- Helper for Chap08 Lemma 8 8 5: the diagonal self-pullback model of a stack's absolute
inertia, viewed as a stack. -/
private noncomputable abbrev absoluteDiagonalStack
    (Y : StackOver.{u, v, max u v, v} J) :
    StackOver J :=
  ⟨FibredCategoryOver.twoFibreProduct
      (InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor Y))
      (InducedCategory.Hom.toFibredCategoryMor (relativeDiagonalStackMor Y)),
    absoluteDiagonalTarget_isStackOnSite Y⟩

/-- Helper for Chap08 Lemma 8 8 5: the map induced by a stackification on the diagonal-pullback
model of absolute inertia. -/
private noncomputable abbrev diagonalInertiaModelMap
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    absoluteDiagonalTarget (J := J) X ⟶ (absoluteDiagonalStack X').toFibredCategoryOver :=
  show absoluteDiagonalTarget (J := J) X ⟶ (absoluteDiagonalStack X').toFibredCategoryOver from
    twoFibreProductOfStackificationsHom
      (relativeDiagonalFibredMap (J := J) X) (relativeDiagonalFibredMap (J := J) X)
      i (basePairMap i) i
      (relativeDiagonalStackMor X') (relativeDiagonalStackMor X')
      (diagonalNaturalityIso i) (diagonalNaturalityIso i)

/-- Helper for Chap08 Lemma 8 8 5: the induced map on the diagonal-pullback model is a
stackification. -/
private theorem diagonalInertiaModelMap_isStackification
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J}
    (i : X ⟶ X')
    (hi : FibredCategoryMor.IsStackification i) :
    FibredCategoryMor.IsStackification (diagonalInertiaModelMap i) := by
  -- Apply Lemma 8.8.4 a second time, now to the two relative diagonals, and transport from the
  -- canonical terminal comparison to the explicit one used in the model map.
  have hCanonical :=
    twoFibreProduct_of_stackifications_isStackification
      (J := J)
      (f := relativeDiagonalFibredMap (J := J) X)
      (g := relativeDiagonalFibredMap (J := J) X)
      (i := i) (j := basePairMap i) (k := i)
      (f' := relativeDiagonalStackMor X') (g' := relativeDiagonalStackMor X')
      (α := diagonalNaturalityIso i) (β := diagonalNaturalityIso i)
      hi (basePairMap_isStackification i hi) hi
  exact hCanonical

/-- Helper for Chap08 Lemma 8 8 5: the forward Chapter 4 comparison from absolute inertia to the
diagonal self-pullback model. -/
private noncomputable abbrev absoluteToDiagonalBased
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    (FibredCategoryOver.absoluteInertiaOver X).toBasedCategory ⥤ᵇ
      (absoluteDiagonalTarget (J := J) X).toBasedCategory :=
  BasedFunctor.comp
    (relativeInertiaBaseLiftUpBased X.p)
    (BasedFunctor.relativeInertiaToDiagonalPullback (toBaseBasedFunctor (J := J) X))

/-- Helper for Chap08 Lemma 8 8 5: the forward comparison based functor is an equivalence over
the base. -/
private theorem absoluteToDiagonalBased_isEquivalenceOverBase
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    (absoluteToDiagonalBased (J := J) X).IsEquivalenceOverBase := by
  -- The comparison is the lifted-base inertia equivalence followed by the Chapter 4 diagonal
  -- pullback equivalence.
  simpa [absoluteToDiagonalBased] using
    BasedFunctor.IsEquivalenceOverBase.comp
      (relativeInertiaBaseLiftUpBased_isEquivalenceOverBase X.p)
      (BasedFunctor.relativeInertiaEquivalenceOverBase (toBaseBasedFunctor (J := J) X))

/-- Helper for Chap08 Lemma 8 8 5: the forward Chapter 4 comparison from absolute inertia to the
diagonal self-pullback model. -/
private noncomputable abbrev absoluteToDiagonal
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryOver.absoluteInertiaOver X ⟶ absoluteDiagonalTarget (J := J) X :=
  FibredCategoryMor.ofBasedFunctor
    (absoluteToDiagonalBased (J := J) X)
    (basedFunctor_preservesStronglyCartesian_of_equivalence_over_base
      (FibredCategoryOver.absoluteInertiaOver X).p
      (absoluteDiagonalTarget (J := J) X).p
      (F := absoluteToDiagonalBased (J := J) X)
      (absoluteToDiagonalBased_isEquivalenceOverBase (J := J) X))

/-- Helper for Chap08 Lemma 8 8 5: the forward absolute-inertia comparison is an equivalence over
the base. -/
private theorem absoluteToDiagonal_isEquivalenceOverBase
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryMor.IsEquivalenceOverBase (absoluteToDiagonal (J := J) X) := by
  -- This is exactly the Chapter 4 equivalence after rebundling the comparison as a fibred
  -- category morphism.
  change BasedFunctor.IsEquivalenceOverBase
    (FibredCategoryMor.toBasedFunctor (absoluteToDiagonal (J := J) X))
  simpa [absoluteToDiagonal] using absoluteToDiagonalBased_isEquivalenceOverBase (J := J) X

/-- Helper for Chap08 Lemma 8 8 5: absolute inertia of a stack is again a stack, by transport
from the diagonal self-pullback model. -/
private theorem absoluteInertiaOfStack_isStackOnSite
    (Y : StackOver.{u, v, max u v, v} J) :
    IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver Y.toFibredCategoryOver).p := by
  have hDiagonal :
      IsStackOnSite J (absoluteDiagonalTarget (J := J) Y.toFibredCategoryOver).p := by
    simpa [absoluteDiagonalTarget, absoluteDiagonalStack, relativeDiagonalStackMor,
      relativeDiagonalFibredMap] using absoluteDiagonalTarget_isStackOnSite (J := J) Y
  exact
    (isStackOnSite_iff_of_equivalence_over_base J
      (FibredCategoryOver.absoluteInertiaOver Y.toFibredCategoryOver).p
      (absoluteDiagonalTarget (J := J) Y.toFibredCategoryOver).p
      (FibredCategoryMor.toBasedFunctor (absoluteToDiagonal (J := J) Y.toFibredCategoryOver))
      (absoluteToDiagonal_isEquivalenceOverBase (J := J) Y.toFibredCategoryOver)).2 hDiagonal

/-- The absolute inertia of a bundled stack, viewed again as a bundled stack over `(C, J)`. -/
abbrev absoluteInertiaOfStack
    (Y : StackOver.{u, v, max u v, v} J) :
    StackOver J :=
  ⟨FibredCategoryOver.absoluteInertiaOver Y.toFibredCategoryOver,
    absoluteInertiaOfStack_isStackOnSite (J := J) Y⟩

/-- The canonical morphism on absolute inertia induced by a morphism from a fibred category to a
stack over `(C, J)`. -/
noncomputable abbrev absoluteInertiaMap
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {Y : StackOver.{u, v, max u v, v} J} (F : X ⟶ Y) :
    FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver :=
  show FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver
    from
      FibredCategoryMor.ofBasedFunctor
        (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F))
        (absoluteInertiaOverMap_preservesStronglyCartesian F)

/-- Helper for Chap08 Lemma 8 8 5: the absolute-to-diagonal comparison has the source inertia
automorphism as its left comparison component. -/
private theorem absoluteToDiagonal_obj_comparison_a
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (((FibredCategoryMor.toFunctor (absoluteToDiagonal (J := J) X)).obj A).comparison).a =
      A.α.hom := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the absolute-to-diagonal comparison has identity as its
right comparison component. -/
private theorem absoluteToDiagonal_obj_comparison_b
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (((FibredCategoryMor.toFunctor (absoluteToDiagonal (J := J) X)).obj A).comparison).b =
      𝟙 A.x := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw forward inertia-to-diagonal object has source object
as its left endpoint. -/
private theorem absoluteToDiagonalBased_obj_fst
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A)).obj.fst.1) = A.x := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw forward inertia-to-diagonal object has source object
as its right endpoint. -/
private theorem absoluteToDiagonalBased_obj_snd
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A)).obj.snd.1) = A.x := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw forward inertia-to-diagonal object stores the
inertia automorphism as its left comparison component. -/
private theorem absoluteToDiagonalBased_obj_comparison_a
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (ExplicitTwoFibreProductObject.comparison
      (FibredCategoryMor.toBasedFunctor (relativeDiagonalFibredMap (J := J) X))
      (FibredCategoryMor.toBasedFunctor (relativeDiagonalFibredMap (J := J) X))
      ((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A))).a = A.α.hom := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw forward inertia-to-diagonal object stores identity as
its right comparison component. -/
private theorem absoluteToDiagonalBased_obj_comparison_b
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (ExplicitTwoFibreProductObject.comparison
      (FibredCategoryMor.toBasedFunctor (relativeDiagonalFibredMap (J := J) X))
      (FibredCategoryMor.toBasedFunctor (relativeDiagonalFibredMap (J := J) X))
      ((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A))).b = 𝟙 A.x := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw Chapter 4 spelling of the comparison has the inertia
automorphism as its left component. -/
private theorem relativeInertiaToDiagonalPullback_obj_comparison_a
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (ExplicitTwoFibreProductObject.comparison
      (toBaseBasedFunctor (J := J) X).relativeDiagonalOver
      (toBaseBasedFunctor (J := J) X).relativeDiagonalOver
      ((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A))).a = A.α.hom := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the raw Chapter 4 spelling of the comparison has identity as
its right component. -/
private theorem relativeInertiaToDiagonalPullback_obj_comparison_b
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (ExplicitTwoFibreProductObject.comparison
      (toBaseBasedFunctor (J := J) X).relativeDiagonalOver
      (toBaseBasedFunctor (J := J) X).relativeDiagonalOver
      ((toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
        (relativeInertiaBaseLiftUpObj X.p A))).b = 𝟙 A.x := by
  cases A
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the absolute-to-diagonal comparison sends a morphism to its
underlying arrow on the left endpoint. -/
private theorem absoluteToDiagonal_map_a
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    {A B : (FibredCategoryOver.absoluteInertiaOver X).S} (φ : A ⟶ B) :
    ((FibredCategoryMor.toFunctor (absoluteToDiagonal (J := J) X)).map φ).a = φ.φ := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the absolute-to-diagonal comparison sends a morphism to its
underlying arrow on the right endpoint. -/
private theorem absoluteToDiagonal_map_b
    (X : FibredCategoryOver.{u, v, max u v, v} C)
    {A B : (FibredCategoryOver.absoluteInertiaOver X).S} (φ : A ⟶ B) :
    ((FibredCategoryMor.toFunctor (absoluteToDiagonal (J := J) X)).map φ).b = φ.φ := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the induced absolute-inertia map has the expected underlying
arrow in the target fibred category. -/
private theorem absoluteInertiaOverMap_map_hom
    {X Y : FibredCategoryOver.{u, v, max u v, v} C} (F : X ⟶ Y)
    {A B : (FibredCategoryOver.absoluteInertiaOver X).S} (φ : A ⟶ B) :
    ((absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F)).map φ).φ =
      (FibredCategoryMor.toFunctor F).map φ.φ := by
  simpa [CategoryOver.absoluteInertiaOverMap, FibredCategoryOver.absoluteInertiaOver,
    CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver] using
    (relativeInertiaMap_map_hom (F₁ := FibredCategoryMor.toFunctor F)
      (F₂ := FibredCategoryMor.toFunctor F) (p' := Y.p)
      (comm := eqToIso (FibredCategoryMor.toBasedFunctor F).w) φ)

/-- Helper for Chap08 Lemma 8 8 5: the absolute-inertia comparison agrees with the diagonal
model on objects. -/
private theorem absoluteInertiaMap_comp_absoluteToDiagonal_obj
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X')
    (A : (FibredCategoryOver.absoluteInertiaOver X).S) :
    (FibredCategoryMor.toFunctor
        ((absoluteInertiaMap i) ≫ (absoluteToDiagonal X'.toFibredCategoryOver))).obj A =
      (FibredCategoryMor.toFunctor (absoluteToDiagonal X ≫ diagonalInertiaModelMap i)).obj A := by
  -- The endpoints agree directly; the comparison component is the naturality comparison for the
  -- diagonal map applied to the Chapter 4 inertia-to-diagonal object.
  apply explicitTwoFibreProductObject_ext_underlying
  · exact Functor.congr_obj (FibredCategoryMor.comm i) A.x
  · rfl
  · rfl
  · dsimp [absoluteInertiaMap, absoluteToDiagonal, absoluteToDiagonalBased, diagonalInertiaModelMap]
    apply heq_of_eq
    cases A with
    | mk x α hα =>
      erw [twoFibreProductOfStackificationsHom_obj_comparison]
      let A₀ : (FibredCategoryOver.absoluteInertiaOver X).S :=
        { x := x, α := α, map_hom_eq_id := hα }
      let P :=
        (toBaseBasedFunctor (J := J) X).relativeInertiaToDiagonalPullback.obj
          (relativeInertiaBaseLiftUpObj X.p A₀)
      let θ := FibredCategoryMor.basedFunctorIsoOfOwnerIso (diagonalNaturalityIso (J := J) i)
      apply ExplicitTwoFibreProductHom.ext
      · change (FibredCategoryMor.toFunctor i).map α.hom = _
        change (FibredCategoryMor.toFunctor i).map α.hom =
          (θ.hom.app P.obj.fst.1).a ≫
            (((FibredCategoryMor.toFunctor (basePairMap (J := J) i)).map P.comparison).a ≫
              (θ.inv.app P.obj.snd.1).a)
        rw [diagonalNaturalityIso_hom_app_a (J := J) i P.obj.fst.1]
        rw [diagonalNaturalityIso_inv_app_a (J := J) i P.obj.snd.1]
        rw [twoFibreProductOfStackificationsHom_map_a]
        rw [relativeInertiaToDiagonalPullback_obj_comparison_a (J := J) X A₀]
        erw [Category.id_comp]
        erw [Category.comp_id]
        rfl
      · change 𝟙 ((FibredCategoryMor.toFunctor i).obj x) = _
        change 𝟙 ((FibredCategoryMor.toFunctor i).obj x) =
          (θ.hom.app P.obj.fst.1).b ≫
            (((FibredCategoryMor.toFunctor (basePairMap (J := J) i)).map P.comparison).b ≫
              (θ.inv.app P.obj.snd.1).b)
        rw [diagonalNaturalityIso_hom_app_b (J := J) i P.obj.fst.1]
        rw [diagonalNaturalityIso_inv_app_b (J := J) i P.obj.snd.1]
        rw [twoFibreProductOfStackificationsHom_map_b]
        rw [relativeInertiaToDiagonalPullback_obj_comparison_b (J := J) X A₀]
        erw [Category.id_comp]
        erw [Functor.map_id]
        erw [Category.comp_id]
        rfl

/-- Helper for Chap08 Lemma 8 8 5: the absolute-inertia comparison agrees with the diagonal
model after forgetting to ordinary functors. -/
private theorem absoluteInertiaMap_comp_absoluteToDiagonal_toFunctor_eq
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    FibredCategoryMor.toFunctor
        ((absoluteInertiaMap i) ≫ (absoluteToDiagonal X'.toFibredCategoryOver)) =
      FibredCategoryMor.toFunctor (absoluteToDiagonal X ≫ diagonalInertiaModelMap i) := by
  -- Object equality is isolated so the morphism branch can use it as transport data.
  refine Functor.hext (fun A ↦ absoluteInertiaMap_comp_absoluteToDiagonal_obj i A) ?_
  · intro A B φ
    refine explicitTwoFibreProductHom_heq_of_components
      (absoluteInertiaMap_comp_absoluteToDiagonal_obj i A)
      (absoluteInertiaMap_comp_absoluteToDiagonal_obj i B) _ _ ?_ ?_
    · apply heq_of_eq
      erw [absoluteToDiagonal_map_a]
    · apply heq_of_eq
      erw [absoluteToDiagonal_map_b]

/-- Helper for Chap08 Lemma 8 8 5: postcomposing the absolute-inertia map with the forward
comparison agrees with first comparing the source to the diagonal model and then applying the
diagonal-model map. -/
private theorem absoluteInertiaMap_comp_absoluteToDiagonal_eq
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    (absoluteInertiaMap i) ≫ (absoluteToDiagonal X'.toFibredCategoryOver) =
      absoluteToDiagonal X ≫ diagonalInertiaModelMap i := by
  -- Route correction: compare only after forward postcomposition with the Chapter 4 map; this
  -- avoids inverse transport across the diagonal-pullback equivalence.
  -- The remaining work is isolated in the ordinary-functor comparison helper.
  exact fibredCategoryMor_eq_of_toFunctor_eq
    (absoluteInertiaMap_comp_absoluteToDiagonal_toFunctor_eq i)

/-- Helper for Chap08 Lemma 8 8 5: owner-isomorphism form of the forward naturality comparison
for absolute inertia. -/
private noncomputable abbrev absoluteInertiaMap_comp_absoluteToDiagonal_iso
    {X : FibredCategoryOver.{u, v, max u v, v} C}
    {X' : StackOver.{u, v, max u v, v} J} (i : X ⟶ X') :
    (absoluteInertiaMap i) ≫ (absoluteToDiagonal X'.toFibredCategoryOver) ≅
      absoluteToDiagonal X ≫ diagonalInertiaModelMap i :=
  eqToIso (absoluteInertiaMap_comp_absoluteToDiagonal_eq i)

-- Proof sketch: use Lemma `4.34.1` to identify absolute inertia with a `2`-fibre-product
-- construction, then apply Lemma `8.8.4` to the stackification morphism `i : X ⟶ X'`. Lemma
-- `8.7.1` supplies the canonical stack structure on the absolute inertia of the stack `X'`,
-- yielding the desired stackification statement for the induced inertia morphism.
/-- Chap08 Lemma 8 8 5: if `i : X ⟶ X'` exhibits the stack `X'` as a stackification of the fibred
category `X` over the site `(C, J)`, then the induced morphism on absolute inertia exhibits the
absolute inertia of `X'` as a stackification of the absolute inertia of `X`. -/
@[stacks 06NS]
theorem absoluteInertia_of_stackification_isStackification
    {X : FibredCategoryOver C} {X' : StackOver J}
    (i : X ⟶ X')
    (hi : FibredCategoryMor.IsStackification i) :
    FibredCategoryMor.IsStackification (absoluteInertiaMap i) := by
  -- Route correction: prove stackification after forward comparison to the diagonal-pullback
  -- model, then cancel the target equivalence over the base.
  have hDiagonal : FibredCategoryMor.IsStackification (diagonalInertiaModelMap i) :=
    diagonalInertiaModelMap_isStackification i hi
  have hPre : FibredCategoryMor.IsStackification
      (absoluteToDiagonal X ≫ diagonalInertiaModelMap i) :=
    isStackification_comp_left_of_isEquivalenceOverBase
      (absoluteToDiagonal X) (absoluteToDiagonal_isEquivalenceOverBase X)
      (diagonalInertiaModelMap i) hDiagonal
  have hPost : FibredCategoryMor.IsStackification
      ((absoluteInertiaMap i) ≫ absoluteToDiagonal X'.toFibredCategoryOver) :=
    isStackification_of_ownerIso
      (absoluteInertiaMap_comp_absoluteToDiagonal_iso i).symm hPre
  exact
    isStackification_of_comp_right_isEquivalenceOverBase
      (D := absoluteInertiaOfStack X') (E := absoluteDiagonalStack X')
      (absoluteInertiaMap i) (absoluteToDiagonal X'.toFibredCategoryOver)
      (absoluteToDiagonal_isEquivalenceOverBase X'.toFibredCategoryOver) hPost

end CategoryTheory
