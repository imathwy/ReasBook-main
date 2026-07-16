import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_33_9
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

universe v vS u w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory

/-
Domain-style sampling for Definition 4.35.6:
- primary domain: categories fibred in groupoids over a fixed base and their morphisms over that
  base.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `FibredCategoryOver`,
  `FibredCategoryMor`,
  `SubTwoCategory`.
- best owner abstraction: the object owner is the full sub-`2`-category of
  `FibredCategoryOver C` cut out by `IsFibredInGroupoids X.p`.
- primitive data: a fibred category over `C` together with the proof that its projection is
  fibred in groupoids.
- derived API: the forgetful views to `FibredCategoryOver C`, `CategoryOver C`, and
  `BasedCategory C`, together with the source-facing morphism type of based functors over `C`;
  the ambient `FibredCategoryMor` is recovered canonically because strong-cartesian preservation
  is automatic in the fibred-in-groupoids case.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver C` and its owner homs `X ⟶ Y`;
- `core/canonical`: `fibredInGroupoidsOverSubTwoCategory C`, `FibredCategoryOver`,
  the ambient owner homs in `FibredCategoryOver C`, and `IsFibredInGroupoids`;
- `bridge/view`: the forgetful coercions to `FibredCategoryOver C`, `CategoryOver C`,
  `BasedCategory C`, the stable chapter alias `FibredInGroupoidsMor X Y`, and the coercion to
  the ambient `FibredCategoryMor`.

Primitive-vs-derived split:
- primitive data: the ambient fibred-category object together with the groupoid condition on its
  projection;
- derived API: the short object projections, the source-facing morphism view by based functors,
  and the ambient fibred-category-morphism coercion. -/

/-- Definition 4.35.6 at the owner level: categories fibred in groupoids over `C` form the full
sub-`2`-category of `FibredCategoryOver C` cut out by the fibred-in-groupoids condition. -/
abbrev fibredInGroupoidsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredCategoryOver C) where
  obj := fun X ↦ IsFibredInGroupoids X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

variable {C : Type u} [Category.{v} C]

/-- The identity functor of `C` is strongly cartesian over `C`. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

instance : IsFibredInGroupoids (𝟭 C) where
  toIsFibered := by
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro a R f
    exact ⟨R, f, idFunctor_isStronglyCartesian f⟩
  isStronglyCartesian_map φ := idFunctor_isStronglyCartesian φ

/-- Definition 4.35.6: the objects of the `2`-category of categories fibred in groupoids over `C`
are the objects of the canonical owner sub-`2`-category
`fibredInGroupoidsOverSubTwoCategory C`. -/
abbrev FibredInGroupoidsOver (C : Type u) [Category.{v} C] :=
  (fibredInGroupoidsOverSubTwoCategory C).Obj

namespace FibredInGroupoidsOver

/-- The slice projection `Over.forget X : Over X ⥤ C` is fibred in groupoids. -/
instance (X : C) : IsFibredInGroupoids (Over.forget X) := by
  sorry

/-- Build a bundled category fibred in groupoids over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredInGroupoidsOver C :=
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [fibredInGroupoidsOverSubTwoCategory, FibredCategoryOver.p, FibredCategoryOver.ofFunctor]
      using (inferInstance : IsFibredInGroupoids p)⟩

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInGroupoidsOver C) : FibredCategoryOver C :=
  X.obj

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInGroupoidsOver C) : CategoryOver C :=
  X.toFibredCategoryOver.toCategoryOver

/-- The total category of a bundled category fibred in groupoids over `C`. -/
abbrev S (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.S

/-- The projection functor of a bundled category fibred in groupoids over `C`. -/
abbrev p (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.p

/-- Forget a bundled category fibred in groupoids over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInGroupoidsOver C) : BasedCategory C :=
  X.toFibredCategoryOver.toBasedCategory

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInGroupoidsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in groupoids over `C` is fibred in
groupoids. -/
instance (X : FibredInGroupoidsOver C) : IsFibredInGroupoids X.p :=
  X.property

/-- The projection functor of a bundled category fibred in groupoids over `C` is fibred. -/
instance (X : FibredInGroupoidsOver C) : X.p.IsFibered :=
  X.property.toIsFibered

end FibredInGroupoidsOver

instance : Bicategory (FibredInGroupoidsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInGroupoidsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInGroupoidsOver C) :=
  SubTwoCategory.strictObj (fibredInGroupoidsOverSubTwoCategory C)

instance fibredInGroupoidsOverCategory : Category (FibredInGroupoidsOver C) :=
  StrictBicategory.category (FibredInGroupoidsOver C)

/-- Definition 4.35.6: `FibredInGroupoidsMor X Y` is the stable chapter vocabulary for the owner
hom `X ⟶ Y` in the full sub-`2`-category of fibred categories over `C` cut out by the
fibred-in-groupoids condition. Since this sub-`2`-category is full on `1`-morphisms, the ambient
canonical `FibredCategoryMor` API is recovered by thin coercion and bridge declarations. -/
abbrev FibredInGroupoidsMor (X Y : FibredInGroupoidsOver C) :=
  X ⟶ Y

namespace FibredInGroupoidsMor

variable {X Y : FibredInGroupoidsOver C}

/-- In a category fibred in groupoids every based functor over `C` preserves strongly cartesian
morphisms, so it canonically defines an ambient morphism of fibred categories. -/
private theorem preservesStronglyCartesian
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    G.PreservesStronglyCartesian := by
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids Y.p).isStronglyCartesian_map (G.map φ)

/-- A morphism of categories fibred in groupoids over `C` is canonically viewed as the
corresponding ambient `1`-morphism of fibred categories over `C`. -/
instance : CoeOut (FibredInGroupoidsMor X Y)
    (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) where
  coe F := F.toHom

/-- The underlying based functor of a morphism of categories fibred in groupoids over `C`. -/
abbrev toBasedFunctor (F : FibredInGroupoidsMor X Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredCategoryMor.toBasedFunctor F.toHom

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : FibredInGroupoidsMor X Y) (U : C) :=
  F.toBasedFunctor.fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : FibredInGroupoidsMor X Y) : X.S ⥤ Y.S :=
  F.toBasedFunctor.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : FibredInGroupoidsMor X Y) : F.G ⋙ Y.p = X.p :=
  F.toBasedFunctor.w

/-- Compatibility coercion from owner homs to based functors over `C`. -/
instance : CoeOut (FibredInGroupoidsMor X Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := F.toBasedFunctor

/-- Build a morphism of categories fibred in groupoids over `C` from a based functor over `C`.
This is the thin bridge from the owner-selected homs to the ambient `BasedFunctor` API. -/
abbrev ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FibredInGroupoidsMor X Y :=
  ⟨FibredCategoryMor.ofBasedFunctor G (preservesStronglyCartesian G), trivial⟩

/-- A morphism of categories fibred in groupoids over `C` is an equivalence over the base if its
underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : FibredInGroupoidsMor X Y) : Prop :=
  FibredCategoryMor.IsEquivalenceOverBase F.toHom

private noncomputable def fibredCategoryMorIsoOfBasedFunctorIso
    {F G : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G := by
  let hom : F.obj ⟶ G.obj := ObjectProperty.homMk e.hom
  let inv : G.obj ⟶ F.obj := ObjectProperty.homMk e.inv
  refine ⟨⟨hom, trivial⟩, ⟨inv, trivial⟩, ?_, ?_⟩
  · apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact e.hom_inv_id
  · apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact e.inv_hom_id

private noncomputable def ownerIsoOfFibredCategoryMorIso
    {F G : FibredInGroupoidsMor X Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G := by
  let e' : F.obj ≅ G.obj :=
    ObjectProperty.isoMk
      (show ObjectProperty (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) from
        ((fibredInGroupoidsOverSubTwoCategory C).hom X Y).obj)
      (show F.obj.obj ≅ G.obj.obj from e)
  exact CategoryTheory.isoMk e' trivial trivial

private noncomputable def ownerIsoOfBasedFunctorIso
    {F G : FibredInGroupoidsMor X Y} (e : F.toBasedFunctor ≅ G.toBasedFunctor) :
    F ≅ G :=
  ownerIsoOfFibredCategoryMorIso (fibredCategoryMorIsoOfBasedFunctorIso e)

/-- Convert an isomorphism between the ambient fibred-category morphisms underlying `F` and `G`
into an isomorphism of morphisms of categories fibred in groupoids. -/
noncomputable def ofFibredCategoryMorIso
    {F G : FibredInGroupoidsMor X Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  ownerIsoOfFibredCategoryMorIso e

noncomputable def basedFunctorIsoOfOwnerIso
    {F G : FibredInGroupoidsMor X Y} (e : F ≅ G) :
    F.toBasedFunctor ≅ G.toBasedFunctor :=
  Functor.mapIso
    (((fibredCategoryOverSubTwoCategory C).hom X.toFibredCategoryOver Y.toFibredCategoryOver).inclusion)
    (Functor.mapIso (((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion) e)

/- A morphism of categories fibred in groupoids over `C` that is an equivalence over the base
determines a bicategorical equivalence. -/
noncomputable def toEquivalence
    (F : FibredInGroupoidsMor X Y) [FibredInGroupoidsMor.IsEquivalenceOverBase F] :
    Bicategory.Equivalence X Y :=
  let e : BasedFunctor.EquivalenceOverBase F.toBasedFunctor :=
    Classical.choice (show Nonempty (BasedFunctor.EquivalenceOverBase F.toBasedFunctor) from
      BasedFunctor.IsEquivalenceOverBase.nonempty)
  let G : FibredInGroupoidsMor Y X := ofBasedFunctor e.inverse
  let eta : (𝟙 X : FibredInGroupoidsMor X X) ≅ F ≫ G :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.unitIso
  let eps : G ≫ F ≅ (𝟙 Y : FibredInGroupoidsMor Y Y) :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.counitIso
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}

/-- The canonical morphism from a category fibred in groupoids over `C` to the base identity
functor. -/
abbrev baseProjection (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsMor X (ofFunctor (𝟭 C)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := X.p
      w := Functor.comp_id X.p }

/- The `1`-morphism underlying a bicategorical equivalence of categories fibred in groupoids over
`C` is an equivalence over the base. -/
theorem hom_isEquivalenceOverBase
    (e : Bicategory.Equivalence X Y) :
    FibredInGroupoidsMor.IsEquivalenceOverBase e.hom := by
  let hHom : FibredInGroupoidsMor X Y := e.hom
  let hInv : FibredInGroupoidsMor Y X := e.inv
  change BasedFunctor.IsEquivalenceOverBase hHom.toBasedFunctor
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      hInv.toBasedFunctor
      (by
        change (𝟙 X.toBasedCategory) ≅ (hHom.toBasedFunctor ⋙ hInv.toBasedFunctor)
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.unit)
      (by
        change (hInv.toBasedFunctor ⋙ hHom.toBasedFunctor) ≅ 𝟙 Y.toBasedCategory
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit)

end FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}
variable (F G : FibredInGroupoidsMor X Y)

/- Definition 4.35.6: a `2`-morphism between `1`-morphisms of categories fibred in groupoids
over `C` is the inherited morphism in the ambient hom-category of fibred categories over `C`. -/
#check (F ⟶ G)

end CategoryTheory
