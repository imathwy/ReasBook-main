import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_35_6 (from Chap04) -/
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

/-- Definition 4.35.6 (1): at the owner level, categories fibred in groupoids over `C` form the full
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

/-- Definition 4.35.6 (2): the objects of the `2`-category of categories fibred in groupoids over `C`
are the objects of the canonical owner sub-`2`-category
`fibredInGroupoidsOverSubTwoCategory C`. -/
abbrev FibredInGroupoidsOver (C : Type u) [Category.{v} C] :=
  (fibredInGroupoidsOverSubTwoCategory C).Obj

namespace FibredInGroupoidsOver

/-- Helper for Definition 4.35.6: a slice morphism built with `Over.homMk` is a hom-lift for the
projection `Over.forget X`. -/
private theorem over_homMk_isHomLift {X : C} {a c : Over X}
    (g : c.left ⟶ a.left) (w : g ≫ a.hom = c.hom) :
    (Over.forget X).IsHomLift g (Over.homMk g w) := by
  -- The forgetful functor remembers exactly the underlying arrow in `C`.
  refine IsHomLift.of_fac' (Over.forget X) g (Over.homMk g w) rfl rfl ?_
  simp

/-- Helper for Definition 4.35.6: every morphism in `Over X` is strongly cartesian for the slice
projection `Over.forget X`. -/
private theorem over_hom_isStronglyCartesian {X : C} {a b : Over X} (φ : a ⟶ b) :
    (Over.forget X).IsStronglyCartesian φ.left φ where
  toIsHomLift := by
    -- A slice morphism lies over its underlying arrow by definition.
    refine IsHomLift.of_fac' (Over.forget X) φ.left φ rfl rfl ?_
    simp
  universal_property' := by
    intro c g φ' hφ'
    -- The competing lift is determined by its underlying arrow in `C`.
    have hbase : g ≫ φ.left = φ'.left := by
      exact
        @IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget X) _ _ (g ≫ φ.left) φ' hφ'
    have hw : g ≫ a.hom = c.hom := by
      -- Route correction: reduce the slice commutativity constraint to underlying arrows.
      have hga : g ≫ a.hom = (g ≫ φ.left) ≫ b.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) (Over.w φ).symm
      have hbase_comp : (g ≫ φ.left) ≫ b.hom = φ'.left ≫ b.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ t ≫ b.hom) hbase
      have hφ'comm : φ'.left ≫ b.hom = c.hom := by
        simpa using Over.w φ'
      exact hga.trans (hbase_comp.trans hφ'comm)
    let χ : c ⟶ a := Over.homMk g hw
    have hχfac : χ ≫ φ = φ' := by
      -- Equality of slice morphisms is equality of their underlying arrows.
      apply Over.OverMorphism.ext
      simpa [χ] using hbase
    refine ⟨χ, ⟨over_homMk_isHomLift g hw, hχfac⟩, ?_⟩
    intro π hπ
    -- Any other candidate must have the same underlying arrow, hence is the same slice morphism.
    apply Over.OverMorphism.ext
    have hπleft : π.left = g := by
      simpa using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget X) _ _ g π hπ.1).symm
    simpa [χ] using hπleft

/-- Helper for Definition 4.35.6: the slice projection `Over.forget X` is fibered. -/
private theorem over_forget_isFibered (X : C) : (Over.forget X).IsFibered := by
  -- Choose the textbook pullback object `f ≫ a.hom : R ⟶ X` and its tautological map to `a`.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro a R f
  let c : Over X := Over.mk (f ≫ a.hom)
  let φ : c ⟶ a := Over.homMk f (show f ≫ a.hom = c.hom by rfl)
  refine ⟨c, φ, ?_⟩
  simpa [c, φ] using over_hom_isStronglyCartesian (X := X) φ

/-- The slice projection `Over.forget X : Over X ⥤ C` is fibred in groupoids. -/
instance (X : C) : IsFibredInGroupoids (Over.forget X) := by
  -- The slice projection is fibered by explicit pullbacks, and every slice arrow is strongly
  -- cartesian because its universal property is controlled by the underlying arrow in `C`.
  refine
    { toIsFibered := over_forget_isFibered X
      isStronglyCartesian_map := fun φ ↦ ?_ }
  simpa using over_hom_isStronglyCartesian (X := X) φ

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

/-- The projection of a bundled category fibred in groupoids is fibred in groupoids. -/
-- Proof sketch: this is exactly the property field of an object of the owner full
-- sub-`2`-category after unfolding the projection abbreviation.
theorem p_isFibredInGroupoids (X : FibredInGroupoidsOver C) :
    IsFibredInGroupoids X.p :=
  X.property

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
  p_isFibredInGroupoids X

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

instance fibredInGroupoidsOverHom₂IsMultiplicative
    (X Y : FibredInGroupoidsOver C) :
    ((fibredInGroupoidsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInGroupoidsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInGroupoidsOverHomInclusionFull
    (X Y : FibredInGroupoidsOver C) :
    (((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance fibredInGroupoidsOverHomWideInclusionFull
    (X Y : FibredInGroupoidsOver C) :
    (wideSubcategoryInclusion ((fibredInGroupoidsOverSubTwoCategory C).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

/-- Definition 4.35.6 (3): `FibredInGroupoidsMor X Y` is the stable chapter vocabulary for the owner
hom `X ⟶ Y` in the full sub-`2`-category of fibred categories over `C` cut out by the
fibred-in-groupoids condition. Since this sub-`2`-category is full on `1`-morphisms, the ambient
canonical `FibredCategoryMor` API is recovered by thin coercion and bridge declarations; the
public theorem surface below uses the owner notation `X ⟶ Y` directly. -/
abbrev FibredInGroupoidsMor (X Y : FibredInGroupoidsOver C) :=
  X ⟶ Y

namespace FibredInGroupoidsMor

variable {X Y : FibredInGroupoidsOver C}

/-- Regard an ambient morphism of the underlying fibred categories over `C` as the corresponding
owner hom in `FibredInGroupoidsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :
    X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- In a category fibred in groupoids every based functor over `C` preserves strongly cartesian
morphisms, so it canonically defines an ambient morphism of fibred categories. -/
private theorem preservesStronglyCartesian
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    G.PreservesStronglyCartesian := by
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids Y.p).isStronglyCartesian_map (G.map φ)

/-- The ambient fibred-category morphism underlying an owner hom in
`FibredInGroupoidsOver C`. -/
abbrev toFibredCategoryMor (F : X ⟶ Y) :
    X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver :=
  F.toHom

/-- A morphism of categories fibred in groupoids over `C` is canonically viewed as the
corresponding ambient `1`-morphism of fibred categories over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) where
  coe F := FibredInGroupoidsMor.toFibredCategoryMor F

/-- The underlying based functor of a morphism of categories fibred in groupoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredCategoryMor.toBasedFunctor (FibredInGroupoidsMor.toFibredCategoryMor F)

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  FibredInGroupoidsMor.toBasedFunctor F |>.fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  FibredInGroupoidsMor.toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : FibredInGroupoidsMor.G F ⋙ Y.p = X.p :=
  FibredInGroupoidsMor.toBasedFunctor F |>.w

/-- Compatibility coercion from owner homs to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := FibredInGroupoidsMor.toBasedFunctor F

/-- Build a morphism of categories fibred in groupoids over `C` from a based functor over `C`.
This is the thin bridge from the owner-selected homs to the ambient `BasedFunctor` API. -/
abbrev ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  ⟨FibredCategoryMor.ofBasedFunctor G (preservesStronglyCartesian G), trivial⟩

/-- A morphism of categories fibred in groupoids over `C` is an equivalence over the base if its
underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : FibredInGroupoidsMor X Y) : Prop :=
  FibredCategoryMor.IsEquivalenceOverBase (FibredInGroupoidsMor.toFibredCategoryMor F)

private noncomputable def fibredCategoryMorIsoOfBasedFunctorIso
    {F G : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Convert an isomorphism between the ambient fibred-category morphisms underlying `F` and `G`
into an isomorphism of morphisms of categories fibred in groupoids. -/
noncomputable def ofFibredCategoryMorIso
    {F G : X ⟶ Y}
    (e : FibredInGroupoidsMor.toFibredCategoryMor F ≅
      FibredInGroupoidsMor.toFibredCategoryMor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

noncomputable def ownerIsoOfBasedFunctorIso
    {F G : X ⟶ Y}
    (e : FibredInGroupoidsMor.toBasedFunctor F ≅ FibredInGroupoidsMor.toBasedFunctor G) :
    F ≅ G :=
  ofFibredCategoryMorIso (fibredCategoryMorIsoOfBasedFunctorIso e)

noncomputable def basedFunctorIsoOfOwnerIso
    {F G : X ⟶ Y} (e : F ≅ G) :
    FibredInGroupoidsMor.toBasedFunctor F ≅ FibredInGroupoidsMor.toBasedFunctor G :=
  Functor.mapIso
    (((fibredCategoryOverSubTwoCategory C).hom X.toFibredCategoryOver Y.toFibredCategoryOver).inclusion)
    (Functor.mapIso (((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion) e)

/-- Explicit equivalence-over-base data on the underlying based functor of `F` induce a
bicategorical equivalence with forward morphism `F`. -/
noncomputable def ofEquivalenceOverBase
    (F : X ⟶ Y)
    (e : BasedFunctor.EquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor F)) :
    Bicategory.Equivalence X Y :=
  let e : BasedFunctor.EquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor F) :=
    e
  let G : Y ⟶ X := ofBasedFunctor e.inverse
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.unitIso
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.counitIso
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

/-- A morphism of categories fibred in groupoids over `C` that is an equivalence over the base
admits a bicategorical equivalence with forward morphism `F`. -/
theorem exists_equivalence
    (F : X ⟶ Y) (hF : FibredInGroupoidsMor.IsEquivalenceOverBase F) :
    ∃ e : Bicategory.Equivalence X Y, e.hom = F := by
  rcases hF.nonempty with ⟨e⟩
  exact ⟨ofEquivalenceOverBase F e, rfl⟩

/-- A morphism of categories fibred in groupoids over `C` that is an equivalence over the base
admits an explicit inverse morphism together with unit and counit isomorphisms. -/
theorem exists_inverse
    (F : X ⟶ Y) (hF : FibredInGroupoidsMor.IsEquivalenceOverBase F) :
    ∃ G : Y ⟶ X,
      Nonempty ((𝟙 X : X ⟶ X) ≅ F ≫ G) ∧
        Nonempty (G ≫ F ≅ (𝟙 Y : Y ⟶ Y)) := by
  rcases hF.nonempty with ⟨e⟩
  refine ⟨ofBasedFunctor e.inverse, ?_, ?_⟩
  · refine ⟨?_⟩
    change (𝟙 X : X ⟶ X) ≅ F ≫ (ofBasedFunctor e.inverse : Y ⟶ X)
    exact ownerIsoOfBasedFunctorIso e.unitIso
  · refine ⟨?_⟩
    change ((ofBasedFunctor e.inverse : Y ⟶ X) ≫ F) ≅ (𝟙 Y : Y ⟶ Y)
    exact ownerIsoOfBasedFunctorIso e.counitIso

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}

/-- The canonical morphism from a category fibred in groupoids over `C` to the base identity
functor. -/
abbrev baseProjection (X : FibredInGroupoidsOver C) :
    X ⟶ ofFunctor (𝟭 C) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := X.p
      w := Functor.comp_id X.p }

/- The `1`-morphism underlying a bicategorical equivalence of categories fibred in groupoids over
`C` is an equivalence over the base. -/
theorem hom_isEquivalenceOverBase
    (e : Bicategory.Equivalence X Y) :
    FibredInGroupoidsMor.IsEquivalenceOverBase e.hom := by
  let hHom : X ⟶ Y := e.hom
  let hInv : Y ⟶ X := e.inv
  change BasedFunctor.IsEquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor hHom)
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      (FibredInGroupoidsMor.toBasedFunctor hInv)
      (by
        change (𝟙 X.toBasedCategory) ≅
            (FibredInGroupoidsMor.toBasedFunctor hHom ⋙
              FibredInGroupoidsMor.toBasedFunctor hInv)
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.unit)
      (by
        change
          (FibredInGroupoidsMor.toBasedFunctor hInv ⋙
              FibredInGroupoidsMor.toBasedFunctor hHom) ≅
            𝟙 Y.toBasedCategory
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit)

end FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}
variable (F G : X ⟶ Y)

/- Definition 4.35.6 (4): a `2`-morphism between `1`-morphisms of categories fibred in groupoids
over `C` is the inherited morphism in the ambient hom-category of fibred categories over `C`. -/
#check (F ⟶ G)

end CategoryTheory

/-! ### Definition_4_35_6_tmpNNZm (from Chap04) -/
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

/-! ### Lemma_4_35_7 (from Chap04) -/
universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.35.7:
- primary domain: categories fibred in groupoids over a fixed base and their `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `FibredInGroupoidsOver`,
  `FibredInGroupoidsMor`,
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `FibredCategoryOver.twoFibreProductLeftProjection`,
  `FibredCategoryOver.twoFibreProductRightProjection`,
  `explicitTwoFibreProduct`;
- best owner abstraction: the source-facing statement for this item should live at the owner level
  `FibredInGroupoidsOver C`, with the canonical square and its `Bicategory.IsFinal` universal
  property obtained by restricting the ambient owner
  `FibredCategoryOver.twoFibreProductSquare`; the explicit pullback projection in `Cat/C` is the
  companion closure theorem feeding that owner-level statement.

Primitive-vs-derived split:
- primitive source-facing data: the based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` over `C`,
  with fibred-in-groupoids hypotheses on the source projections and fibredness of the target
  projection;
- derived API: the bundled owner-level rebundling
  `FibredInGroupoidsOver.twoFibreProduct`, its two projections, the canonical square
  `FibredInGroupoidsOver.twoFibreProductSquare`, and the resulting
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`, all obtained by restricting the
  ambient owner `FibredCategoryOver.twoFibreProductSquare` to the full sub-`2`-category
  `FibredInGroupoidsOver C`.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver.twoFibreProductSquare` and
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `IsFibredInGroupoids` on the explicit pullback projection in `Cat/C`;
- `bridge/view`: `explicitTwoFibreProductProjection_isFibredInGroupoids` and the owner-level
  rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

section Raw

variable {X Y S : BasedCategory.{v, max u v} C}

/-- Helper for Lemma 4.35.7: the categorical pullback of two groupoids is again a groupoid. -/
private theorem categorical_pullback_isGroupoid
    {A B T : Type*} [Category A] [Category B] [Category T]
    (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid A] [IsGroupoid B] :
    IsGroupoid (Limits.CategoricalPullback L R) where
  all_isIso := fun f ↦
    (Limits.CategoricalPullback.isIso_iff (F := L) (G := R) f).2
      ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 4.35.7: each fiber of the explicit `2`-fibre product is equivalent to the
categorical pullback of the source fibers, hence is a groupoid. -/
private theorem explicit_two_fibre_product_fiber_isGroupoid
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    (U : C) :
    IsGroupoid ((explicitTwoFibreProduct F G).p.Fiber U) := by
  -- Transport the fiber across the canonical equivalence from Lemma 4.32.5.
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F G U
  -- The pullback model is a groupoid because both source fibers are groupoids.
  letI : IsGroupoid (Limits.CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :=
    categorical_pullback_isGroupoid (F.fiberFunctor U) (G.fiberFunctor U)
  exact isGroupoid_of_reflects_iso e.functor

-- Proof sketch: apply Lemma `4.33.10` to the same explicit `2`-fibre-product model from
-- Lemma `4.32.3` using only that the target projection is fibred, then use Lemma `4.35.2` to
-- reduce the remaining work to checking that every fiber is a groupoid.
/-- Lemma 4.35.7 (1): if `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` are based functors over `C` whose source
categories are fibred in groupoids and whose target category is fibred in groupoids over `C`, then
the
explicit `2`-fibre-product projection from Lemma 4.32.3 is again fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductProjection_isFibredInGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids S.p] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p := by
  -- Rebundle `F` and `G` as morphisms of fibred categories over `C`.
  let Ff : FibredCategoryOver.ofFunctor X.p ⟶ FibredCategoryOver.ofFunctor S.p :=
    FibredCategoryMor.ofBasedFunctor
      (show (FibredCategoryOver.ofFunctor X.p).toBasedCategory ⥤ᵇ
          (FibredCategoryOver.ofFunctor S.p).toBasedCategory from F)
      (by
        intro a b φ hφ
        exact (inferInstance : IsFibredInGroupoids S.p).isStronglyCartesian_map (F.map φ))
  let Gf : FibredCategoryOver.ofFunctor Y.p ⟶ FibredCategoryOver.ofFunctor S.p :=
    FibredCategoryMor.ofBasedFunctor
      (show (FibredCategoryOver.ofFunctor Y.p).toBasedCategory ⥤ᵇ
          (FibredCategoryOver.ofFunctor S.p).toBasedCategory from G)
      (by
        intro a b φ hφ
        exact (inferInstance : IsFibredInGroupoids S.p).isStronglyCartesian_map (G.map φ))
  -- Lemma 4.33.10 supplies the ambient fibredness of the explicit pullback projection.
  have hp : (explicitTwoFibreProduct F G).p.IsFibered := by
    change (FibredCategoryOver.twoFibreProduct Ff Gf).p.IsFibered
    exact FibredCategoryOver.isFibred (X := FibredCategoryOver.twoFibreProduct Ff Gf)
  -- Lemma 4.35.2 then reduces the remaining work to the fiberwise groupoid statement proved above.
  exact
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (explicitTwoFibreProduct F G).p hp
      (explicit_two_fibre_product_fiber_isGroupoid F G)

instance (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids S.p] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p :=
  explicitTwoFibreProductProjection_isFibredInGroupoids F G

end Raw

namespace FibredInGroupoidsOver

variable {X Y S : FibredInGroupoidsOver C}

open FibredInGroupoidsMor

/-- Helper for Lemma 4.35.7: forget a square in `FibredInGroupoidsOver C` to the ambient square
in `FibredCategoryOver C`. -/
private noncomputable abbrev toFibredCategorySquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.toFibredCategoryOver
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((fibredInGroupoidsOverSubTwoCategory C).hom P.obj S).inclusion) P.ψ

private theorem ambientTwoFibreProduct_isFibredInGroupoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p := by
  change IsFibredInGroupoids
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  exact explicitTwoFibreProductProjection_isFibredInGroupoids (toBasedFunctor F) (toBasedFunctor G)

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in groupoids over
`C`, obtained by restricting the chapter-level owner `FibredCategoryOver.twoFibreProduct` to the
full sub-`2`-category `FibredInGroupoidsOver C`. -/
noncomputable def twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInGroupoidsOver C :=
  ⟨FibredCategoryOver.twoFibreProduct F.toHom G.toHom,
    ambientTwoFibreProduct_isFibredInGroupoids F G⟩

/-- The left projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`.  Kept as a (semireducible) `def`, not an `abbrev`: as a reducible abbrev it is
eagerly unfolded during `isDefEq`, exposing the heavy explicit-pullback projection and causing
whnf-heartbeat overflows when matched (e.g. in `Lemma_4_42_6`). -/
noncomputable def twoFibreProductLeftProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ X :=
  by
    unfold twoFibreProduct
    exact ofAmbientHom (FibredCategoryOver.twoFibreProductLeftProjection F.toHom G.toHom)

/-- The right projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`.  Kept as a (semireducible) `def` for the same reason as
`twoFibreProductLeftProjection`. -/
noncomputable def twoFibreProductRightProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ Y :=
  by
    unfold twoFibreProduct
    exact ofAmbientHom (FibredCategoryOver.twoFibreProductRightProjection F.toHom G.toHom)

/- The canonical `2`-commutative square in `FibredInGroupoidsOver C` for the two-fibre-product
construction above. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  { obj := twoFibreProduct F G
    p := twoFibreProductLeftProjection F G
    q := twoFibreProductRightProjection F G
    ψ := by
      unfold twoFibreProduct
      exact (mkTwoFibreProductSquare F G
        (ambientTwoFibreProduct_isFibredInGroupoids F G)).ψ }

/-- Helper for Lemma 4.35.7: forget a morphism into the fibred-in-groupoids pullback square to the
ambient morphism into the fibred-category pullback square. -/
private noncomputable abbrev toAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ mkTwoFibreProductSquare F G hP) :
    toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    -- Forget the owner square equation to the underlying ambient `2`-cells.
    exact congrArg (fun α ↦ α.hom.hom) u.comm

/-- Helper for Lemma 4.35.7: rewrap an ambient morphism into the fibred-category pullback square
as a morphism into the fibred-in-groupoids pullback square. -/
private noncomputable abbrev ofAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ mkTwoFibreProductSquare F G hP := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Rebuild the owner square equation from the ambient equation by extensionality of the two
  -- wrapper layers on `2`-morphisms.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Lemma 4.35.7: forget a `2`-morphism between owner square morphisms to the ambient
`2`-morphism between their forgotten ambient square morphisms. -/
private noncomputable abbrev toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ mkTwoFibreProductSquare F G hP}
    (η : u ⟶ v) :
    toAmbientSquareHom hP u ⟶ toAmbientSquareHom hP v where
  hom := η.hom.hom.hom
  left_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient left compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient right compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Lemma 4.35.7: rewrap an ambient `2`-morphism between ambient square morphisms as
an owner `2`-morphism between their rewrapped owner square morphisms. -/
private noncomputable abbrev ofAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom}
    (η : u ⟶ v) :
    ofAmbientSquareHom hP u ⟶ ofAmbientSquareHom hP v := by
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · -- Rebuild the left compatibility through the two wrapper layers on owner `2`-morphisms.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · -- Rebuild the right compatibility through the two wrapper layers on owner `2`-morphisms.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Lemma 4.35.7: rewrapping after forgetting a square `2`-morphism is definitionally
the original owner `2`-morphism. -/
private theorem of_toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ mkTwoFibreProductSquare F G hP}
    (η : u ⟶ v) :
    ofAmbientSquareTwoHom hP (toAmbientSquareTwoHom hP η) = η := by
  rfl

/-- Helper for Lemma 4.35.7: for any competing square, the hom-category into the owner
fibred-in-groupoids pullback square has a terminal object obtained by transporting the ambient
terminal object from the fibred-category pullback square. -/
private theorem square_hasTerminal
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.HasTerminal (P ⟶ mkTwoFibreProductSquare F G hP) := by
  let Q := toFibredCategorySquare P
  let T := FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal T := FibredCategoryOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : Q ⟶ T := ⊤_ (Q ⟶ T)
  let targetOwner : P ⟶ mkTwoFibreProductSquare F G hP := ofAmbientSquareHom hP targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  -- Transport the ambient terminal object and its uniqueness through the owner/ambient square-hom
  -- conversions established above.
  exact
    (Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ ofAmbientSquareTwoHom hP (Limits.terminal.from (toAmbientSquareHom hP u)))
      (fun u η ↦ by
        have hηambient :
            toAmbientSquareTwoHom hP η = Limits.terminal.from (toAmbientSquareHom hP u) :=
          htarget.hom_ext _ _
        have hηowner :
            ofAmbientSquareTwoHom hP (toAmbientSquareTwoHom hP η) =
              ofAmbientSquareTwoHom hP (Limits.terminal.from (toAmbientSquareHom hP u)) :=
          congrArg (ofAmbientSquareTwoHom hP) hηambient
        exact (of_toAmbientSquareTwoHom hP η).symm.trans hηowner)).hasTerminal

-- Proof sketch: use the ambient `FibredCategoryOver.twoFibreProductSquare` and restrict its
-- universal property along the full sub-`2`-category `FibredInGroupoidsOver C`.
/-- Lemma 4.35.7 (2): the canonical square `twoFibreProductSquare F G` is a bicategorical
`2`-fibre product in the `2`-category of categories fibred in groupoids over `C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- Route correction: instead of a looping `simpa`, transport the ambient terminal objects in the
  -- square-hom categories through the explicit owner/ambient square-hom conversions above.
  refine ⟨fun P ↦ ?_⟩
  unfold twoFibreProductSquare
  unfold twoFibreProductLeftProjection
  unfold twoFibreProductRightProjection
  unfold twoFibreProduct
  exact square_hasTerminal (ambientTwoFibreProduct_isFibredInGroupoids F G) P

end FibredInGroupoidsOver

end CategoryTheory
