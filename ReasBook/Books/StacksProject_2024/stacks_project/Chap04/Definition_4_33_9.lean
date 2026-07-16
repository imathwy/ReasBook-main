import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_29_2
import StacksProject_2024.stacks_project.Chap04.Definition_4_32_1
import StacksProject_2024.stacks_project.Chap04.Lemma_4_33_7
import StacksProject_2024.stacks_project.Chap04.Lemma_4_33_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v vS w

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

/- Domain-style sampling for Definition 4.33.9:
- primary domain: fibred categories over a fixed base, organized as a full sub-`2`-category of
  `Cat/C`.
- inspected owner-level declarations:
  `CategoryOver`,
  `BasedFunctor.PreservesStronglyCartesian`,
  `Functor.IsFibered`,
  `Functor.IsStronglyCartesian`,
  `SubTwoCategory`.
- best owner abstraction: `SubTwoCategory (CategoryOver C)`.
- primitive data: the ambient predicate `X.p.IsFibered` on objects of `Cat/C` and the ambient
  predicate that a based functor over `C` preserves strongly cartesian arrows.
- derived API: the source-facing object owner `FibredCategoryOver C` together with the helper
  namespace `FibredCategoryMor` on the canonical ambient homs `X ⟶ Y`, keeping only the genuine
  bridge constructor from based functors preserving strongly cartesian arrows and otherwise using
  the ambient owner accessor `SubTwoCategory.Hom.toHom` and its induced coercion.

Source/core/bridge triage:
- `source-facing`: fibred categories over `C` and morphisms preserving strongly cartesian arrows.
- `core/canonical`: the sub-`2`-category `fibredCategoryOverSubTwoCategory C`.
- `bridge/view`: the bundled object owner `FibredCategoryOver` and the constructor
  `FibredCategoryMor.ofBasedFunctor`, with the ambient owner homs viewed through the canonical
  accessor `SubTwoCategory.Hom.toHom`. -/

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X Y : CategoryOver C}

/-- A based functor over `C` preserves strongly cartesian morphisms if it sends every strongly
cartesian arrow in the source fibred category to a strongly cartesian arrow in the target. -/
def PreservesStronglyCartesian
    (G : X ⥤ᵇ Y) : Prop :=
  ∀ ⦃a b : X.obj⦄ (φ : a ⟶ b),
    X.p.IsStronglyCartesian (X.p.map φ) φ →
      Y.p.IsStronglyCartesian (Y.p.map (G.map φ)) (G.map φ)

end BasedFunctor

private theorem fibredCategoryMor_id_preservesStronglyCartesian
    (X : CategoryOver C) :
    BasedFunctor.PreservesStronglyCartesian (𝟙 X) := by
  intro _ _ _ hφ
  simpa using hφ

private theorem fibredCategoryMor_comp_preservesStronglyCartesian
    {X Y Z : CategoryOver C}
    {F : X ⥤ᵇ Y}
    {G : Y ⥤ᵇ Z}
    (hF : BasedFunctor.PreservesStronglyCartesian F)
    (hG : BasedFunctor.PreservesStronglyCartesian G) :
    BasedFunctor.PreservesStronglyCartesian (F ⋙ G) := by
  intro a b φ hφ
  exact hG (F.map φ) (hF φ hφ)

/-- Definition 4.33.9 at the canonical owner level: fibred categories over `C` and
strongly-cartesian-preserving functors form the full sub-`2`-category of `Cat/C` cut out by
fibred objects and cartesian-preserving `1`-morphisms. -/
abbrev fibredCategoryOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (CategoryOver C) where
  obj := fun X ↦ X.p.IsFibered
  hom _ _ := {
    obj := BasedFunctor.PreservesStronglyCartesian
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem X := fibredCategoryMor_id_preservesStronglyCartesian X.obj
  comp_mem hF hG := fibredCategoryMor_comp_preservesStronglyCartesian hF hG
  whiskerLeft_mem _ _ _ _ := by
    trivial
  whiskerRight_mem _ _ _ _ := by
    trivial

/-- Definition 4.33.9: categories fibred over `C` are the objects of the owner sub-`2`-category
`fibredCategoryOverSubTwoCategory C`. -/
abbrev FibredCategoryOver (C : Type u) [Category.{v} C] :=
  (fibredCategoryOverSubTwoCategory C).Obj

instance : Bicategory (FibredCategoryOver C) :=
  SubTwoCategory.bicategoryObj (fibredCategoryOverSubTwoCategory C)

instance : Bicategory.Strict (FibredCategoryOver C) :=
  SubTwoCategory.strictObj (fibredCategoryOverSubTwoCategory C)

instance fibredCategoryOverCategory : Category (FibredCategoryOver C) :=
  StrictBicategory.category (FibredCategoryOver C)

namespace FibredCategoryOver

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredCategoryOver C) :
    CategoryOver C :=
  X.obj

/-- The total category of a fibred category over `C`. -/
abbrev S (X : FibredCategoryOver C) :=
  X.toCategoryOver.obj

/-- The projection functor to the base category. -/
abbrev p (X : FibredCategoryOver C) :=
  X.toCategoryOver.p

/-- Forget a fibred category over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredCategoryOver C) :
    BasedCategory.{vS, w} C :=
  X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

instance isFibred (X : FibredCategoryOver C) : X.p.IsFibered :=
  by
    simpa [FibredCategoryOver.p, fibredCategoryOverSubTwoCategory]
      using X.property

/-- Build a fibred category over `C` from a fibred functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    FibredCategoryOver C :=
  ⟨BasedCategory.ofFunctor p, by
    simpa [fibredCategoryOverSubTwoCategory, BasedCategory.ofFunctor] using
      (inferInstance : p.IsFibered)⟩

end FibredCategoryOver

variable (X Y : FibredCategoryOver C)

/- Definition 4.33.9: for fibred categories over `C`, the canonical `1`-morphisms are the
ambient homs `X ⟶ Y` in the owner bicategory. -/
#check (X ⟶ Y)

variable {X Y}

/-- Stable chapter vocabulary for the owner hom-category of morphisms of fibred categories over
`C`. -/
abbrev FibredCategoryMor (X Y : FibredCategoryOver C) :=
  X ⟶ Y

namespace FibredCategoryMor

variable {X Y : FibredCategoryOver C}

/-- The object property on based functors over `C` underlying morphisms of fibred categories. -/
abbrev objectProperty (X Y : FibredCategoryOver C) :
    ObjectProperty (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :=
  BasedFunctor.PreservesStronglyCartesian

/-- The underlying based functor of a morphism of fibred categories over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  show X.toBasedCategory ⥤ᵇ Y.toBasedCategory from F.toHom

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  toBasedFunctor F |>.fiberFunctor U

/-- The underlying functor between total categories. -/
abbrev toFunctor (F : X ⟶ Y) :
    X.S ⥤ Y.S :=
  toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) :
    toFunctor F ⋙ Y.p = X.p :=
  toBasedFunctor F |>.w

/-- Every object of every target fiber is locally in the essential image of the corresponding
fiber functor. This is the canonical site-local essential-surjectivity predicate for a morphism of
fibred categories over `C`. -/
def LocallyEssentiallySurjectiveOnObjects
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  ∀ (U : C) (y : Y.p.Fiber U),
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      ∃ x : X.p.Fiber I.Y,
        Nonempty (((fiberFunctor F I.Y).obj x) ≅ I.f ^*[canonicalPullbackChoice Y.p] y)

/-- A morphism of fibred categories over `C` is an equivalence over the base if its underlying
based functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)

/-- Strongly cartesian morphisms are preserved by a morphism of fibred categories. -/
theorem map_stronglyCartesian
    (F : X ⟶ Y) {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map ((toFunctor F).map φ)) ((toFunctor F).map φ) :=
  F.obj.property φ hφ

instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- Build a morphism of fibred categories from a based functor preserving strongly cartesian
morphisms. -/
abbrev ofBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hG : G.PreservesStronglyCartesian) : X ⟶ Y :=
  ⟨⟨G, by
      simpa [fibredCategoryOverSubTwoCategory] using hG⟩⟩

/-- Lift the full subcategory of based functors preserving strongly cartesian morphisms to the
owner hom-category `X ⟶ Y`. -/
abbrev ofObjectProperty (X Y : FibredCategoryOver C) :
    (objectProperty X Y).FullSubcategory ⥤ (X ⟶ Y) where
  obj F := ofBasedFunctor F.obj F.property
  map η := ⟨ObjectProperty.homMk η.hom, trivial⟩

private noncomputable def ownerIsoOfBasedFunctorIso
    {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Convert an isomorphism of owner morphisms into the corresponding isomorphism of underlying
based functors over `C`. -/
noncomputable def basedFunctorIsoOfOwnerIso
    {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  Functor.mapIso (((fibredCategoryOverSubTwoCategory C).hom X Y).inclusion) e

/-- Explicit equivalence-over-base data on the underlying based functor of `F` induce a
bicategorical equivalence with forward morphism `F`. -/
noncomputable def ofEquivalenceOverBase
    (F : X ⟶ Y)
    (e : BasedFunctor.EquivalenceOverBase (toBasedFunctor F)) :
    Bicategory.Equivalence X Y :=
  let G : Y ⟶ X :=
    ofBasedFunctor e.inverse <| by
      intro a b φ hφ
      exact
        BasedFunctor.isStronglyCartesian_map_of_isEquivalenceOverBase
          e.inverse
          e.inverse_isEquivalenceOverBase
          φ
          hφ
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G := by
    simpa [G] using ownerIsoOfBasedFunctorIso e.unitIso
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) := by
    simpa [G] using ownerIsoOfBasedFunctorIso e.counitIso
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

/-- A morphism of fibred categories over `C` that is an equivalence over the base admits a
bicategorical equivalence with forward morphism `F`. -/
theorem exists_equivalence
    (F : X ⟶ Y) (hF : FibredCategoryMor.IsEquivalenceOverBase F) :
    ∃ e : Bicategory.Equivalence X Y, e.hom = F := by
  rcases hF.nonempty with ⟨e⟩
  exact ⟨ofEquivalenceOverBase F e, rfl⟩

end FibredCategoryMor

-- Proof sketch: a morphism in the owner hom-category `X ⟶ Y` is a morphism between the
-- underlying based functors, hence a `BasedNatTrans`; its components are therefore vertical
-- over the identity on the corresponding base objects by the defining field of
-- `CategoryTheory.BasedNatTrans`.
/-- Any `2`-morphism between morphisms of fibred categories is vertical over the identity on each
source object. -/
theorem fibredCategoryMor_hom_isHomLift_id
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (τ : F ⟶ G) (a : X.S) :
    Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
      ((τ.hom.hom).toNatTrans.app a) := by
  exact (τ.hom.hom).isHomLift rfl

namespace FibredCategoryOver

variable {X Y : FibredCategoryOver C}

/- The `1`-morphism underlying a bicategorical equivalence of fibred categories over `C` is an
equivalence over the base. -/
theorem hom_isEquivalenceOverBase
    (e : Bicategory.Equivalence X Y) :
    FibredCategoryMor.IsEquivalenceOverBase e.hom := by
  let hHom : X ⟶ Y := e.hom
  let hInv : Y ⟶ X := e.inv
  change BasedFunctor.IsEquivalenceOverBase (FibredCategoryMor.toBasedFunctor hHom)
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      (FibredCategoryMor.toBasedFunctor hInv)
      (by
        change (𝟙 X.toBasedCategory) ≅
            (FibredCategoryMor.toBasedFunctor hHom ⋙
              FibredCategoryMor.toBasedFunctor hInv)
        simpa [hHom, hInv] using FibredCategoryMor.basedFunctorIsoOfOwnerIso e.unit)
      (by
        change
          (FibredCategoryMor.toBasedFunctor hInv ⋙
              FibredCategoryMor.toBasedFunctor hHom) ≅
            𝟙 Y.toBasedCategory
        simpa [hHom, hInv] using FibredCategoryMor.basedFunctorIsoOfOwnerIso e.counit)

end FibredCategoryOver

end CategoryTheory
