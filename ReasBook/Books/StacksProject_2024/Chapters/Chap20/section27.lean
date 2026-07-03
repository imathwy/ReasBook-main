import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Triangulated

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_27_1 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space `X`. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The functor `K(\mathcal A) ⥤ D(\mathcal B)` obtained by applying an additive functor termwise
and then passing to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms used to localize the homotopy category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves on a
ringed space `X`, formalized as the localization of the homotopy category at quasi-isomorphisms.
-/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  (ModuleQis X).Localization

/-- The functor `K(\mathcal O_Y) ⥤ D(\mathcal O_X)` obtained by applying `f^*` termwise and then
passing to the derived category. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :=
  mapHomotopyCategoryToDerived (modulePullback f)

-- Proof sketch: apply Lemma `13.14.15` to the triangulated functor
-- `modulePullbackToDerived f : K(\mathcal O_Y) ⥤ D(\mathcal O_X)` with the subset of K-flat
-- complexes. Lemma `20.26.12` gives enough K-flat resolutions, Lemma `20.26.8` shows pullback
-- preserves K-flatness, and Lemma `20.26.13` shows pullback sends quasi-isomorphisms between
-- K-flat complexes to quasi-isomorphisms. Equation `13.14.9.1` then identifies the resulting
-- total left derived functor with the desired `Lf^*`.
/-- Lemma 20.27.1: the pullback functor on homotopy categories
`K(\mathcal O_Y) ⥤ D(\mathcal O_X)` obtained from `f^*` has an everywhere defined total left
derived functor with respect to quasi-isomorphisms. Equivalently, the construction via K-flat
resolutions is independent of choices and defines the derived pullback functor
`Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for homotopy-category pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    ModuleDerived Y ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (ModuleQis Y).Q
    (ModuleQis Y)

/-- The canonical functor from cochain complexes of `\mathcal O_X`-modules to the derived
category `D(\mathcal O_X)`. -/
abbrev complexToDerived (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

/-- Short notation for the derived pullback functor `Lf^*`. -/
abbrev Lf
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    ModuleDerived Y ⥤ DerivedCategory (RingedSpace.Modules X) :=
  modulePullbackDerived f

-- Proof sketch: the underived functor `modulePullbackToDerived f` commutes with the shift on the
-- homotopy category, and the universal property of total left derived functors transports this
-- shift compatibility to `modulePullbackDerived f`.
/-- The derived pullback functor commutes with the triangulated shift. -/
noncomputable instance modulePullbackDerived_commShift
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [HasShift (ModuleDerived Y) ℤ]
    [(modulePullback f).Additive] :
    (modulePullbackDerived f).CommShift ℤ := sorry

-- Proof sketch: `modulePullbackToDerived f` is an exact functor of triangulated categories from
-- the homotopy category to the derived category, and the exactness comparison for total left
-- derived functors upgrades this to the derived pullback `modulePullbackDerived f`.
/-- The derived pullback functor is exact in the triangulated sense. -/
theorem modulePullbackDerived_isTriangulated
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [HasShift (ModuleDerived Y) ℤ]
    [Preadditive (ModuleDerived Y)]
    [∀ n : ℤ, (shiftFunctor (ModuleDerived Y) n).Additive]
    [Pretriangulated (ModuleDerived Y)]
    [IsTriangulated (ModuleDerived Y)]
    [(modulePullback f).Additive] :
    (modulePullbackDerived f).IsTriangulated := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_27_2 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
/-- The abelian category of `\mathcal O_X`-modules on a ringed space `X`. -/
abbrev ModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules.{u} (RingedSpace.ringCatSheaf X)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The localized derived category `D(\mathcal O_X)` used for unbounded derived pullback. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  (ModuleQis X).Localization

/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_*\mathcal O_X` after forgetting
commutativity. -/
abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
      ⟨f.hom.c⟩)

/-- The pullback functor on `\mathcal O`-modules induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ModuleCat Y ⥤ ModuleCat X :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

-- Proof sketch: `f^*` is left adjoint to pushforward on sheaves of modules, hence preserves
-- biproducts; additive functors are exactly those preserving the preadditive structure encoded by
-- these biproducts.
/-- Pullback of sheaves of modules along a morphism of ringed spaces is additive. -/
instance modulePullback_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (modulePullback f).Additive := sorry

/-- The standard pullback-composition isomorphism on categories of sheaves of modules. -/
noncomputable abbrev modulePullbackCompIso {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback (f ≫ g) ≅ modulePullback g ⋙ modulePullback f :=
  (SheafOfModules.pullbackComp (pushforwardStructureSheafHom g) (pushforwardStructureSheafHom f)).symm

-- Proof sketch: the two functors on homotopy categories have the same effect on objects and
-- maps, because applying `F ⋙ G` termwise is the same as first applying `F` termwise and then
-- `G` termwise.
/-- The comparison from the homotopy functor of a composite to the composite homotopy functor is
the identity on objects. -/
private theorem mapHomotopyCategoryComp_hom_naturality
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := sorry

-- Proof sketch: this is the same identity-on-objects comparison as above, read in the reverse
-- direction.
/-- The reverse comparison from the composite homotopy functor to the homotopy functor of a
composite is the identity on objects. -/
private theorem mapHomotopyCategoryComp_inv_naturality
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ := sorry

/-- The forward comparison from the homotopy functor of a composite to the composite homotopy
functor. -/
private abbrev mapHomotopyCategoryCompHom
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (up ℤ) ⟶
      F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_hom_naturality F G)

/-- The reverse comparison from the composite homotopy functor to the homotopy functor of a
composite. -/
private abbrev mapHomotopyCategoryCompInv
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) ⟶
      (F ⋙ G).mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_inv_naturality F G)

-- Proof sketch: both composites are the identity natural transformation because the components
-- are identities and the forward and backward comparisons are inverse on each homotopy object.
/-- The forward and backward homotopy-composition comparisons compose to the identity. -/
private theorem mapHomotopyCategoryComp_hom_inv_id
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompHom F G ≫ mapHomotopyCategoryCompInv F G =
      𝟙 ((F ⋙ G).mapHomotopyCategory (up ℤ)) := sorry

-- Proof sketch: this is the converse identity, proved by the same objectwise computation.
/-- The reverse and forward homotopy-composition comparisons compose to the identity. -/
private theorem mapHomotopyCategoryComp_inv_hom_id
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompInv F G ≫ mapHomotopyCategoryCompHom F G =
      𝟙 (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)) := sorry

/-- Applying `mapHomotopyCategory` to a composite functor is canonically isomorphic to composing
the induced functors on homotopy categories. -/
noncomputable def mapHomotopyCategoryCompIso
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (up ℤ) ≅
      F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) where
  hom := mapHomotopyCategoryCompHom F G
  inv := mapHomotopyCategoryCompInv F G
  hom_inv_id := mapHomotopyCategoryComp_hom_inv_id F G
  inv_hom_id := mapHomotopyCategoryComp_inv_hom_id F G

-- Proof sketch: functoriality of `NatTrans.mapHomotopyCategory` transports the inverse pair
-- defining `modulePullbackCompIso f g` to the homotopy category.
/-- The mapped pullback-composition morphisms on homotopy categories compose to the identity. -/
private theorem modulePullbackComp_mapHomotopy_hom_inv_id
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).hom (up ℤ) ≫
      NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).inv (up ℤ) =
        𝟙 ((modulePullback (f ≫ g)).mapHomotopyCategory (up ℤ)) := sorry

-- Proof sketch: this is the inverse identity transported from the pullback-composition
-- isomorphism by `NatTrans.mapHomotopyCategory`.
/-- The reverse mapped pullback-composition morphisms on homotopy categories compose to the
identity. -/
private theorem modulePullbackComp_mapHomotopy_inv_hom_id
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).inv (up ℤ) ≫
      NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).hom (up ℤ) =
        𝟙 ((modulePullback g ⋙ modulePullback f).mapHomotopyCategory (up ℤ)) := sorry

/-- The pullback-composition isomorphism transported to homotopy categories. -/
noncomputable def modulePullbackCompIsoOnHomotopy
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullback (f ≫ g)).mapHomotopyCategory (up ℤ) ≅
      (modulePullback g ⋙ modulePullback f).mapHomotopyCategory (up ℤ) where
  hom := NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).hom (up ℤ)
  inv := NatTrans.mapHomotopyCategory (modulePullbackCompIso f g).inv (up ℤ)
  hom_inv_id := modulePullbackComp_mapHomotopy_hom_inv_id f g
  inv_hom_id := modulePullbackComp_mapHomotopy_inv_hom_id f g

/-- The functor from the homotopy category to the localized derived category induced by
underived pullback. -/
abbrev modulePullbackToLocalization {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived X :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ (ModuleQis X).Q

/-- The underived pullback for a composite morphism agrees canonically with first pulling back
along `g` and then along `f`, after passing to the localized derived categories. -/
noncomputable abbrev modulePullbackToLocalizationCompIso
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackToLocalization (f ≫ g) ≅
      (modulePullback g).mapHomotopyCategory (up ℤ) ⋙ modulePullbackToLocalization f :=
  Functor.isoWhiskerRight (modulePullbackCompIsoOnHomotopy f g) ((ModuleQis X).Q) ≪≫
    Functor.isoWhiskerRight
      (mapHomotopyCategoryCompIso (modulePullback g) (modulePullback f))
      ((ModuleQis X).Q) ≪≫
    (Functor.associator
      ((modulePullback g).mapHomotopyCategory (up ℤ))
      ((modulePullback f).mapHomotopyCategory (up ℤ))
      ((ModuleQis X).Q))

-- Proof sketch: compute `Lf^*` by a K-flat resolution on the source homotopy category and use
-- the K-flat pullback stability from the preceding section so that pulling back along `f` still
-- computes the left derived functor after localization.
/-- Pullback on complexes admits an unbounded left derived functor after localizing at
quasi-isomorphisms. -/
instance modulePullbackToLocalization_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasLeftDerivedFunctor (modulePullbackToLocalization f) (ModuleQis Y) := sorry

/-- The unbounded derived pullback functor `Lf^* : D(\mathcal O_X) \to D(\mathcal O_Y)`. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  (modulePullbackToLocalization f).totalLeftDerived (ModuleQis Y).Q (ModuleQis Y)

/-- Short notation for the unbounded derived pullback functor `Lf^*`. -/
noncomputable abbrev Lf {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  modulePullbackDerived f

/-- The canonical comparison morphism from the composite derived pullback to the derived pullback
of the composite morphism. -/
noncomputable def modulePullbackDerivedCompComparison
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackDerived g ⋙ modulePullbackDerived f ⟶ modulePullbackDerived (f ≫ g) :=
  (modulePullbackDerived (f ≫ g)).leftDerivedLift
    ((modulePullbackToLocalization (f ≫ g)).totalLeftDerivedCounit (ModuleQis Z).Q (ModuleQis Z))
    (ModuleQis Z)
    (modulePullbackDerived g ⋙ modulePullbackDerived f)
    ((Functor.associator (ModuleQis Z).Q (modulePullbackDerived g) (modulePullbackDerived f)).inv ≫
      Functor.whiskerRight
        ((modulePullbackToLocalization g).totalLeftDerivedCounit (ModuleQis Z).Q (ModuleQis Z))
        (modulePullbackDerived f) ≫
      (Functor.associator
        ((modulePullback g).mapHomotopyCategory (up ℤ))
        (ModuleQis Y).Q
        (modulePullbackDerived f)).hom ≫
      Functor.whiskerLeft
        ((modulePullback g).mapHomotopyCategory (up ℤ))
        ((modulePullbackToLocalization f).totalLeftDerivedCounit (ModuleQis Y).Q (ModuleQis Y)) ≫
      (modulePullbackToLocalizationCompIso f g).symm.hom)

-- Proof sketch: choose a K-flat representative of an object of `D(\mathcal O_Z)`, use pullback
-- stability of K-flat complexes to see that applying `g^*` still gives a valid input for the
-- derived pullback along `f`, and then identify the iterated pullback complex with the pullback
-- along `g ∘ f`.
/-- Lemma 20.27.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical comparison morphism from `Lf^* ∘ Lg^*` to `L(g \circ f)^*` is an isomorphism on
`D(\mathcal O_Z)`. -/
theorem modulePullbackDerived_comp_isIso
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (modulePullbackDerivedCompComparison f g) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_27_3 (from Chap20) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- The structure sheaf of a ringed space is viewed below as a sheaf of not-necessarily-commutative
rings, and the induced module category is `RingedSpace.Modules X`. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O_X`-modules.
-/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The functor on homotopy categories induced by module pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use the preservation of K-flatness by pullback,
-- and apply the universal property of total left derived functors.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

variable {X Y : RingedSpace.{u}}

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

/-- The category of `\mathcal O_X`-modules is preadditive. -/
local instance instPreadditiveSheafModules : Preadditive (RingedSpace.Modules X) :=
  (inferInstance : Abelian (RingedSpace.Modules X)).toPreadditive

/-- The category of `\mathcal O_X`-modules has binary biproducts. -/
local instance instHasBinaryBiproductsSheafModules :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [HasCountableCoproducts (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [(curriedTensor ((RingedSpace.Modules Y))).Additive]
variable [∀ ℱ : (RingedSpace.Modules Y), ((curriedTensor ((RingedSpace.Modules Y))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules Y)))]

/-- A chosen homotopy-category representative of a derived `\mathcal O_X`-module. -/
private noncomputable abbrev derivedTensorRepresentative
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  DerivedCategory.Qh.objPreimage ℱ

/-- The cochain complex underlying the chosen representative of a derived `\mathcal O_X`-module.
-/
private noncomputable abbrev derivedTensorRepresentativeComplex
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    CochainComplex (RingedSpace.Modules X) ℤ :=
  (derivedTensorRepresentative ℱ).as

/-- Tensor-totalization on the homotopy category with a fixed right complex. -/
private noncomputable abbrev tensorLeftHomotopyFunctorOfComplex
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 K)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ)))

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor. -/
private noncomputable abbrev derivedTensorSourceFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  tensorLeftHomotopyFunctorOfComplex (derivedTensorRepresentativeComplex ℱ) ⋙
    DerivedCategory.Qh

-- Proof sketch: replace the chosen representative of the fixed right factor by a K-flat one and
-- use invariance of tensoring with a K-flat complex under quasi-isomorphism.
/-- Tensoring on the homotopy category with a fixed right factor admits a total left derived
functor. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (derivedTensorSourceFunctor ℱ).HasLeftDerivedFunctor (ModuleQis X) := sorry

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

private noncomputable abbrev derivedTensorProductX
    (ℱ : DModX) :
    DModX ⥤ DModX :=
  AlgebraicGeometry.RingedSpace.derivedTensorProduct ℱ

private noncomputable abbrev derivedTensorProductY
    (ℱ : DModY) :
    DModY ⥤ DModY :=
  AlgebraicGeometry.RingedSpace.derivedTensorProduct ℱ

/-- The canonical counit exhibiting derived tensoring with a fixed right factor as a left derived
functor. -/
private abbrev derivedTensorProductCounit
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
      derivedTensorProductX ℱ ⟶
        derivedTensorSourceFunctor ℱ :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor ℱ
  (derivedTensorSourceFunctor ℱ).totalLeftDerivedCounit
    DerivedCategory.Qh
    (ModuleQis X)

-- Proof sketch: this is the defining `IsLeftDerivedFunctor` instance for the total left derived
-- functor attached to `derivedTensorSourceFunctor ℱ`.
/-- Derived tensoring with a fixed right factor is the left derived functor of the corresponding
homotopy-category tensor functor. -/
private theorem derivedTensorProduct_isLeftDerivedFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (derivedTensorProductX ℱ).IsLeftDerivedFunctor
      (derivedTensorProductCounit ℱ)
      (ModuleQis X) := by
  sorry

/-- The counit exhibiting
`(- \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet) \circ Lf^*`
as a left derived functor after postcomposing with `Lf^*`. -/
private abbrev derivedTensorThenPullbackCounit
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y)) ⋙
      (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f) ⟶
        derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
      (derivedTensorProductY 𝒢)
      (modulePullbackDerived f)).hom ≫
    Functor.whiskerRight
      (derivedTensorProductCounit 𝒢)
      (modulePullbackDerived f)

-- Proof sketch: postcompose the left derived functor `derivedTensorProduct 𝒢` with `Lf^*`; the
-- universal property of left derived functors is preserved under this fixed postcomposition.
/-- Postcomposing derived tensoring with derived pullback again yields a left derived functor. -/
private theorem derivedTensorThenPullback_isLeftDerivedFunctor
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f).IsLeftDerivedFunctor
      (derivedTensorThenPullbackCounit f 𝒢)
      (ModuleQis Y) := by
  sorry

/-- The counit exhibiting
`Lf^* \circ (- \otimes_{\mathcal O_X}^{\mathbf L} Lf^*\mathcal G^\bullet)` as a left derived
functor of the underived pullback-to-derived functor followed by derived tensoring on `X`. -/
private abbrev pullbackThenDerivedTensorCounit
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y)) ⋙
      (modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢)) ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
      (modulePullbackDerived f)
      (derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))).hom ≫
    Functor.whiskerRight
      ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
        (ModuleQis Y))
      (derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))

-- Proof sketch: derive `modulePullbackToDerived f` first and then postcompose with the fixed
-- derived tensor functor on `X`.
/-- Pullback followed by derived tensoring with the pulled-back right factor is a left derived
functor of the underived pullback-to-derived functor followed by tensoring on `X`. -/
private theorem pullbackThenDerivedTensor_isLeftDerivedFunctor
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    ((modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
      ).IsLeftDerivedFunctor
        (pullbackThenDerivedTensorCounit f 𝒢)
        (ModuleQis Y) := by
  sorry

-- Proof sketch: on K-flat representatives this is the underived pullback-tensor comparison from
-- Lemma `17.16.4`, descended through the homotopy category and then localized to
-- `D(\mathcal O_X)`.
/-- The underived comparison natural transformation whose left derived transform is the pullback
comparison of Lemma `20.27.3`. -/
private theorem modulePullbackDerivedTensorUnderivedComparison_nonempty
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    Nonempty
      (derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢)) := by
  sorry

/-- The canonical pullback-tensor comparison morphism. -/
noncomputable def modulePullbackDerivedTensorComparison
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f ⟶
      modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  let τ :
      derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
    Classical.choice (modulePullbackDerivedTensorUnderivedComparison_nonempty f 𝒢)
  let _ :
      (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f)
        .IsLeftDerivedFunctor
        (derivedTensorThenPullbackCounit f 𝒢)
        (ModuleQis Y) :=
    derivedTensorThenPullback_isLeftDerivedFunctor f 𝒢
  let _ :
      ((modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
        ).IsLeftDerivedFunctor
          (pullbackThenDerivedTensorCounit f 𝒢)
          (ModuleQis Y) :=
    pullbackThenDerivedTensor_isLeftDerivedFunctor f 𝒢
  Functor.leftDerivedNatTrans
    (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f)
    (modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
    (derivedTensorThenPullbackCounit f 𝒢)
    (pullbackThenDerivedTensorCounit f 𝒢)
    (ModuleQis Y)
    τ

-- Proof sketch: represent the fixed right factor and the varying left factor by K-flat complexes.
-- By Lemma `20.26.5`, their total tensor product is again K-flat, so `Lf^*` can be computed by
-- ordinary pullback on that total tensor complex. The termwise pullback-tensor comparison from
-- Lemma `17.16.4` then identifies the pulled-back tensor totalization with the tensor totalization
-- of the pulled-back representatives, and passing to the derived category yields the comparison
-- natural isomorphism.
/-- The canonical pullback-tensor comparison morphism is an isomorphism. -/
theorem modulePullbackDerivedTensorComparison_isIso
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    IsIso (modulePullbackDerivedTensorComparison f 𝒢) := by
  sorry

/-- Lemma 20.27.3: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to
(Y, \mathcal O_Y)` and a fixed object `\mathcal G^\bullet` of `D(\mathcal O_Y)`, the derived
pullback functor carries `- \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet` to the
derived tensor product with the pulled-back right factor `Lf^* \mathcal G^\bullet`. Evaluating
this natural isomorphism at `\mathcal F^\bullet` gives the canonical comparison
`Lf^*(\mathcal F^\bullet \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet) \cong
Lf^*\mathcal F^\bullet \otimes_{\mathcal O_X}^{\mathbf L} Lf^*\mathcal G^\bullet`. -/
noncomputable abbrev modulePullbackDerived_derivedTensorProduct_iso
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f ≅
      modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  letI := modulePullbackDerivedTensorComparison_isIso f 𝒢
  asIso (modulePullbackDerivedTensorComparison f 𝒢)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_27_4 (from Chap20) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [Abelian (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules Y)]
variable
  [Abelian
    (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y)))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

variable
  (leftDerivedPullback : DModY ⥤ DModX)
  (derivedTensorSource : DModX ⥤ DModX ⥤ DModX)
  (derivedTensorInverseImage :
    DerivedCategory
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y))) ⥤
      DModX ⥤ DModX)
  (inverseImageDerived :
    DModY ⥤
      DerivedCategory
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y))))

-- Proof sketch: replace `Lf^*` and the two derived tensor products by K-flat representatives,
-- identify the underived comparison using the formula
-- `f^*\mathcal G = \mathcal O_X \otimes_{f^{-1}\mathcal O_Y} f^{-1}\mathcal G`, and descend the
-- resulting termwise comparison to the derived categories. The canonical bifunctoriality is
-- encoded as a natural isomorphism in the functor category `D(\mathcal O_Y) ⥤ D(\mathcal O_X) ⥤
-- D(\mathcal O_X)`.
/-- Lemma 20.27.4: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the canonical bifunctorial isomorphism
`\mathcal F^\bullet \otimes_{\mathcal O_X}^{\mathbf L} Lf^* \mathcal G^\bullet \cong
\mathcal F^\bullet \otimes_{f^{-1}\mathcal O_Y}^{\mathbf L} f^{-1}\mathcal G^\bullet`
is expressed canonically as a natural isomorphism of functors
`D(\mathcal O_Y) ⥤ D(\mathcal O_X) ⥤ D(\mathcal O_X)`. -/
theorem derivedTensor_leftDerivedPullback_iso :
    leftDerivedPullback ⋙ derivedTensorSource ≅
      inverseImageDerived ⋙ derivedTensorInverseImage := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_27_5 (from Chap20) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Functor.OplaxMonoidal
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}

/-- The localization functor from complexes to the homotopy category of `\mathcal O_X`-modules.
-/
private abbrev complexToHomotopy (X : RingedSpace) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ)

/-- The canonical functor from complexes of `\mathcal O_X`-modules to `D(\mathcal O_X)`. -/
private abbrev complexToDerived (X : RingedSpace) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X) :=
  complexToHomotopy X ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

/-- Pullback of complexes of module sheaves along a morphism of ringed spaces. -/
private abbrev modulePullbackComplex {X Y : RingedSpace} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    CochainComplex (RingedSpace.Modules Y) ℤ ⥤ CochainComplex (RingedSpace.Modules X) ℤ :=
  (modulePullback f).mapHomologicalComplex (up ℤ)

/-- The canonical abelian structure on `\mathcal O_X`-modules. -/
local instance instAbelianSourceModules : Abelian (RingedSpace.Modules X) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf X)

/-- The canonical abelian structure on `\mathcal O_Y`-modules. -/
local instance instAbelianTargetModules : Abelian (RingedSpace.Modules Y) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf Y)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ, ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [(curriedTensor ((RingedSpace.Modules Y))).Additive]
variable [∀ ℱ, ((curriedTensor ((RingedSpace.Modules Y))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules Y)))]

section PullbackTensorCounitLadder

local infixr:70 " ⊗c " => HomologicalComplex.tensorObj

/-- The canonical counit comparing derived pullback of a complex with ordinary pullback of that
complex. -/
private abbrev modulePullbackCounitApp (f : X ⟶ Y) [(modulePullback f).Additive]
    (K : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (modulePullbackDerived f).obj ((complexToDerived Y).obj K) ⟶
      (complexToDerived X).obj ((modulePullbackComplex f).obj K) :=
  ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y)).app
    ((complexToHomotopy Y).obj K)

/-- Tensor-totalization on `K(\mathcal O_Y)` with fixed right factor `M^\bullet`. -/
private abbrev targetTensorHomotopyFunctorOfComplex
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules Y) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules Y) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules Y)).map₂CochainComplex).flip.obj M) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules Y) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 M)
          (curriedTensor (RingedSpace.Modules Y)) (up ℤ)))

/-- The homotopy-category tensor functor with fixed right factor `M^\bullet`, followed by
localization to `D(\mathcal O_Y)`. -/
private abbrev targetDerivedTensorComplexSourceFunctor
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  targetTensorHomotopyFunctorOfComplex M ⋙
    DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions of the varying left factor and use the same argument as
-- in Definition `20.26.14`, now with the fixed right factor given by the literal complex
-- `M^\bullet`.
/-- Tensoring on `K(\mathcal O_Y)` with a fixed complex `M^\bullet` admits a total left derived
functor. -/
private theorem targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (targetDerivedTensorComplexSourceFunctor M).HasLeftDerivedFunctor (ModuleQis Y) := by
  sorry

/-- The derived tensor functor `- \otimes_{\mathcal O_Y}^{\mathbf L} M^\bullet` attached to a
fixed complex `M^\bullet`. -/
private abbrev targetDerivedTensorOfComplex
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  letI := targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  (targetDerivedTensorComplexSourceFunctor M).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)

/-- The canonical counit from derived tensoring with a fixed right complex `M^\bullet` to the
ordinary tensor total complex `K^\bullet ⊗ M^\bullet`. -/
private abbrev targetTensorCounitApp
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (targetDerivedTensorOfComplex M).obj ((complexToDerived Y).obj K) ⟶
      (complexToDerived Y).obj (K ⊗c M) :=
  letI := targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  ((targetDerivedTensorComplexSourceFunctor M).totalLeftDerivedCounit
    DerivedCategory.Qh (ModuleQis Y)).app ((complexToHomotopy Y).obj K)

/-- Tensor-totalization on `K(\mathcal O_X)` with fixed right factor `M^\bullet`. -/
private abbrev sourceTensorHomotopyFunctorOfComplex
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj M) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 M)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ)))

/-- The homotopy-category tensor functor with fixed right factor `M^\bullet`, followed by passage
to the derived category `D(\mathcal O_X)`. -/
private abbrev sourceDerivedTensorComplexSourceFunctor
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  sourceTensorHomotopyFunctorOfComplex M ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

-- Proof sketch: as on `Y`, fix the right complex `M^\bullet`, resolve the varying left factor by
-- K-flat complexes, and invoke the universal property of the total left derived functor.
/-- Tensoring on `K(\mathcal O_X)` with a fixed complex `M^\bullet` admits a total left derived
functor. -/
private theorem sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    (sourceDerivedTensorComplexSourceFunctor M).HasLeftDerivedFunctor (ModuleQis X) := by
  sorry

/-- The derived tensor functor `- \otimes_{\mathcal O_X}^{\mathbf L} M^\bullet` attached to a
fixed complex `M^\bullet`. -/
private abbrev sourceDerivedTensorOfComplex
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  letI := sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  (sourceDerivedTensorComplexSourceFunctor M).totalLeftDerived
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)

/-- The canonical counit from derived tensoring with a fixed right complex `M^\bullet` to the
ordinary tensor total complex `K^\bullet ⊗ M^\bullet`. -/
private abbrev sourceTensorCounitApp
    (K M : CochainComplex (RingedSpace.Modules X) ℤ) :
    (sourceDerivedTensorOfComplex M).obj ((complexToDerived X).obj K) ⟶
      (complexToDerived X).obj (K ⊗c M) :=
  letI := sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  ((sourceDerivedTensorComplexSourceFunctor M).totalLeftDerivedCounit
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)).app ((complexToHomotopy X).obj K)

variable
  (f : X ⟶ Y) [(modulePullback f).Additive]

/-- The underived pullback-tensor comparison on total tensor complexes exists canonically. -/
private theorem underivedPullbackTensorComparison_nonempty :
    Nonempty
      (∀ (K M : CochainComplex (RingedSpace.Modules Y) ℤ),
        (complexToDerived X).obj ((modulePullbackComplex f).obj (K ⊗c M)) ⟶
      (complexToDerived X).obj
        (((modulePullbackComplex f).obj K) ⊗c ((modulePullbackComplex f).obj M))) := by
  sorry

/-- The canonical underived pullback-tensor comparison on total tensor complexes. -/
private noncomputable abbrev underivedPullbackTensorComparison
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (complexToDerived X).obj ((modulePullbackComplex f).obj (K ⊗c M)) ⟶
      (complexToDerived X).obj
        (((modulePullbackComplex f).obj K) ⊗c ((modulePullbackComplex f).obj M)) :=
  Classical.choice (underivedPullbackTensorComparison_nonempty f) K M

-- Proof sketch: resolve the varying left factor by K-flat complexes, keep the literal right
-- complex `M^\bullet` fixed, and descend the underived pullback-tensor comparison to the derived
-- categories.
/-- The fixed-right-factor pullback-tensor comparison of Lemma `20.27.3`, specialized to a
literal right complex `M^\bullet`. -/
private theorem modulePullbackDerived_tensorComplex_iso_nonempty :
    Nonempty
      (∀ M : CochainComplex (RingedSpace.Modules Y) ℤ,
        targetDerivedTensorOfComplex M ⋙ modulePullbackDerived f ≅
          modulePullbackDerived f ⋙
            sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)) := by
  sorry

/-- The fixed-right-factor pullback-tensor comparison of Lemma `20.27.3`, specialized to a
literal right complex `M^\bullet`. -/
private noncomputable abbrev modulePullbackDerived_tensorComplex_iso
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    targetDerivedTensorOfComplex M ⋙ modulePullbackDerived f ≅
      modulePullbackDerived f ⋙
        sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M) :=
  Classical.choice (modulePullbackDerived_tensorComplex_iso_nonempty f) M

-- Proof sketch: choose K-flat resolutions of `K` and `M` as in Lemma `20.26.8`, so that
-- derived pullback and derived tensor product are computed by ordinary pullback and tensor
-- totalization on those resolutions. The top horizontal arrow is the component of the
-- pullback-tensor comparison of Lemma `20.27.3` for the fixed right factor `M^\bullet`, the left
-- and right vertical arrows are the canonical counits of the corresponding total left derived
-- tensor functors, the lower horizontal arrow is the canonical derived-pullback counit on
-- `Tot(K \otimes M)`, and the remaining comparison is the oplax-monoidal tensor comparison for
-- ordinary pullback on total tensor complexes. The resulting
-- resolution-level ladder commutes, and hence so does the descended ladder in the derived
-- categories.
/-- Lemma 20.27.5, as the outer `CommSq` of the source ladder.

For complexes `K^\bullet` and `M^\bullet`, the outer rectangle built from the canonical
pullback-tensor comparison of Lemma `20.27.3`, the canonical tensor counits, the canonical
derived-pullback counit, and the canonical underived pullback-tensor comparison on total tensor
complexes is commutative.
-/
theorem modulePullback_tensor_counit_commSq
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    CommSq
      ((modulePullbackDerived_tensorComplex_iso f M).hom.app ((complexToDerived Y).obj K))
      ((modulePullbackDerived f).map (targetTensorCounitApp K M))
      ((sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)).map
          (modulePullbackCounitApp f K) ≫
        sourceTensorCounitApp ((modulePullbackComplex f).obj K)
          ((modulePullbackComplex f).obj M))
      (modulePullbackCounitApp f (K ⊗c M) ≫
        underivedPullbackTensorComparison f K M) := by
  sorry

/-- Equality form of Lemma 20.27.5, obtained by taking `.w` of the canonical `CommSq`
statement. -/
theorem modulePullback_tensor_counit_ladder_commutes
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (modulePullbackDerived f).map (targetTensorCounitApp K M) ≫
        modulePullbackCounitApp f (K ⊗c M) ≫
        underivedPullbackTensorComparison f K M =
      ((modulePullbackDerived_tensorComplex_iso f M).hom.app ((complexToDerived Y).obj K)) ≫
        (sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)).map
            (modulePullbackCounitApp f K) ≫
          sourceTensorCounitApp ((modulePullbackComplex f).obj K)
            ((modulePullbackComplex f).obj M) :=
  by
    simpa using (modulePullback_tensor_counit_commSq f K M).w.symm

end PullbackTensorCounitLadder

end AlgebraicGeometry.RingedSpace
