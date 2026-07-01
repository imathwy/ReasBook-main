import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

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
