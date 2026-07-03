import Mathlib

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev ringedSpaceCommRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev ringedSpacePushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceRingCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringedSpaceRingCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (ringedSpaceCommRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf Y) :=
  SheafOfModules.pushforward (ringedSpacePushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf Y) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pullback (ringedSpacePushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of
`\mathcal O_X`-modules on a ringed space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The homotopy-to-derived functor induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  (ringedSpaceModulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  (ringedSpaceModulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded derived direct image functor `Rf_*`. -/
abbrev modulePushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The unbounded derived inverse-image functor `Lf^*`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The source object `Lg^* Rf_* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeSource {X S S' : RingedSpace.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)

/-- The target object `R(f')_* L(g')^* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeTarget {X X' S' : RingedSpace.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K)

/-- The defining adjoint formula for the unbounded base-change map of a single square. -/
def IsUnboundedDerivedBaseChangeMap
    {X' X Y' Y : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y)
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback l).Additive]
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (hpull : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (K : ModuleDerived X)
    (τ : derivedBaseChangeSource f l K ⟶ derivedBaseChangeTarget k f' K) : Prop :=
  ((adjf'.homEquiv (derivedBaseChangeSource f l K) ((modulePullbackDerived k).obj K)).symm τ) =
    (hpull.hom.app ((modulePushforwardDerived f).obj K) ≫
      (modulePullbackDerived k).map (adjf.counit.app K))

/-- The source object `Lm^* Rg_* Rf_* K` for the composed base-change map of the outer
rectangle. -/
abbrev composedDerivedBaseChangeSource
    {X Y Z Z' : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : Z' ⟶ Z)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePushforward g).Additive]
    [(ringedSpaceModulePullback m).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
    (K : ModuleDerived X) : ModuleDerived Z' :=
  (modulePullbackDerived m).obj (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K)

/-- The target object `Rg'_* Rf'_* Lk^* K` for the composed base-change map of the outer
rectangle. -/
abbrev composedDerivedBaseChangeTarget
    {X' X Y' Z' : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePushforward g').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
    (K : ModuleDerived X) : ModuleDerived Z' :=
  ((modulePushforwardDerived f') ⋙ (modulePushforwardDerived g')).obj ((modulePullbackDerived k).obj K)

/-- The defining adjoint formula for the composite of two unbounded base-change maps in a
three-row diagram of ringed spaces. -/
def IsComposedUnboundedDerivedBaseChangeMap
    {X' X Y' Y Z' Z : RingedSpace.{u}}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y) (m : Z' ⟶ Z) (g' : Y' ⟶ Z')
    (g : Y ⟶ Z)
    [(ringedSpaceModulePullback k).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback l).Additive]
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback m).Additive]
    [(ringedSpaceModulePushforward g').Additive]
    [(ringedSpaceModulePushforward g).Additive]
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePullback g).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis Z')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adjg : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adjg' : modulePullbackDerived g' ⊣ modulePushforwardDerived g')
    (hpull₁ : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (hpull₂ : modulePullbackDerived m ⋙ modulePullbackDerived g' ≅
      modulePullbackDerived g ⋙ modulePullbackDerived l)
    (K : ModuleDerived X)
    (τ : composedDerivedBaseChangeSource f g m K ⟶ composedDerivedBaseChangeTarget k f' g' K) :
    Prop :=
  (((adjg'.comp adjf').homEquiv (composedDerivedBaseChangeSource f g m K)
      ((modulePullbackDerived k).obj K)).symm τ) =
    ((Functor.whiskerRight hpull₂.hom (modulePullbackDerived f')).app
        (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K) ≫
      (Functor.whiskerLeft (modulePullbackDerived g) hpull₁.hom).app
        (((modulePushforwardDerived f) ⋙ (modulePushforwardDerived g)).obj K) ≫
      (modulePullbackDerived k).map ((adjg.comp adjf).counit.app K))

section Composition

variable {X' X Y' Y Z' Z : RingedSpace.{u}}
variable (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (f : X ⟶ Y)
variable (m : Z' ⟶ Z) (g' : Y' ⟶ Z') (g : Y ⟶ Z)

variable [(ringedSpaceModulePullback k).Additive]
variable [(ringedSpaceModulePushforward f').Additive]
variable [(ringedSpaceModulePullback l).Additive]
variable [(ringedSpaceModulePushforward f).Additive]
variable [(ringedSpaceModulePullback m).Additive]
variable [(ringedSpaceModulePushforward g').Additive]
variable [(ringedSpaceModulePushforward g).Additive]
variable [(ringedSpaceModulePullback g').Additive]
variable [(ringedSpaceModulePullback g).Additive]
variable [(ringedSpaceModulePullback f').Additive]
variable [(ringedSpaceModulePullback f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived k) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived l) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived m) (ModuleQis Z)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g') (ModuleQis Y')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis Z')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

-- Proof sketch: transpose the composite `Lm^*Rg_*Rf_*K ⟶ Rg'_*Ll^*Rf_*K ⟶ Rg'_*Rf'_*Lk^*K`
-- across the composite adjunction `Lg'^* ⋙ Lf'^* ⊣ Rf'_* ⋙ Rg'_*`. Naturality of the two
-- hom-set equivalences identifies its adjoint with the lower-square pullback comparison, then the
-- upper-square pullback comparison, followed by the counit for the composite adjunction
-- `(adjg.comp adjf)`, which is exactly the rectangle formula.
/-- Remark 20.28.4: for a commutative diagram of ringed spaces
`X' \xrightarrow{k} X`, `Y' \xrightarrow{l} Y`, `Z' \xrightarrow{m} Z` with vertical maps
`f' : X' \to Y'`, `f : X \to Y`, `g' : Y' \to Z'`, and `g : Y \to Z`, if `τ₁` and `τ₂` are the
base-change maps for the upper and lower squares as in Remark 20.28.3, then the composite
`Lm^* Rg_* Rf_* K \to Rg'_* Ll^* Rf_* K \to Rg'_* Rf'_* Lk^* K` is the base-change map for the
outer rectangle. -/
theorem unbounded_derived_baseChange_map_comp
    (adjf : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adjf' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adjg : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adjg' : modulePullbackDerived g' ⊣ modulePushforwardDerived g')
    (hpull₁ : modulePullbackDerived l ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived k)
    (hpull₂ : modulePullbackDerived m ⋙ modulePullbackDerived g' ≅
      modulePullbackDerived g ⋙ modulePullbackDerived l)
    (K : ModuleDerived X)
    (τ₁ : derivedBaseChangeSource f l K ⟶ derivedBaseChangeTarget k f' K)
    (hτ₁ : IsUnboundedDerivedBaseChangeMap k f' l f adjf adjf' hpull₁ K τ₁)
    (τ₂ : derivedBaseChangeSource g m ((modulePushforwardDerived f).obj K) ⟶
      derivedBaseChangeTarget l g' ((modulePushforwardDerived f).obj K))
    (hτ₂ : IsUnboundedDerivedBaseChangeMap l g' m g adjg adjg' hpull₂
      ((modulePushforwardDerived f).obj K) τ₂) :
    IsComposedUnboundedDerivedBaseChangeMap k f' l f m g' g adjf adjf' adjg adjg' hpull₁ hpull₂ K
      (τ₂ ≫ (modulePushforwardDerived g').map τ₁) := sorry

end Composition

end AlgebraicGeometry.RingedSpace
