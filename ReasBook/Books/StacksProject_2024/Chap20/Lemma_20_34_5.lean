import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_2
import StacksProject_2024.Chap20.«20_14_1_1»

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.DerivedCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The inclusion of a closed subset into the ambient ringed space. -/
private abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The induced map on opens for a closed-subset inclusion is continuous for the canonical
Grothendieck topologies. -/
private instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The restriction of the structure sheaf of `X` to the closed subspace `Z`. -/
private abbrev closedSubsetRingCatSheaf (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subspace `Z`. -/
private abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRingCatSheaf X Z)

/-- Pushforward of `\mathcal O_X|_Z`-modules from the closed subspace `Z` to `X`. -/
private abbrev closedSubsetModulePushforward (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
      (closedSubsetInclusion X Z)).unit.app (RingedSpace.ringCatSheaf X))

-- Proof sketch: this is the module-valued closed-immersion adjunction. The pushforward functor
-- from `Z` to `X` is exact, and the usual sections-with-support construction provides its right
-- adjoint.
/-- Pushforward from the closed subspace is a left adjoint. -/
private theorem closedSubsetModulePushforward_isLeftAdjoint
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetModulePushforward X Z).IsLeftAdjoint := sorry

/-- The underived sections-with-support functor along the closed subset `Z`. -/
private abbrev closedSubsetModuleSectionsWithSupportFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (RingedSpace.Modules X) ⥤ closedSubsetModuleCategory X Z :=
  letI : (closedSubsetModulePushforward X Z).IsLeftAdjoint :=
    closedSubsetModulePushforward_isLeftAdjoint X Z hZ
  (closedSubsetModulePushforward X Z).rightAdjoint

/-- Pushforward from the closed subspace is additive. -/
private instance closedSubsetModulePushforward_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModulePushforward X Z).Additive := sorry

/-- Pushforward from the closed subspace preserves finite limits. -/
private instance closedSubsetModulePushforward_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteLimits (closedSubsetModulePushforward X Z) := sorry

/-- Pushforward from the closed subspace preserves finite colimits. -/
private instance closedSubsetModulePushforward_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteColimits (closedSubsetModulePushforward X Z) := sorry

/-- The underived sections-with-support functor is additive. -/
private instance closedSubsetModuleSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetModuleSectionsWithSupportFunctor X Z hZ).Additive := sorry

-- Proof sketch: resolve a complex of `\mathcal O_X`-modules by a K-injective complex and apply
-- the sections-with-support functor termwise; this computes the total right derived functor.
/-- The cochain-level sections-with-support functor admits a total right derived functor. -/
private theorem closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q :
          CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
            DerivedCategory (closedSubsetModuleCategory X Z))).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for sections with support along `Z`. -/
private instance closedSubsetModuleSectionsWithSupportToDerived_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q :
          CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
            DerivedCategory (closedSubsetModuleCategory X Z))).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ

/-- The derived sections-with-support functor `R\mathcal H_Z : D(\mathcal O_X) \to
`D(\mathcal O_X|_Z)`. -/
private abbrev closedSubsetModuleSectionsWithSupportDerived
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (closedSubsetModuleCategory X Z) :=
  (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Q :
        CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
          DerivedCategory (closedSubsetModuleCategory X Z))).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))

/-- Exact closed-subset pushforward viewed on derived categories. -/
private abbrev closedSubsetModulePushforwardExactFunctor
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ₑ (RingedSpace.Modules X) :=
  ExactFunctor.of (closedSubsetModulePushforward X Z)

/-- Exact closed-subset pushforward viewed on derived categories. -/
private abbrev closedSubsetModulePushforwardDerived
    (X : RingedSpace.{u}) (Z : Set X) :
    DerivedCategory (closedSubsetModuleCategory X Z) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  let _ : (closedSubsetModulePushforwardExactFunctor X Z).obj.Additive :=
    closedSubsetModulePushforward_additive X Z
  (closedSubsetModulePushforwardExactFunctor X Z).obj.mapDerivedCategory

/-- The derived global-sections-with-support functor `RΓ_Z(X, -)` modeled in
`D(Γ(X, \mathcal O_X))` as derived global sections of the pushed-forward support sheaf. -/
private abbrev derivedGlobalSectionsWithSupport
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  closedSubsetModuleSectionsWithSupportDerived X Z hZ ⋙
    closedSubsetModulePushforwardDerived X Z ⋙
    moduleDerivedGlobalSections X

/-- The open complement `U = X \setminus Z` of the closed subset `Z`. -/
private abbrev openComplement {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The restriction map on section rings from `Γ(X, \mathcal O_X)` to
`Γ(X \setminus Z, \mathcal O_X)`. -/
private abbrev sectionsRestrictionToOpenMap
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    globalSectionsRing X ⟶ sectionsRingOnOpen X (openComplement hZ) :=
  X.presheaf.map
    (homOfLE
      (show openComplement hZ ≤ (⊤ : Opens X.carrier) from
        fun _ _ ↦ trivial)).op

/-- Restriction of scalars from `Γ(X \setminus Z, \mathcal O_X)` to `Γ(X, \mathcal O_X)`. -/
private abbrev moduleSectionsRestrictionToOpenFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ModuleCat (sectionsRingOnOpen X (openComplement hZ)) ⥤ ModuleCat (globalSectionsRing X) :=
  ModuleCat.restrictScalars (sectionsRestrictionToOpenMap X hZ).hom

/-- Restriction of scalars from the open-complement section ring is additive. -/
private instance moduleSectionsRestrictionToOpenFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (moduleSectionsRestrictionToOpenFunctor X hZ).Additive :=
  inferInstance

/-- Restriction of scalars from the open-complement section ring, viewed on derived categories. -/
private abbrev moduleSectionsRestrictionToOpenExactFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ModuleCat (sectionsRingOnOpen X (openComplement hZ)) ⥤ₑ ModuleCat (globalSectionsRing X) :=
  ExactFunctor.of (moduleSectionsRestrictionToOpenFunctor X hZ)

/-- Restriction of scalars from the open-complement section ring, viewed on derived categories. -/
private abbrev moduleSectionsRestrictionToOpenDerivedFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (openComplement hZ))) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let _ : (moduleSectionsRestrictionToOpenExactFunctor X hZ).obj.Additive :=
    moduleSectionsRestrictionToOpenFunctor_additive X hZ
  (moduleSectionsRestrictionToOpenExactFunctor X hZ).obj.mapDerivedCategory

/-- The derived sections functor on the open complement `X \setminus Z`, viewed in
`D(Γ(X, \mathcal O_X))` by restriction of scalars. -/
private abbrev derivedSectionsAtOpenViaRestriction
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  moduleDerivedSectionsAtOpen X (openComplement hZ) ⋙
    moduleSectionsRestrictionToOpenDerivedFunctor X hZ

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

-- Proof sketch: choose a K-injective complex `I` representing `K`. By Lemma `20.32.1`, the
-- restriction `I|_U` is still K-injective on `U = X \setminus Z`, so `RΓ(U, K)` is computed by
-- `Γ(U, I)`. By Lemma `20.8.1` and the definition of sections with support, the sequence
-- `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is exact. The associated triangle in
-- `D(Γ(X, \mathcal O_X))` is functorial in `K`.
/-- Lemma 20.34.5: for a ringed space `(X, \mathcal O_X)`, a closed subset `Z ⊆ X`, and
`U = X \setminus Z`, there are natural morphisms
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
in `D(Γ(X, \mathcal O_X))` whose evaluation at every `K ∈ D(\mathcal O_X)` is a distinguished
triangle. Here `RΓ_Z(X, -)` is formalized by `derivedGlobalSectionsWithSupport`, and `RΓ(U, -)` is
viewed in `D(Γ(X, \mathcal O_X))` by restriction of scalars along
`Γ(X, \mathcal O_X) ⟶ Γ(U, \mathcal O_X)`. -/
theorem derivedGlobalSectionsWithSupport_distinguishedTriangle :
    ∃ α : derivedGlobalSectionsWithSupport X Z hZ ⟶ moduleDerivedGlobalSections X,
      ∃ β :
          moduleDerivedGlobalSections X ⟶ derivedSectionsAtOpenViaRestriction X hZ,
        ∃ δ :
            derivedSectionsAtOpenViaRestriction X hZ ⟶
              derivedGlobalSectionsWithSupport X Z hZ ⋙
                shiftFunctor (DerivedCategory (ModuleCat (globalSectionsRing X))) (1 : ℤ),
          ∀ K : DerivedCategory (RingedSpace.Modules X),
            Triangle.mk (α.app K) (β.app K) (δ.app K) ∈
              distTriang (DerivedCategory (ModuleCat (globalSectionsRing X))) := sorry

end

end AlgebraicGeometry.RingedSpace
