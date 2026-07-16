import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap06.Lemma_6_32_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_3
import StacksProject_2024.stacks_project.Chap17.Lemma_17_13_4
import StacksProject_2024.stacks_project.Chap17.Remark_17_13_5
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetSectionsWithSupport

attribute [local instance] RingedSpace.modules_abelian

/-- Helper for Lemma 20.34.1: `Mod(𝒪_X|_Z)` is an abelian category. Caching this instance avoids
repeated typeclass search through the closed-subset ringed-space abbreviations. -/
private local instance closedSubsetModuleCategory_abelian
    (X : RingedSpace.{u}) (Z : Set X) :
    Abelian (closedSubsetModuleCategory X Z) :=
  let _ : HasSheafify
      (Opens.grothendieckTopology (TopCat.of Z))
      AddCommGrpCat.{u} := inferInstance
  let _ :
      (Opens.grothendieckTopology (TopCat.of Z)).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  SheafOfModules.instAbelian (RingedSpace.closedSubsetRestrictedRingCatSheaf X Z)

/- Domain-style sampling for Lemma 20.34.1:
- primary domain: derived adjunction between closed-subset pushforward and sections with support
  for module sheaves on a ringed space;
- sampled owner declarations:
  `DerivedCategory`,
  `RingedSpace.closedSubsetModuleCategory`,
  `RingedSpace.closedSubsetModulePushforward`,
  `ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction`,
  `AlgebraicGeometry.ringedSpaceModulePushforward_exact_of_isClosedImmersion`,
  `CategoryTheory.additiveFunctorTotalRightDerived`;
- best owner abstraction:
  `source-facing`: the derived adjunction
    `i_* : D(𝒪_X|_Z) ⥤ D(𝒪_X)` with right adjoint `R𝓗_Z`;
  `core/canonical`: the Chapter 17 owners
    `DerivedCategory (RingedSpace.Modules X)`,
    `closedSubsetModulePushforward X Z ⊣ 𝓗[hZ]`, the closed-immersion exactness owner
    `AlgebraicGeometry.ringedSpaceModulePushforward_exact_of_isClosedImmersion`; the local
    exactness helper below is only the closed-subset specialization used privately to supply the
    exact instances consumed by `mapDerivedCategory`, while the public surface keeps the
    source-facing adjunction owner `i⋆[hZ] ⊣ R𝓗[hZ]` together with the derived adjointness
    typeclass instances;
  `bridge/view`: none beyond those owner functors in this file.

Primitive data are only `X`, `Z`, and the closedness proof `hZ`; all functorial data are reused
from the Chapter 17 and Chapter 20 owners rather than repackaged locally.
-/

/-- The unbounded derived category `D(𝒪_X|_Z)` of module sheaves on the closed subset
`Z`. -/
abbrev closedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (closedSubsetModuleCategory X Z)

/-- The closed-subset pushforward `i_* : Mod(𝒪_X|_Z) ⥤ Mod(𝒪_X)` is exact. -/
theorem closedSubsetModulePushforward_exact
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    exactFunctor
      (closedSubsetModuleCategory X Z)
      (RingedSpace.Modules X)
      (RingedSpace.closedSubsetModulePushforward X Z) := by
  let F := RingedSpace.closedSubsetModulePushforward X Z
  let _ : F.IsRightAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.closedSubsetStructureSheafHom X Z)).isRightAdjoint
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : F.IsLeftAdjoint := (pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint
  let _ : PreservesColimits F :=
    (pushforwardSectionsWithSupportAdjunction hZ).leftAdjoint_preservesColimits
  let _ : PreservesFiniteColimits F := inferInstance
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

instance closedSubsetModulePushforward_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    PreservesFiniteLimits (RingedSpace.closedSubsetModulePushforward X Z) :=
  (exactFunctor_iff (RingedSpace.closedSubsetModulePushforward X Z)).1
    (closedSubsetModulePushforward_exact X Z hZ) |>.1

instance closedSubsetModulePushforward_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    PreservesFiniteColimits (RingedSpace.closedSubsetModulePushforward X Z) :=
  (exactFunctor_iff (RingedSpace.closedSubsetModulePushforward X Z)).1
    (closedSubsetModulePushforward_exact X Z hZ) |>.2

instance closedSubsetModuleSectionsWithSupport_isRightAdjoint
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Functor.IsRightAdjoint (𝓗[hZ]) :=
  (pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

section

variable (X : RingedSpace.{u}) (Z : Set X)
variable (hZ : IsClosed Z)

local notation "ModX" => RingedSpace.Modules X
local notation "ModZ" => closedSubsetModuleCategory X Z
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QZ" => (DerivedCategory.Q : CochainComplex ModZ ℤ ⥤ DModZ)
local notation "QisX" => HomologicalComplex.quasiIso ModX (up ℤ)
local notation "QisZ" => HomologicalComplex.quasiIso ModZ (up ℤ)

local instance : Abelian ModZ :=
  SheafOfModules.instAbelian (RingedSpace.closedSubsetRestrictedRingCatSheaf X Z)

local instance : CategoryWithHomology ModZ := inferInstance

local instance : (RingedSpace.closedSubsetModulePushforward X Z).Additive := inferInstance

local instance : (𝓗[hZ]).Additive := inferInstance

/-- Helper for Lemma 20.34.1: forget a closed-subset module sheaf to its underlying abelian
sheaf on `Z`. This local owner replaces the heavier Chapter 20 import. -/
private abbrev closedSubsetModuleUnderlyingSheaf :
    ModZ ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.closedSubsetRestrictedRingCatSheaf X Z)

/-- The derived closed-subset pushforward `i_* : D(𝒪_X|_Z) ⥤ D(𝒪_X)`. -/
noncomputable abbrev closedSubsetModulePushforwardDerived
    (hZ : IsClosed Z) :
    DModZ ⥤ DModX :=
  letI : PreservesFiniteLimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  (RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory

private abbrev closedSubsetModuleSectionsWithSupportToDerived :
    CochainComplex ModX ℤ ⥤ DModZ :=
  Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ) ⋙ QZ

private abbrev closedSubsetModulePushforwardDerivedComparison :
    QZ ⋙ closedSubsetModulePushforwardDerived X Z hZ ⟶
      (RingedSpace.closedSubsetModulePushforward X Z).mapHomologicalComplex (up ℤ) ⋙ QX :=
  letI : PreservesFiniteLimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  (RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors.hom

/-- Helper for Lemma 20.34.1: exact closed-subset pushforward already computes its right derived
functor. -/
private instance closedSubsetModulePushforwardDerived_isRightDerivedFunctor :
    (closedSubsetModulePushforwardDerived X Z hZ).IsRightDerivedFunctor
      (asIso (closedSubsetModulePushforwardDerivedComparison X Z hZ)).inv
      QisZ := by
  -- Proof comment: exactness makes `i_*` invert quasi-isomorphisms, so its canonical
  -- `mapDerivedCategory` owner is simultaneously the left and right derived functor.
  let F : ModZ ⥤ ModX := RingedSpace.closedSubsetModulePushforward X Z
  letI : PreservesFiniteLimits F :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits F :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  simpa [F, closedSubsetModulePushforwardDerived] using
    (Functor.isRightDerivedFunctor_of_inverts
      QisZ
      (F.mapDerivedCategory : DModZ ⥤ DModX)
      F.mapDerivedCategoryFactors)

/-- Helper for Lemma 20.34.1: the underived closed-subset pushforward localized to `D(𝒪_X)`
already has a chosen total right derived functor. -/
private abbrev closedSubsetModulePushforwardToDerived :
    CochainComplex ModZ ℤ ⥤ DModX :=
  Functor.mapHomologicalComplex (RingedSpace.closedSubsetModulePushforward X Z) (up ℤ) ⋙ QX

/-- Helper for Lemma 20.34.1: exact closed-subset pushforward also provides the left-derived
package required by Chapter 13's direct derived-adjunction owner. -/
private theorem closedSubsetModulePushforwardToDerived_hasLeftDerivedFunctor
    (hZ : IsClosed Z) :
    (closedSubsetModulePushforwardToDerived X Z).HasLeftDerivedFunctor QisZ := by
  -- Proof comment: exactness makes `i_*` compute its left derived functor through the canonical
  -- `mapDerivedCategoryFactors.hom` comparison.
  exact Functor.HasLeftDerivedFunctor.mk'
    (closedSubsetModulePushforwardDerived X Z hZ)
    (closedSubsetModulePushforwardDerivedComparison X Z hZ)

private noncomputable def closedSubsetModuleComplexAdjunction :
    (RingedSpace.closedSubsetModulePushforward X Z).mapHomologicalComplex (up ℤ) ⊣
      (𝓗[hZ]).mapHomologicalComplex (up ℤ) :=
  (pushforwardSectionsWithSupportAdjunction hZ).mapHomologicalComplex (up ℤ)

private instance closedSubsetModulePushforwardDerived_isLeftDerivedFunctor :
    (closedSubsetModulePushforwardDerived X Z hZ).IsLeftDerivedFunctor
      (closedSubsetModulePushforwardDerivedComparison X Z hZ)
      QisZ := by
  let F : ModZ ⥤ ModX := RingedSpace.closedSubsetModulePushforward X Z
  letI : PreservesFiniteLimits F :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits F :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  simpa [F, closedSubsetModulePushforwardDerived] using
    (Functor.isLeftDerivedFunctor_of_inverts
      QisZ
      (F.mapDerivedCategory : DModZ ⥤ DModX)
      F.mapDerivedCategoryFactors)

private instance closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (closedSubsetModuleSectionsWithSupportToDerived X Z hZ).HasRightDerivedFunctor QisX := by
  simpa [closedSubsetModuleSectionsWithSupportToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor (𝓗[hZ]))

/-- The derived sections-with-support functor `R𝓗_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportDerived :
    DModX ⥤ DModZ :=
  letI :
      (closedSubsetModuleSectionsWithSupportToDerived X Z hZ).HasRightDerivedFunctor QisX :=
    closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ
  Functor.totalRightDerived
    (closedSubsetModuleSectionsWithSupportToDerived X Z hZ)
    QX
    QisX

private instance closedSubsetModuleSectionsWithSupportDerived_isRightDerivedFunctor :
    (closedSubsetModuleSectionsWithSupportDerived X Z hZ).IsRightDerivedFunctor
      ((closedSubsetModuleSectionsWithSupportToDerived X Z hZ).totalRightDerivedUnit QX QisX)
      QisX := by
  letI :
      (closedSubsetModuleSectionsWithSupportToDerived X Z hZ).HasRightDerivedFunctor QisX :=
    closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ
  simpa [closedSubsetModuleSectionsWithSupportDerived, closedSubsetModuleSectionsWithSupportToDerived] using
    (show
      (closedSubsetModuleSectionsWithSupportDerived X Z hZ).IsRightDerivedFunctor
        ((closedSubsetModuleSectionsWithSupportToDerived X Z hZ).totalRightDerivedUnit QX QisX)
        QisX from inferInstance)

/-- Helper for Lemma 20.34.1: the underived unit
`M ⟶ 𝓗_Z(i_* M)` is an isomorphism because closed-subset pushforward is fully faithful. -/
private theorem closedSubsetModulePullbackPushforwardCounit_app_isIso
    (M : ModZ) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app M) := by
  -- Proof comment: forget the module structure to the underlying abelian sheaf on `Z`, use the
  -- closed-subset counit isomorphism there, and reflect the isomorphism back to modules.
  let F := closedSubsetModuleUnderlyingSheaf X Z
  have hUnderlying :
      IsIso
        (F.map
          ((SheafOfModules.pullbackPushforwardAdjunction
            (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app M)) := by
    simpa [closedSubsetModuleUnderlyingSheaf, RingedSpace.closedSubsetModulePushforward,
      RingedSpace.closedSubsetModulePullback, RingedSpace.closedSubsetStructureSheafHom,
      RingedSpace.closedSubsetInclusion] using
      (subsetSheaf_pullback_pushforward_counit_isIso
        ((closedSubsetModuleUnderlyingSheaf X Z).obj M))
  exact
    isIso_of_reflects_iso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app M)
      F

/-- Helper for Lemma 20.34.1: closed-subset module pushforward is fully faithful because the
generic pullback-pushforward counit is already invertible on the underlying abelian sheaf. -/
private noncomputable instance closedSubsetModulePushforward_fullyFaithful :
    (RingedSpace.closedSubsetModulePushforward X Z).FullyFaithful := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.closedSubsetStructureSheafHom X Z)
  letI (M : ModZ) : IsIso (adj.counit.app M) :=
    closedSubsetModulePullbackPushforwardCounit_app_isIso (X := X) (Z := Z) M
  letI : IsIso adj.counit := NatIso.isIso_of_isIso_app adj.counit
  exact adj.fullyFaithfulROfIsIsoCounit

namespace ClosedSubsetDerived

/- Textbook surface notation for the derived closed-subset pushforward `i_*`. The ambient
ringed space and subset are recovered from the closedness proof `hZ`. -/
scoped[RingedSpaceClosedSubsetDerived] notation:max "i⋆[" hZ "]" =>
  AlgebraicGeometry.RingedSpace.closedSubsetModulePushforwardDerived _ _ hZ

/- Textbook surface notation for the derived sections-with-support functor `R𝓗_Z`. The
ambient ringed space and subset are recovered from the closedness proof `hZ`. -/
scoped[RingedSpaceClosedSubsetDerived] notation:max "R𝓗[" hZ "]" =>
  AlgebraicGeometry.RingedSpace.closedSubsetModuleSectionsWithSupportDerived _ _ hZ

end ClosedSubsetDerived

open scoped RingedSpaceClosedSubsetDerived

section

variable {X : RingedSpace.{u}} {Z : Set X}
variable (hZ : IsClosed Z)

/-- The open complement `Zᶜ` of a closed subset of a ringed space, viewed as an open subset. -/
abbrev closedSubsetOpenComplement : Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

end

/-- The canonical derived adjunction `i_* ⊣ R𝓗_Z` attached to a closed subset of a ringed
space. -/
noncomputable def closedSubsetModulePushforwardDerivedAdjunction
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    i⋆[hZ] ⊣ R𝓗[hZ] :=
  letI :
      (closedSubsetModulePushforwardToDerived X Z).HasLeftDerivedFunctor QisZ :=
    closedSubsetModulePushforwardToDerived_hasLeftDerivedFunctor X Z hZ
  letI :
      (closedSubsetModuleSectionsWithSupportToDerived X Z hZ).HasRightDerivedFunctor QisX :=
    closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ
  -- Route correction: use the direct Chapter 13 derived-adjunction owner instead of the old
  -- comparison-heavy `Adjunction.derived` route.
  CategoryTheory.Adjunction.derivedCochainComplex
    (pushforwardSectionsWithSupportAdjunction hZ)

/-- Lemma 20.34.1: the derived closed-subset pushforward `i_* : D(𝒪_X|_Z) ⥤ D(𝒪_X)` is a left
adjoint to the derived sections-with-support functor `R𝓗[hZ]`. -/
@[stacks 0A3B]
instance closedSubsetModulePushforwardDerived_isLeftAdjoint :
    Functor.IsLeftAdjoint (i⋆[hZ]) :=
  (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).isLeftAdjoint

/-- Companion owner form of Lemma 20.34.1: the derived sections-with-support functor is right
adjoint to the derived pushforward from the closed subset. -/
instance closedSubsetModuleSectionsWithSupportDerived_isRightAdjoint :
    Functor.IsRightAdjoint (R𝓗[hZ]) :=
  (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).isRightAdjoint

/-- Helper for Lemma 20.34.1: exact closed-subset pushforward stays fully faithful on derived
categories. -/
private instance closedSubsetModulePushforwardDerived_full :
    Functor.Full (closedSubsetModulePushforwardDerived X Z hZ) := by
  -- Proof comment: the imported derived full-faithfulness API transports the underived fully
  -- faithful pushforward through the exact `mapDerivedCategory` owner.
  simpa [closedSubsetModulePushforwardDerived] using
    (inferInstance :
      Functor.Full
        ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory : DModZ ⥤ DModX))

/-- Helper for Lemma 20.34.1: the same exact-owner transport gives faithfulness on derived
categories. -/
private instance closedSubsetModulePushforwardDerived_faithful :
    Functor.Faithful (closedSubsetModulePushforwardDerived X Z hZ) := by
  -- Proof comment: this is the faithful half of the same exact derived full-faithfulness package.
  simpa [closedSubsetModulePushforwardDerived] using
    (inferInstance :
      Functor.Faithful
        ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory : DModZ ⥤ DModX))

/-- Helper for Lemma 20.34.1: exact pushforward carries a degree-zero derived object on `Z` to
the corresponding degree-zero derived object on `X`. -/
private noncomputable def closedSubsetModulePushforwardDerived_singleFunctorIso
    (𝒢 : closedSubsetModuleCategory X Z) :
    (closedSubsetModulePushforwardDerived X Z hZ).obj
        ((DerivedCategory.singleFunctor (closedSubsetModuleCategory X Z) (0 : ℤ)).obj 𝒢) ≅
      (DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)).obj
        ((RingedSpace.closedSubsetModulePushforward X Z).obj 𝒢) := by
  -- Proof comment: exactness identifies derived pushforward of a single complex with the single
  -- complex on the underived pushforward.
  simpa [closedSubsetModulePushforwardDerived] using
    ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategorySingleFunctor 0).app 𝒢

-- Proof sketch: represent `K` by a K-injective complex on `Z`. Exactness of pushforward keeps the
-- pushforward complex suitable for computing the derived functor, and on such a representative
-- the derived adjunction unit identifies `K` with `R𝓗_Z(i_* K)`.
/-- Companion to Lemma 20.34.1: the unit of the derived closed-subset adjunction is an
isomorphism on objects of the closed subset. -/
instance closedSubsetModulePushforwardDerived_unit_app_isIso
    (K : closedSubsetModuleDerived X Z) :
    IsIso ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).unit.app K) := by
  let adj : i⋆[hZ] ⊣ R𝓗[hZ] := closedSubsetModulePushforwardDerivedAdjunction X Z hZ
  -- Proof comment: full faithfulness of the exact derived pushforward makes the derived unit
  -- invertible objectwise, exactly as in the open-immersion companion pattern.
  letI : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  simpa [adj] using (inferInstance : IsIso (adj.unit.app K))

-- Proof sketch: the previous derived identification shows that an object of the form `i_* 𝒢`,
-- with `𝒢` in degree zero on `Z`, is right-acyclic for the underived sections-with-support
-- functor. Therefore every positive right derived functor vanishes on `i_* 𝒢`.
/-- The higher local cohomology sheaves with support in `Z` vanish on pushforwards from `Z`. -/
theorem isZero_higherRightDerived_closedSubsetModuleSectionsWithSupport_of_pushforward
    (𝒢 : closedSubsetModuleCategory X Z) (p : ℕ) :
    IsZero
      (((𝓗[hZ]).rightDerived (p + 1)).obj
        ((RingedSpace.closedSubsetModulePushforward X Z).obj 𝒢)) := by
  let singleZ := DerivedCategory.singleFunctor (closedSubsetModuleCategory X Z) (0 : ℤ)
  let singleX := DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)
  let H := DerivedCategory.homologyFunctor (closedSubsetModuleCategory X Z) (p + 1 : ℤ)
  rcases
      Functor.rightDerived_isomorphic_to_singleFunctorCompHomologyFunctor
        (𝓗[hZ]) (p + 1) (R𝓗[hZ]) with
    ⟨eHigher⟩
  let eUnit :
      (singleZ.obj 𝒢) ≅
        (R𝓗[hZ]).obj (singleX.obj ((RingedSpace.closedSubsetModulePushforward X Z).obj 𝒢)) :=
    asIso ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).unit.app (singleZ.obj 𝒢)) ≪≫
      (R𝓗[hZ]).mapIso
        (closedSubsetModulePushforwardDerived_singleFunctorIso (X := X) (Z := Z) hZ 𝒢)
  let eSingle :
      (H.obj (singleZ.obj 𝒢)) ≅
        ((((CochainComplex.singleFunctor (closedSubsetModuleCategory X Z) (0 : ℤ)).obj 𝒢).homology
          (p + 1))) :=
    H.mapIso ((DerivedCategory.singleFunctorIsoCompQ (closedSubsetModuleCategory X Z) (0 : ℤ)).app 𝒢) ≪≫
      (DerivedCategory.homologyFunctorFactors (closedSubsetModuleCategory X Z) (p + 1 : ℤ)).app _
  have hSingleZero :
      IsZero
        ((((CochainComplex.singleFunctor (closedSubsetModuleCategory X Z) (0 : ℤ)).obj 𝒢).homology
          (p + 1))) := by
    -- Proof comment: a degree-zero complex has zero homology in every positive degree.
    simpa [CochainComplex.singleFunctor] using
      (CochainComplex.exactAt_succ_single_obj 𝒢 p).isZero_homology
  let eFinal :
      (((𝓗[hZ]).rightDerived (p + 1)).obj
        ((RingedSpace.closedSubsetModulePushforward X Z).obj 𝒢)) ≅
        ((((CochainComplex.singleFunctor (closedSubsetModuleCategory X Z) (0 : ℤ)).obj 𝒢).homology
          (p + 1))) :=
    eHigher.app ((RingedSpace.closedSubsetModulePushforward X Z).obj 𝒢) ≪≫
      H.mapIso eUnit.symm ≪≫
      eSingle
  exact IsZero.of_iso hSingleZero eFinal

end

end AlgebraicGeometry.RingedSpace
