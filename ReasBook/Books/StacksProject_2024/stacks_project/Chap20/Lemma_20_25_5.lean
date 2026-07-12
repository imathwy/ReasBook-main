import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RingTheory.Derivation.Basic
import StacksProject_2024.Chap17.Definition_17_28_3
import StacksProject_2024.Chap18.KernelIdealSheaf
import StacksProject_2024.Chap18.Lemma_18_33_9_Owner
import StacksProject_2024.Chap20.«20_11_0_1»
import StacksProject_2024.Chap20.ConstantIntegerSheaf
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Lemma_20_11_2
import StacksProject_2024.Chap20.OpensInstances

open CategoryTheory
open Opposite
open CategoryTheory.Sheaf (Γ ΓRes)
open SheafOfModules.RingedSite
open TopCat
open TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace TopologicalSpace.SheafCohomology

variable {X : TopCat.{u}}

local notation "SiteX" => Opens.grothendieckTopology X

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

local instance (O : X.Sheaf CommRingCat.{u}) :
    IsGrothendieckAbelian.{u} (RingedSpace.Modules O.toRingedSpace) :=
  AlgebraicGeometry.RingedSpace.sheafModules_isGrothendieckAbelian O.toRingedSpace

local instance
    {O' O : X.Sheaf CommRingCat.{u}}
    [HasInjectiveResolutions (RingedSpace.Modules O.toRingedSpace)]
    {π : O' ⟶ O} (s : O ⟶ O') :
    Module (globalSectionsRing O.toRingedSpace)
      ↑(moduleCohomologyAtOpen (⊤ : Opens O.toRingedSpace.carrier) (kernelIdealSheafModule π s)
        1) := by
  change Module (sectionsRingOnOpen O.toRingedSpace (⊤ : Opens O.toRingedSpace.carrier))
    ↑(moduleCohomologyAtOpen (⊤ : Opens O.toRingedSpace.carrier) (kernelIdealSheafModule π s) 1)
  infer_instance

/- Domain-style sampling for Lemma 20.25.5:
- primary domain: square-zero extensions `𝒪' ⟶ 𝒪` of sheaves of commutative rings on `X`, their
  intrinsic kernel ideal sheaf, and the boundary map in `H¹(X, Ker π)`;
- sampled owner declarations:
  `kernelIdealSheaf`,
  `kernelIdealSheafInclusion`,
  `KernelSquareZero`,
  `Sheaf.Γ`,
  `ΓRes`,
  `sheafCompose`;
- best owner abstraction: the intrinsic Chapter 18 kernel ideal `kernelIdealSheaf π`, its
  underlying additive sheaf, and the canonical site-level global-sections owner
  `(Sheaf.Γ SiteX CommRingCat).obj O`.

Source/core/bridge triage:
- `source-facing`: the boundary class attached to `0 ⟶ Ker π ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` and the existence of a
  derivation representing it;
- `core/canonical`: `kernelIdealSheaf`, `kernelIdealSheafInclusion`, `KernelSquareZero`,
  `Sheaf.Γ`, `ΓRes`, and `sheafCompose`;
- `bridge/view`: passing from the intrinsic kernel ideal sheaf to its underlying additive sheaf on
  `X`.

This file therefore keeps the source-facing boundary-map statement, but it no longer introduces a
parallel square-zero-extension wrapper or local copies of the Chapter 20 owners for underlying
sheaves and global sections. -/

/-- The forgetful functor from sheaves of commutative rings on `X` to sheaves of abelian groups. -/
private abbrev underlyingAdditiveSheafFunctor :
    X.Sheaf CommRingCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  sheafCompose SiteX
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})

/-- The sheaf of abelian groups underlying a sheaf of commutative rings on `X`. -/
private abbrev underlyingAdditiveSheaf
    (O : X.Sheaf CommRingCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} :=
  underlyingAdditiveSheafFunctor.obj O

private abbrev kernelIdealSheafOnX
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    SheafOfModules (ringSheaf SiteX O') :=
  @kernelIdealSheaf (Opens X) _ SiteX _ O O' π

private abbrev kernelIdealSheafInclusionOnX
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    kernelIdealSheafOnX π ⟶ unitModule SiteX O' :=
  @kernelIdealSheafInclusion (Opens X) _ SiteX _ O O' π

/-- The intrinsic kernel ideal sheaf of `π`, viewed as a sheaf of abelian groups on `X`. -/
private abbrev kernelIdealUnderlyingSheaf
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    X.Sheaf AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringSheaf SiteX O')).obj (kernelIdealSheafOnX π)

private abbrev structureSheafUnderlyingMap
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    underlyingAdditiveSheaf O' ⟶ underlyingAdditiveSheaf O :=
  underlyingAdditiveSheafFunctor.map π

private theorem kernelIdealUnderlying_zero_comp
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    ((SheafOfModules.toSheaf (ringSheaf SiteX O')).map
        (kernelIdealSheafInclusionOnX π) :
          kernelIdealUnderlyingSheaf π ⟶ underlyingAdditiveSheaf O') ≫
      structureSheafUnderlyingMap π = 0 := by
  sorry

private abbrev kernelIdealUnderlyingShortComplex
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) :
    ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk
    ((SheafOfModules.toSheaf (ringSheaf SiteX O')).map
      (kernelIdealSheafInclusionOnX π) :
        kernelIdealUnderlyingSheaf π ⟶ underlyingAdditiveSheaf O')
    (structureSheafUnderlyingMap π)
    (kernelIdealUnderlying_zero_comp π)

private theorem kernelIdealUnderlyingShortComplex_shortExact
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) [Epi π] :
    (kernelIdealUnderlyingShortComplex π).ShortExact := by
  sorry

/-- The additive global section underlying a global section of a sheaf of commutative rings. -/
private noncomputable abbrev sectionToUnderlyingAdditiveGlobalSection
    (O : X.Sheaf CommRingCat.{u})
    (r : (Γ SiteX CommRingCat.{u}).obj O) :
    (Γ SiteX AddCommGrpCat.{u}).obj (underlyingAdditiveSheaf O) :=
  (Sheaf.ΓNatIsoSheafSections SiteX AddCommGrpCat.{u}
    (Preorder.isTerminalTop (Opens X))).inv.app (underlyingAdditiveSheaf O)
      (ΓRes O (op (⊤ : Opens X)) r)

/-- The morphism from the constant integer sheaf classified by a global section of `O`. -/
private noncomputable abbrev sectionToConstantIntegerSheafHom
    (O : X.Sheaf CommRingCat.{u})
    (r : (Γ SiteX CommRingCat.{u}).obj O) :
    constantIntegerSheaf X ⟶ underlyingAdditiveSheaf O :=
  (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHom X
    (underlyingAdditiveSheaf O)) (sectionToUnderlyingAdditiveGlobalSection O r)

private theorem kernelIdealModuleUnderlyingSheaf_eq
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) (s : O ⟶ O') :
    (moduleUnderlyingSheaf O.toRingedSpace).obj (kernelIdealSheafModule π s) =
      kernelIdealUnderlyingSheaf π :=
  rfl

private theorem kernelIdealModuleUnderlyingCohomology_carrier_eq
    {O' O : X.Sheaf CommRingCat.{u}} (π : O' ⟶ O) (s : O ⟶ O') :
    ↑((((moduleUnderlyingSheaf O.toRingedSpace).obj (kernelIdealSheafModule π s)).H' 1
        (⊤ : Opens X)) : AddCommGrpCat.{u}) =
      (kernelIdealUnderlyingSheaf π).H 1 := by
  sorry

/-- A derivation `D : Γ(X, 𝒪) → H¹(X, Ker π)` represents the square-zero boundary map if it
matches the boundary class attached to every global section of `𝒪`, after forgetting the
canonical `Γ(X, 𝒪)`-module structure on `H¹(X, Ker π)` coming from the descended kernel module
along a chosen section `s : 𝒪 ⟶ 𝒪'`. -/
def RepresentsSquareZeroBoundaryMap
    {O' O : X.Sheaf CommRingCat.{u}}
    [HasSheafify SiteX AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    {π : O' ⟶ O} [Epi π]
    [HasInjectiveResolutions (RingedSpace.Modules O.toRingedSpace)]
    (s : O ⟶ O')
    (D : Derivation ℤ (globalSectionsRing O.toRingedSpace)
      (moduleCohomologyAtOpen (⊤ : Opens O.toRingedSpace.carrier) (kernelIdealSheafModule π s)
        1)) :
    Prop :=
  ∀ r : globalSectionsRing O.toRingedSpace,
    (eqToIso
        (moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology
          (⊤ : Opens O.toRingedSpace.carrier)
          (kernelIdealSheafModule π s) 1)).hom (D r) =
      (by
        let rΓ : (Γ SiteX CommRingCat.{u}).obj O :=
          (Sheaf.ΓNatIsoSheafSections SiteX CommRingCat.{u}
            (Preorder.isTerminalTop (Opens X))).inv.app O r
        let extClass := (kernelIdealUnderlyingShortComplex_shortExact π).extClass
        exact Eq.mp
          (kernelIdealModuleUnderlyingCohomology_carrier_eq π s).symm
          ((extClass.postcomp (constantIntegerSheaf X) (rfl : 0 + 1 = 1))
            ((Abelian.Ext.addEquiv₀).symm (sectionToConstantIntegerSheafHom O rΓ))))

/-- Lemma 20.25.5: for a square-zero extension `π : 𝒪' ⟶ 𝒪`, the boundary map of
`0 ⟶ Ker π ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` is represented by a derivation
`Γ(X, 𝒪) → H¹(X, Ker π)`. Relative to a chosen section `s : 𝒪 ⟶ 𝒪'` of `π`, the codomain is
the canonical top-open module cohomology owner of the descended kernel module
`kernelIdealSheafModule π s`. -/
@[stacks 0B8S]
theorem exists_derivation_of_square_zero_boundary_map
    {O' O : X.Sheaf CommRingCat.{u}}
    [HasSheafify SiteX AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    {π : O' ⟶ O} [Epi π]
    [HasInjectiveResolutions (RingedSpace.Modules O.toRingedSpace)]
    (s : O ⟶ O') (hs : s ≫ π = 𝟙 O)
    (hzero : KernelSquareZero π) :
    ∃ D : Derivation ℤ (globalSectionsRing O.toRingedSpace)
      (moduleCohomologyAtOpen (⊤ : Opens O.toRingedSpace.carrier) (kernelIdealSheafModule π s)
        1),
      RepresentsSquareZeroBoundaryMap s D := by
  let _ := hs
  let _ := hzero
  sorry

end TopologicalSpace.SheafCohomology
