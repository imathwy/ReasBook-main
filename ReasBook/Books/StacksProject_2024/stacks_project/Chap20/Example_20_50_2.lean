import StacksProject_2024.stacks_project.Chap20.Example_20_50_2_Core
import StacksProject_2024.stacks_project.Chap21.Example_21_48_2
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CochainComplex
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Example 20.50.2:
- primary domain: closed-monoidal duality for complexes of `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyStrictlyPerfect`,
  `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`,
  `AlgebraicGeometry.RingedSpace.cochainComplex_isLocallyStrictlyPerfect_iff_site`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexDualCoevaluation`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexDualEvaluation`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexDual_coevaluation_evaluation`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexDual_evaluation_coevaluation`;
- best owner abstraction:
  `source-facing`: the Chapter 20 ringed-space hypothesis
    `CochainComplex.IsLocallyStrictlyPerfect F`, together with the resulting left-dual triangle
    identities for `F^∨`;
  `core/canonical`: the ringed-site duality maps and triangle identities for `F^∨`;
  `bridge/view`: the equivalence
    `cochainComplex_isLocallyStrictlyPerfect_iff_site`.
- primitive data: the ringed-space local strict-perfectness hypothesis on `F`;
- derived API: the Chapter 20 specialization is obtained by feeding the bridge theorem into the
  Chapter 21 duality theorems, without introducing a parallel ringed-space owner.

Source/core/bridge triage:
- `source-facing`: Example 20.50.2 for a complex on a ringed space;
- `core/canonical`: the Chapter 21 duality-map bundle on the ringed-site surface;
- `bridge/view`: `cochainComplex_isLocallyStrictlyPerfect_iff_site`.

Because the Chapter 21 duality laws still carry proof debt upstream, this file keeps the
source-faithful Chapter 20 specialization thin: it transports the hypothesis to the ringed-site
surface and reuses the canonical ringed-site duality morphisms and triangle-identity theorems
already exported there, instead of packaging any new data-bearing ringed-space duality owner
locally. -/

/- Example 20.50.2: if a complex `F` of `𝒪_X`-modules on a ringed space is locally strictly
perfect in the Chapter 20 open-cover sense, then the internal-Hom dual `F^∨`, together with the
canonical coevaluation and evaluation morphisms, satisfies the left-dual triangle identities. The
refined Lean surface records this through the two triangle identities, after transporting the
Chapter 20 hypothesis across `cochainComplex_isLocallyStrictlyPerfect_iff_site` and reusing the
theorem-level Chapter 21 duality API rather than exporting new ringed-space duality data. -/
/-- The Chapter 20 open-cover notion of local strict perfectness canonically transports to the
ringed-site formulation used by the duality API. -/
instance cochainComplex_isLocallyStrictlyPerfect_site
    {F : CpxX}
    [hF : CochainComplex.IsLocallyStrictlyPerfect F] :
    IsLocallyStrictlyPerfect F :=
  (cochainComplex_isLocallyStrictlyPerfect_iff_site F).1 hF

/-- Example 20.50.2, first triangle identity on a ringed space: if `F` is locally strictly
perfect in the Chapter 20 sense, then the canonical coevaluation and evaluation maps of `F^∨`
satisfy the left-dual identity on `F^∨`. -/
@[stacks 0FP9]
theorem ringedSpaceModuleComplexDual_coevaluation_evaluation
    [MonoidalCategory CpxX]
    [BraidedCategory CpxX]
    [MonoidalClosed CpxX]
    {F : CpxX}
    [CochainComplex.IsLocallyStrictlyPerfect F] :
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ =
      (ρ_ F^∨).hom ≫
        (λ_ F^∨).inv := by
  simpa using
    ringedSiteModuleComplexDual_coevaluation_evaluation_of_isLocallyStrictlyPerfect

/-- Example 20.50.2, second triangle identity on a ringed space: if `F` is locally strictly
perfect in the Chapter 20 sense, then the canonical coevaluation and evaluation maps of `F^∨`
satisfy the left-dual identity on `F`. -/
@[stacks 0FP9]
theorem ringedSpaceModuleComplexDual_evaluation_coevaluation
    [MonoidalCategory CpxX]
    [BraidedCategory CpxX]
    [MonoidalClosed CpxX]
    {F : CpxX}
    [CochainComplex.IsLocallyStrictlyPerfect F] :
    ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSiteModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := by
  simpa using
    ringedSiteModuleComplexDual_evaluation_coevaluation_of_isLocallyStrictlyPerfect

end AlgebraicGeometry.RingedSpace
