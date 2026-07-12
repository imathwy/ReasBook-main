import StacksProject_2024.Chap20.Lemma_20_6_1
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Lemma_21_49_2

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite
open TopologicalSpace
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.52.2:
- primary domain: invertible objects of `D(𝒪_X)` on a ringed space, their perfectness,
  and their local shifted-invertible description after passing to the opens ringed site;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.ModuleDerived`,
  `Functor.IsEquivalence (tensorRight M)`,
  `RingedSite.ofCommRingSheaf`,
  `SheafOfModules.RingedSite.LocallyIsomorphicToShiftedInvertibleModule`,
  `SheafOfModules.RingedSite
    .isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule_of_isLocallyRingedSite`,
  `AlgebraicGeometry.RingedSpace.instOpensSheafIsLocallyRingedSiteOfStalkIsLocalRing`;
- best owner abstraction:
  `source-facing`: the Chapter 20 ringed-space wording for `D(𝒪_X)`;
  `core/canonical`: the Chapter 21 local-criterion owner
    `LocallyIsomorphicToShiftedInvertibleModule` on the opens ringed site of `X`;
  `bridge/view`: specialization of that owner to the opens ringed site
    `RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf`, together with the
    stalk-local to `IsLocallyRingedSite` instance from Lemma `20.6.1`;
- primitive data:
  the canonical opens ringed site of `X` and the stalk-local ring hypothesis on `X`;
- derived API:
  the source-facing Chapter 20 bridge statement below, expressed directly using the canonical
  Chapter 21 local-criterion owner rather than a second local wrapper definition.

This file stays at the `bridge/view` layer and specializes the canonical Chapter 21 owner
data on the opens ringed site of `X`, but its public Chapter 20 surface is phrased using the
intrinsic owner `ModuleDerived X`; the stalk-local to `IsLocallyRingedSite` bridge is supplied by
the instance from Lemma `20.6.1`. -/

/- Lemma 20.52.2: the local shifted-invertible criterion already has the canonical Chapter 21
owner `LocallyIsomorphicToShiftedInvertibleModule` on a ringed site. This Chapter 20 file is only
the ringed-space bridge obtained by viewing `X` as the canonical opens ringed site and supplying
the stalkwise local-ring hypothesis needed for local instance inference of
`IsLocallyRingedSite X.sheaf`. -/

section

variable {X : RingedSpace.{u}}

variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X,
  MonoidalCategory (ModuleCat ((opensRingedSite X).localization U))]
variable [MonoidalCategory (ModuleDerived X)]
variable [∀ U : Opens X,
  (localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : Opens X,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : Opens X,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)]

/-- Ambient-instance companion: on a ringed space whose stalk rings are local, invertibility in
`D(𝒪_X)` is equivalent to the Chapter 21 local shifted-invertible owner on the opens ringed site
of `X`. -/
theorem isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (M : ModuleDerived X) :
    Functor.IsEquivalence (tensorRight M) ↔
      LocallyIsomorphicToShiftedInvertibleModule M := by
  let _ : IsLocallyRingedSite X.sheaf := inferInstance
  let Msite : RingedSite.Hom.ModuleDerived (opensRingedSite X) := M
  simpa using
    (SheafOfModules.RingedSite.isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule_of_isLocallyRingedSite
      Msite)

/-- Lemma 20.52.2: if all stalk rings of `X` are local, then an object of `D(𝒪_X)` is
invertible exactly when, after restricting to a cover of every open, it becomes isomorphic to an
invertible local module placed in a single shifted degree locally on `X`. This is the ringed-space
specialization of the Chapter 21 owner theorem
`isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule_of_isLocallyRingedSite`. -/
@[stacks 0FPG]
theorem isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule_of_stalk_isLocalRing
    (M : ModuleDerived X)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    Functor.IsEquivalence (tensorRight M) ↔
      LocallyIsomorphicToShiftedInvertibleModule M := by
  let _ : ∀ x : X, IsLocalRing (X.presheaf.stalk x) := hlocal
  simpa using isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule M

end

end AlgebraicGeometry.RingedSpace
