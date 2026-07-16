import StacksProject_2024.stacks_project.Chap21.Lemma_21_30_8
import StacksProject_2024.stacks_project.Chap21.Lemma_21_31_7
import StacksProject_2024.stacks_project.Chap21.«21_31_0_1»

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open TopologicalSpace
open scoped CategoryTheory
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 21.31.11:
- primary domain: bounded-below derived localization from the small Zariski site of
  `X ∈ LC_{qc}` to the localized qc site `LC_{qc}/X`;
- inspected owner declarations:
  `a[_, _]⁻¹`,
  `a[_, _]*`,
  `π[_, _]*`,
  `comparisonTopologyPushforwardDerived`,
  `lcZar_pi_derived_unit_isomorphic`,
  `comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn`;
- best owner abstraction: the source-facing lemma should stay on the Chapter 21 inverse image
  `a_X⁻¹` and the resulting direct image `R a_{X,*}`, with `a_{X,*}` owned by
  `a[hle, πFunctor X]*` and the comparison to `Rπ_{X,*} ∘ Rε_{X,*}` kept as a bridge;
  `K : D⁺((SmallAbSheaf X))`;
- derived API: the canonical comparison from `K` to
  `R a_{X,*}(a_X^{-1} K)`.

Source/core/bridge triage:
- `source-facing`: Lemma `21.31.11`;
- `core/canonical`: `a[_, _]⁻¹`, `a[_, _]*`, `comparisonTopologyPushforwardDerived`,
  `Functor.mapDerivedCategory`, `D⁺`, `lcZar_pi_derived_unit_isomorphic`, and
  `comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn`;
- `bridge/view`: the source identity `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}` is realized by the owner
  `a[hle, πFunctor X]⁻¹`, while the proof-level comparison between `R a_{X,*}` and
  `Rπ_{X,*} ∘ Rε_{X,*}` is isolated in a companion bridge theorem. -/

section

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (hle : τzar ≤ τqc)
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u}, Functor.Full (πFunctor X)]
variable [∀ X : LCCat.{u}, Functor.Faithful (πFunctor X)]
variable [∀ X : LCCat.{u},
  (πFunctor X).IsAlmostCocontinuous (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u}, HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u}, Abelian (SmallAbSheaf X)]
variable [∀ X : LCCat.{u}, IsGrothendieckAbelian (LCZarAbSheaf (τzar.over X))]
variable [∀ X : LCCat.{u}, IsGrothendieckAbelian (LCZarAbSheaf (τqc.over X))]

section Derived

variable (X : LCCat.{u})
local notation "πX*" => π[τzar.over X, πFunctor X]*
local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹
local notation "aX*" => a[hle, πFunctor X]*
local notation "RπX*" => additiveFunctorTotalRightDerived πX*
local notation "RεX*" => comparisonTopologyPushforwardDerived hle X
local notation "RaX*" => additiveFunctorTotalRightDerived aX*

attribute [local instance]
  comparisonTopologyPushforwardAb_additive
  mapHomologicalComplexQ_hasRightDerivedFunctor
  aInverseAb_additive
  aInverseAb_preservesFiniteLimits
  aInverseAb_preservesFiniteColimits

local instance : Preadditive (Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :=
  Abelian.toPreadditive

local instance : Preadditive (Sheaf (τqc.over X) AddCommGrpCat.{u + 1}) :=
  Abelian.toPreadditive

local instance : Preadditive (SmallAbSheaf X) :=
  Abelian.toPreadditive

variable [Functor.Additive (π[τzar.over X, πFunctor X]*)]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
  (HomotopyCategory.quasiIso
    (Sheaf (τqc.over X) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
variable [Functor.Additive (aInverseAb hle (πFunctor X))]
variable [PreservesFiniteLimits (aInverseAb hle (πFunctor X))]
variable [PreservesFiniteColimits (aInverseAb hle (πFunctor X))]

-- Proof sketch: combine the small-site derived unit
-- `K ⟶ Rπ_{X,*}(π_X^{-1} K)` from Lemma `21.31.7` with the Chapter `21.30.8`
-- comparison-unit theorem specialized to `π_X^{-1} K`, and then identify the resulting
-- bounded-below composite with the canonical source-facing derived direct image
-- `R a_{X,*}(a_X^{-1} K)`.
/-- Lemma 21.31.11: for `X ∈ LC_{qc}` and `K ∈ D^+(X)`, the small-site derived object `K` is
canonically isomorphic to `R a_{X,*}(a_X^{-1} K)`. The source-facing direct-image owner is
`a[hle, πFunctor X]*`; the intermediate comparison with the raw composite
`Rπ_{X,*} ∘ Rε_{X,*}` remains proof-side and is not promoted to a separate public bridge theorem,
since the Chapter `21.30` input is only used in this bounded-below source-specific setting. -/
@[stacks 0D91]
theorem smallDerived_isomorphic_localizationPushforward_aInverseDerived
    (K : D⁺((SmallAbSheaf X))) :
    IsIsomorphic
      K.toDerived
      ((RaX*).obj ((aX⁻¹.mapDerivedCategory).obj K.toDerived)) := by
  sorry

end Derived

end

end CategoryTheory.GrothendieckTopology
