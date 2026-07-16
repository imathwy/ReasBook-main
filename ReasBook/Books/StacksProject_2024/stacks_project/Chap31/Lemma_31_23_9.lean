import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap31.ClosedImmersionIdealSubobject
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

local notation "OpensX" => TopologicalSpace.Opens X.toTopCat
local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "𝒪X" => (SheafOfModules.unit (ringSheaf JX X.𝒪) : ModX)
local notation "MerModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.meromorphicFunctionSheaf
local notation "KX" =>
  (SheafOfModules.unit (ringSheaf JX X.toLocallyRingedSpace.meromorphicFunctionSheaf) : MerModX)
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

private abbrev meromorphicSectionSheafFunctorX : ModX ⥤ MerModX :=
  X.toLocallyRingedSpace.meromorphicSectionSheafFunctor

private abbrev toMeromorphicFunctionRingSheafMap :
    ringSheaf JX X.𝒪 ⟶
      ((𝟭 OpensX).sheafPushforwardContinuous RingCat.{u} JX JX).obj
        (ringSheaf JX X.toLocallyRingedSpace.meromorphicFunctionSheaf) :=
  @ringedSiteStructureMap OpensX _ JX _ X.𝒪 X.toLocallyRingedSpace.meromorphicFunctionSheaf
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom

private abbrev meromorphicSectionSheafUnitMap :
    X.toLocallyRingedSpace.meromorphicSectionSheaf 𝒪X ⟶ KX :=
  @SheafOfModules.pullbackObjUnitToUnit OpensX _ OpensX _ JX JX (𝟭 OpensX)
    (ringSheaf JX X.𝒪) (ringSheaf JX X.toLocallyRingedSpace.meromorphicFunctionSheaf) _
    toMeromorphicFunctionRingSheafMap _ _ _

namespace IdealSheafData

/-- The ideal sheaf underlying `X.IdealSheafData`, viewed canonically as a subobject of
`\mathcal O_X`. -/
abbrev idealSheaf (D : X.IdealSheafData) : Subobject 𝒪X :=
  closedImmersionIdealSubobject D.subschemeι

/-- The `\mathcal O_X`-module sheaf underlying `D.idealSheaf`. -/
abbrev idealModule (D : X.IdealSheafData) : ModX :=
  Subobject.underlying.obj D.idealSheaf

/-- The canonical inclusion `\mathcal I \to \mathcal O_X` attached to `D.idealSheaf`. -/
abbrev idealSheafArrow (D : X.IdealSheafData) : D.idealModule ⟶ 𝒪X :=
  D.idealSheaf.arrow

end IdealSheafData

-- Semantic recall: Chapter 31 already provides the canonical owner
-- `X.toLocallyRingedSpace.meromorphicSections ℒ` for meromorphic sections and
-- `X.toLocallyRingedSpace.meromorphicSectionMap ℒ s` for the induced meromorphic-sheaf morphism,
-- while Chapter 17 already provides the canonical module-sheaf owners
-- `SheafOfModules.IsQuasicoherent` and `SheafOfModules.support`. For the denominator ideal
-- itself, Chapter 30/31 already uses the scheme-level canonical owner `Scheme.IdealSheafData`,
-- and the underlying ideal subsheaf of `𝒪_X` is recovered by `closedImmersionIdealSubobject`.

/-- A module sheaf on `X` has closed nowhere dense support. -/
abbrev HasClosedNowhereDenseSupport (ℱ : ModX) : Prop :=
  IsClosed (SheafOfModules.support ℱ) ∧
    IsNowhereDense (SheafOfModules.support ℱ)

/-- The denominator-section compatibility condition from Lemma 31.23.9, stated on the canonical
scheme-level ideal-sheaf owner and its induced map into `\mathcal L`. -/
abbrev IsDenominatorSectionMap
    [MonoidalCategory ModX]
    (D : X.IdealSheafData)
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (sectionMap : D.idealModule ⟶ ℒ) : Prop :=
  meromorphicSectionSheafFunctorX.map sectionMap =
    meromorphicSectionSheafFunctorX.map D.idealSheafArrow ≫
      meromorphicSectionSheafUnitMap ≫
      X.toLocallyRingedSpace.meromorphicSectionMap ℒ s

/-- A morphism of `\mathcal O_X`-modules has cokernel supported on a closed nowhere dense subset
of `X`. -/
abbrev HasClosedNowhereDenseCokernel {A B : ModX} (f : A ⟶ B) : Prop :=
  HasClosedNowhereDenseSupport (cokernel f)

/-- Lemma 31.23.9: for a scheme `X`, an invertible `\mathcal O_X`-module `\mathcal L`, and a
regular meromorphic section `s`, the source-defined denominator ideal sheaf is recorded through
the canonical scheme-level owner `X.IdealSheafData`; its underlying ideal submodule
`\mathcal I \subset \mathcal O_X`, recovered as `h.idealSheaf`, carries the induced map
`s : \mathcal I \to \mathcal L`, and both cokernels are supported on closed nowhere dense subsets
of `X`. The inclusion `1 : \mathcal I \to \mathcal O_X` is recovered canonically from the
subobject structure. -/
structure RegularMeromorphicSectionIdealSheaf
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) where
  /-- The denominator ideal sheaf recorded through the canonical scheme-level ideal-sheaf owner.
  The underlying ideal subsheaf of `\mathcal O_X` is `h.idealSheaf`. -/
  denominatorIdeal : X.IdealSheafData
  /-- Multiplication by the meromorphic section `s` on the denominator ideal. -/
  sectionMap : denominatorIdeal.idealModule ⟶ ℒ
  /-- After extension of scalars to meromorphic sections, `sectionMap` is multiplication by the
  chosen meromorphic section `s`. -/
  sectionMap_meromorphicSectionSheaf_eq :
    IsDenominatorSectionMap denominatorIdeal ℒ s sectionMap
  /-- The induced map `s : \mathcal I \to \mathcal L` is injective. -/
  sectionMap_mono : Mono sectionMap
  /-- The cokernel of `1 : \mathcal I \to \mathcal O_X` is supported on a closed nowhere dense
  subset of `X`. -/
  inclusionCokernel_hasClosedNowhereDenseSupport :
    HasClosedNowhereDenseCokernel denominatorIdeal.idealSheafArrow
  /-- The cokernel of `s : \mathcal I \to \mathcal L` is supported on a closed nowhere dense
  subset of `X`. -/
  sectionMapCokernel_hasClosedNowhereDenseSupport :
    HasClosedNowhereDenseCokernel sectionMap

namespace RegularMeromorphicSectionIdealSheaf

/-- The ideal subsheaf `\mathcal I \subset \mathcal O_X` attached to a regular meromorphic
section, recovered from the canonical scheme-level ideal-sheaf data. -/
abbrev idealSheaf
    [MonoidalCategory ModX]
    {ℒ : ModX} [IsInvertibleX ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) :
    Subobject 𝒪X :=
  h.denominatorIdeal.idealSheaf

/-- The `\mathcal O_X`-module sheaf underlying the denominator ideal `h.idealSheaf`. -/
abbrev idealModule
    [MonoidalCategory ModX]
    {ℒ : ModX} [IsInvertibleX ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) : ModX :=
  h.denominatorIdeal.idealModule

/-- The canonical inclusion `1 : \mathcal I \to \mathcal O_X` attached to the denominator ideal
of a regular meromorphic section. -/
abbrev idealSheafArrow
    [MonoidalCategory ModX]
    {ℒ : ModX} [IsInvertibleX ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) :
    h.idealModule ⟶ 𝒪X :=
  h.denominatorIdeal.idealSheafArrow

end RegularMeromorphicSectionIdealSheaf

/-- Lemma 31.23.9: a regular meromorphic section admits a denominator ideal sheaf with the
canonical quasi-coherence and support properties formalized by
`RegularMeromorphicSectionIdealSheaf`. -/
@[stacks 02P0]
theorem exists_regularMeromorphicSectionIdealSheaf
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    ∃ h : RegularMeromorphicSectionIdealSheaf ℒ s,
      h.idealModule.IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme
