import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_23_1
import stacks_project.Chap17.Definition_17_25_1
import stacks_project.Chap17.Lemma_17_25_2
import stacks_project.Chap17.Lemma_17_25_3
import stacks_project.Chap17.Lemma_17_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local notation "ModX" => ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf
local notation "ModY" => ringedSiteModuleCategory (Opens.grothendieckTopology Y) Y.sheaf
local notation "IsInvertibleX" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _
local notation "IsInvertibleY" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology Y) Y.sheaf _ _

namespace Hom

private instance pullbackObjUnitToUnit_isIso (f : X ⟶ Y) :
    IsIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f)) := by
  sorry

/-- The canonical pullback of a global section along a morphism of ringed spaces. -/
noncomputable abbrev pullbackSections (f : X ⟶ Y)
    {ℒ : RingedSpace.Modules Y} (s : ℒ.sections) :
    ((RingedSpace.Hom.pullback f).obj ℒ).sections :=
  ((RingedSpace.Hom.pullback f).obj ℒ).unitHomEquiv
    ((asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f))).inv ≫
      (RingedSpace.Hom.pullback f).map (ℒ.unitHomEquiv.symm s))

/-- The morphism corresponding to `f.pullbackSections s` under the global-sections/unit adjunction
is obtained by pulling back the morphism corresponding to `s` and transporting across the
canonical pullback of the unit object. -/
@[simp]
theorem unitHomEquiv_symm_pullbackSections (f : X ⟶ Y)
    {ℒ : RingedSpace.Modules Y} (s : ℒ.sections) :
    ((RingedSpace.Hom.pullback f).obj ℒ).unitHomEquiv.symm
        (RingedSpace.Hom.pullbackSections f s) =
      (asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f))).inv ≫
        (RingedSpace.Hom.pullback f).map (ℒ.unitHomEquiv.symm s) := by
  change
    ((RingedSpace.Hom.pullback f).obj ℒ).unitHomEquiv.symm
        (((RingedSpace.Hom.pullback f).obj ℒ).unitHomEquiv
          ((asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f))).inv ≫
            (RingedSpace.Hom.pullback f).map (ℒ.unitHomEquiv.symm s))) =
      (asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f))).inv ≫
        (RingedSpace.Hom.pullback f).map (ℒ.unitHomEquiv.symm s)
  exact Equiv.symm_apply_apply ((RingedSpace.Hom.pullback f).obj ℒ).unitHomEquiv _

end Hom

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

open AlgebraicGeometry.RingedSpace

variable {X Y : LocallyRingedSpace.{u}}

local notation:max f:max "^*" => RingedSpace.Hom.pullback (LocallyRingedSpace.Hom.toShHom f)
local notation "ModX" =>
  ringedSiteModuleCategory (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf
local notation "ModY" =>
  ringedSiteModuleCategory (Opens.grothendieckTopology Y.toRingedSpace) Y.toRingedSpace.sheaf
local notation "IsInvertibleX" =>
  @SheafOfModules.RingedSite.IsInvertible _ _
    (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf _ _
local notation "IsInvertibleY" =>
  @SheafOfModules.RingedSite.IsInvertible _ _
    (Opens.grothendieckTopology Y.toRingedSpace) Y.toRingedSpace.sheaf _ _
local notation "IsInvertible" => IsInvertibleX

/- Domain-style sampling for Remark 17.25.11:
- primary domain: nonvanishing loci of sections of invertible module sheaves under pullback along
  morphisms of locally ringed spaces;
- inspected owner declarations:
  `RingedSpace.sectionNonvanishingOpen`,
  `RingedSpace.sectionNonvanishingLocus`,
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pullbackSections`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.pullbackObjUnitToUnit`;
- best owner abstraction: the source-facing owner here is the nonvanishing locus/open of a
  section, while the pullback of sections is bridge data owned by the canonical pullback owner
  `RingedSpace.Hom.pullback`; the pulled-back section should therefore live in
  `RingedSpace.Hom`, and the main chapter statement here should be the source-facing open-subset
  identity on locally ringed spaces, with the underlying set-theoretic nonvanishing-locus
  equality kept only as a companion view;
- primitive data: a morphism `f : Y ⟶ X`, an `\mathcal O_X`-module `\mathcal L`, and a global
  section `s : \mathcal L(X)`;
- derived API: the equality identifying the inverse image open subset `X_s` with the pullback
  nonvanishing locus `Y_{f^*s}`, together with the canonical pullback-on-global-sections map and
  the companion equality of the corresponding open subsets when invertibility is available.

Source/core/bridge triage:
- `source-facing`: `sectionNonvanishingLocus` and its associated open subset
  `sectionNonvanishingOpen`;
- `core/canonical`: `RingedSpace.Hom.pullback`;
- `bridge/view`: `RingedSpace.Hom.pullbackSections` and the open-subset equality derived from the
  locus identity.
-/

private instance tensorLeft_isEquivalence_of_isInvertible
    [MonoidalCategory ModX] (ℒ : ModX) [IsInvertibleX ℒ] :
    Functor.IsEquivalence (tensorLeft ℒ) :=
  (AlgebraicGeometry.RingedSpace.isInvertible_iff_tensorLeft_isEquivalence ℒ).1 inferInstance

-- Proof sketch: the germ of the pulled-back section at `y : Y` is the image of the germ of `s`
-- at `f(y)` under base change along the local ring map
-- `\mathcal O_{X,f(y)} → \mathcal O_{Y,y}`. For an invertible module, nonvanishing is the
-- condition that the germ is not contained in the maximal-ideal multiple of the stalk, and this
-- condition is preserved and reflected by local base change.
/-- Companion to Remark 17.25.11: without using invertibility, the underlying nonvanishing loci
agree set-theoretically after pulling back the section along `f`. -/
theorem preimage_sectionNonvanishingLocus_eq_sectionNonvanishingLocus_pullback
    (f : Y ⟶ X) (ℒ : ModX)
    (s : ℒ.sections) :
    f.base ⁻¹' sectionNonvanishingLocus X.toRingedSpace ℒ s =
      sectionNonvanishingLocus Y.toRingedSpace ((f^*).obj ℒ)
        (RingedSpace.Hom.pullbackSections f.toShHom s) :=
  sorry

variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]
variable [SymmetricCategory (RingedSpace.Modules X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.Modules X.toRingedSpace)]
variable [∀ U : Opens X.toRingedSpace,
  MonoidalCategory
    (ringedSiteModuleCategory
      ((Opens.grothendieckTopology X.toRingedSpace).over U)
      (X.toRingedSpace.sheaf.over U))]
variable [∀ U : Opens X.toRingedSpace,
  MonoidalClosed
    (ringedSiteModuleCategory
      ((Opens.grothendieckTopology X.toRingedSpace).over U)
      (X.toRingedSpace.sheaf.over U))]
variable [MonoidalCategory (RingedSpace.Modules Y.toRingedSpace)]
variable [SymmetricCategory (RingedSpace.Modules Y.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.Modules Y.toRingedSpace)]
variable [∀ U : Opens Y.toRingedSpace,
  MonoidalCategory
    (ringedSiteModuleCategory
      ((Opens.grothendieckTopology Y.toRingedSpace).over U)
      (Y.toRingedSpace.sheaf.over U))]
variable [∀ U : Opens Y.toRingedSpace,
  MonoidalClosed
    (ringedSiteModuleCategory
      ((Opens.grothendieckTopology Y.toRingedSpace).over U)
      (Y.toRingedSpace.sheaf.over U))]

/-- Remark 17.25.11: for a morphism of locally ringed spaces `f : Y → X`, an invertible
`\mathcal O_X`-module `\mathcal L`, and a global section `s`, the inverse image open subset
`(X.toRingedSpace)_[s]` is the nonvanishing open subset
`(Y.toRingedSpace)_[f^*s]` cut out by the pulled-back section. -/
theorem comap_sectionNonvanishingOpen_eq_sectionNonvanishingOpen_pullback
    (f : Y ⟶ X)
    (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) :
    Opens.comap f.base.hom ((X.toRingedSpace)_[s]) =
      (Y.toRingedSpace)_[RingedSpace.Hom.pullbackSections f.toShHom s] := by
  apply TopologicalSpace.Opens.ext
  simpa using
    preimage_sectionNonvanishingLocus_eq_sectionNonvanishingLocus_pullback f ℒ s

end AlgebraicGeometry.LocallyRingedSpace
