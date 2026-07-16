import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_1
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Lemma_21_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open AlgebraicGeometry
open RingedSite (Hom)
open RingedSite.Hom (ModuleCat localizedRestriction)
open TopologicalSpace
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

open ModuleDerived
local notation "DModY" => ModuleDerived Y
local notation:65 K:65 ".IsMPseudoCoherent " m:66 =>
  IsMPseudoCoherent K m

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [HasBinaryProducts (opensRingedSite Y).carrier]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : (opensRingedSite X).carrier, (localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite Y).carrier, (localizedRestriction (opensRingedSite Y) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite Y).carrier,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite Y) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite Y).carrier,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite Y) U)]
variable [∀ U : (opensRingedSite X).carrier,
  HasBinaryProducts ((opensRingedSite X).localization U).carrier]
variable [∀ U : (opensRingedSite X).carrier,
  HasWeakSheafify ((opensRingedSite X).localization U).siteTopology AddCommGrpCat.{u}]
variable [∀ U : (opensRingedSite X).carrier,
  ((opensRingedSite X).localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : (opensRingedSite X).carrier, ∀ V : (opensRingedSite X).localization U,
  (localizedRestriction ((opensRingedSite X).localization U) V).Additive]
variable [∀ U : (opensRingedSite X).carrier, ∀ V : (opensRingedSite X).localization U,
  PreservesFiniteLimits (localizedRestriction ((opensRingedSite X).localization U) V)]
variable [∀ U : (opensRingedSite X).carrier, ∀ V : (opensRingedSite X).localization U,
  PreservesFiniteColimits (localizedRestriction ((opensRingedSite X).localization U) V)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (ModuleCat ((opensRingedSite X).localization U))]
variable [∀ U : (opensRingedSite X).carrier, ∀ V : (opensRingedSite X).localization U,
  CategoryWithHomology (ModuleCat (((opensRingedSite X).localization U).localization V))]
variable [∀ U : (opensRingedSite Y).carrier,
  CategoryWithHomology (ModuleCat ((opensRingedSite Y).localization U))]

namespace ModuleDerived

open RingedSite.Hom.ModuleDerived.IsMPseudoCoherent

local notation "ringedSitePullbackImported" =>
  @pullback

/- Domain-style sampling for Lemma 20.47.3:
- primary domain: derived pullback of sheaves of modules on ringed spaces and preservation of
  local pseudo-coherence;
- sampled owner declarations:
  `ModuleDerived`,
  `IsMPseudoCoherent`,
  `modulePullbackDerived`,
  the Chapter 21 ringed-site pullback theorem,
  `isMPseudoCoherent_iff_exists_openCover`;
- best owner abstraction: this theorem is source-facing over the canonical owners
  `modulePullbackDerived f : ModuleDerived Y ⥤ ModuleDerived X` and `IsMPseudoCoherent`; it
  should specialize the Chapter 21 ringed-site owner theorem on the opens ringed site rather than
  introduce a parallel pullback or pseudo-coherence wrapper;
- primitive vs. derived:
  primitive data are the morphism `f`, the derived object `E`, and the owner witness
  `IsMPseudoCoherent E m`;
  the preservation statement below is derived API;
- source/core/bridge triage:
  `source-facing`: derived pullback preserves `m`-pseudo-coherence on ringed spaces;
  `core/canonical`: `ModuleDerived`, `modulePullbackDerived`, and `IsMPseudoCoherent`;
  `bridge/view`: the surface notation `L(f)^*` for `modulePullbackDerived f` and the open-cover
  criterion `isMPseudoCoherent_iff_exists_openCover`.
- layer: this file is source-facing over canonical owners, so the theorem surface should reuse
  those owners directly and keep the pullback notation only as surface syntax. -/

/-- Lemma 20.47.3: if an object `E` of `D(𝒪_Y)` is `m`-pseudo-coherent, then the
derived pullback `L(f)^* E` is `m`-pseudo-coherent in `D(𝒪_X)`. -/
@[stacks 09U7]
theorem IsMPseudoCoherent.pullback
    (f : X ⟶ Y) [(f^*).Additive] {E : DModY} {m : ℤ}
    (hE : E.IsMPseudoCoherent m) :
    ((L(f)^*).obj E).IsMPseudoCoherent m :=
  let ringedSitePullback : E.IsMPseudoCoherent m → ((L(f)^*).obj E).IsMPseudoCoherent m :=
    ringedSitePullbackImported (opensRingedSiteHom f)
      _ _
      (show
          ∀ U : (opensRingedSite X).carrier,
            (localizedRestriction (opensRingedSite X) U).Additive from
        inferInstanceAs
          (∀ U : (opensRingedSite X).carrier,
            (localizedRestriction (opensRingedSite X) U).Additive))
      (show
          ∀ U : (opensRingedSite Y).carrier,
            (localizedRestriction (opensRingedSite Y) U).Additive from
        inferInstanceAs
          (∀ U : (opensRingedSite Y).carrier,
            (localizedRestriction (opensRingedSite Y) U).Additive))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      E
      m
  -- The Chapter 21 owner theorem is the canonical source of this result, with the localized
  -- additivity instances pinned in the opens-site specialization.
  ringedSitePullback hE

end ModuleDerived

end

end AlgebraicGeometry.RingedSpace
