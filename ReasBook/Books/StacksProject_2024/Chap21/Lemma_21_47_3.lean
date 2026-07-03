import Mathlib
import StacksProject_2024.Chap21.Definition_21_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option linter.unusedSectionVars false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteModuleCategory (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

/-- Restriction of `\mathcal O`-modules from `(\mathcal C, \mathcal O)` to the localized ringed
site `(\mathcal C/U, J.over U, \mathcal O_U)`. -/
private abbrev localizedRestriction (U : C) :
    Mod ⥤ ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))
variable [∀ U : C, (@localizedRestriction C _ J _ 𝒪 U).PreservesZeroMorphisms]
variable [CategoryWithHomology Mod]
variable [∀ U : C, CategoryWithHomology (ringedSiteModuleCategory (J.over U) (𝒪.over U))]

/-- Restriction of complexes of `\mathcal O`-modules to the localized ringed site over `U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (ringedSiteModuleCategory (J.over U) (𝒪.over U)) ℤ :=
  (@localizedRestriction C _ J _ 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)

namespace CochainComplex

/-- A complex of `\mathcal O`-modules on a ringed site is `(a - 1)`-pseudo-coherent if each object
admits a covering on whose members the restriction is approximated by a strictly perfect complex
that is a cohomology isomorphism in degrees `> a - 1` and an epimorphism in degree `a - 1`. -/
def IsMPseudoCoherent (E : Cpx) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ringedSiteModuleCategory (J.over I.Y) (𝒪.over I.Y)) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

end CochainComplex

variable [Abelian Mod]

namespace DerivedCategory

/-- An object of `D(\mathcal O)` is `(a - 1)`-pseudo-coherent if it is represented by an
`(a - 1)`-pseudo-coherent complex of `\mathcal O`-modules. -/
def IsMPseudoCoherent (E : DMod) (m : ℤ) : Prop :=
  ∃ K : Cpx, CochainComplex.IsMPseudoCoherent K m ∧
    ∃ α : ((DerivedCategory.Q : Cpx ⥤ DMod).obj K) ⟶ E, IsIso α

end DerivedCategory

variable [MonoidalCategoryStruct (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

local notation "SiteIsMPseudoCoherent" => DerivedCategory.IsMPseudoCoherent
local notation "SiteIsPerfect" => DerivedCategory.IsPerfect

/-- An object of `D(\mathcal O)` has tor-amplitude in `[a, b]` if derived tensoring with any
degree-zero `\mathcal O`-module has vanishing homology outside that interval. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor Mod i).obj
      (E ⊗ ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ)))

local notation "SiteHasTorAmplitudeIn" => HasTorAmplitudeIn

/-- Lemma 21.47.3: let `(\mathcal C, \mathcal O)` be a ringed site, let `E` be an object of
`D(\mathcal O)`, and let `a ≤ b` be integers. If `E` has tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, then `E` is perfect. -/
def isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : DMod) (a b : ℤ) : Prop :=
  a ≤ b →
    SiteHasTorAmplitudeIn E a b →
      SiteIsMPseudoCoherent E (a - 1) →
        SiteIsPerfect E

end

end SheafOfModules.RingedSite

namespace SheafOfModules.RingedSite

-- Proof sketch: apply the implication packaged by
-- `isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent` to the hypotheses `a ≤ b`,
-- `HasTorAmplitudeIn E a b`, and `DerivedCategory.IsMPseudoCoherent E (a - 1)`.
/-- Applying `isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent` to its hypotheses yields the
resulting perfection statement. -/
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent_apply
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [∀ U : C, ((J.over U).HasSheafCompose
      (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
    [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [∀ U : C, (@localizedRestriction C _ J _ 𝒪 U).PreservesZeroMorphisms]
    [∀ U : C, CategoryWithHomology (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
    [MonoidalCategoryStruct (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
    (E : DerivedCategory (ringedSiteModuleCategory J 𝒪)) (a b : ℤ)
    (h : isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent E a b)
    (hab : a ≤ b)
    (hTor : HasTorAmplitudeIn E a b)
    (hPseudo : DerivedCategory.IsMPseudoCoherent E (a - 1)) :
    DerivedCategory.IsPerfect E := sorry

end SheafOfModules.RingedSite
