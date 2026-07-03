import Mathlib
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

/-- Restriction of `\mathcal O`-modules from `(\mathcal C, \mathcal O)` to the localized ringed
site `(\mathcal C/U, J.over U, \mathcal O_U)`. -/
private abbrev localizedRestriction {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :
    RingedSiteModules J 𝒪 ⥤ LocalizedRingedSiteModules J 𝒪 U :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪).over U))

/-- The ambient module category on a ringed site uses the preadditive structure induced by any
abelian structure. -/
private instance instPreadditiveRingedSiteModules {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :
    Preadditive (RingedSiteModules J 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules J 𝒪)).toPreadditive

/-- The localized module category on a ringed site uses the preadditive structure induced by any
abelian structure. -/
private instance instPreadditiveLocalizedRingedSiteModules {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)
    [Abelian (LocalizedRingedSiteModules J 𝒪 U)] :
    Preadditive (LocalizedRingedSiteModules J 𝒪 U) :=
  (inferInstance : Abelian (LocalizedRingedSiteModules J 𝒪 U)).toPreadditive

section PerfectAndPseudoCoherent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, (localizedRestriction J 𝒪 U).PreservesZeroMorphisms]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [∀ U : C, CategoryWithHomology (LocalizedRingedSiteModules J 𝒪 U)]

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

/-- Restriction of complexes of `\mathcal O`-modules to the localized ringed site over `U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (LocalizedRingedSiteModules J 𝒪 U) ℤ :=
  (localizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)

namespace CochainComplex

/-- A complex of `\mathcal O`-modules on a ringed site is `m`-pseudo-coherent if, after passing
to a covering of every object, its restriction is approximated by a strictly perfect complex
inducing cohomology isomorphisms above `m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent (E : Cpx) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (LocalizedRingedSiteModules J 𝒪 I.Y) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `\mathcal O`-modules on a ringed site is pseudo-coherent if it is
`m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (E : Cpx) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

end CochainComplex

variable [Abelian Mod]

namespace DerivedCategory

/-- An object of `D(\mathcal O)` is pseudo-coherent if it is represented by a pseudo-coherent
complex of `\mathcal O`-modules. -/
def IsPseudoCoherent (E : DMod) : Prop :=
  ∃ K : Cpx, CochainComplex.IsPseudoCoherent K ∧
    ∃ α : ((DerivedCategory.Q : Cpx ⥤ DMod).obj K) ⟶ E, IsIso α

end DerivedCategory

end PerfectAndPseudoCoherent

section LocalTorDimension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Abelian (RingedSiteModules J 𝒪)]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [∀ U : C, Abelian (LocalizedRingedSiteModules J 𝒪 U)]
variable [∀ U : C, CategoryWithHomology (LocalizedRingedSiteModules J 𝒪 U)]
variable [∀ U : C, MonoidalCategory (DerivedCategory (LocalizedRingedSiteModules J 𝒪 U))]
variable [∀ U : C, (localizedRestriction J 𝒪 U).Additive]
variable [∀ U : C,
  Functor.HasRightDerivedFunctor
    (((localizedRestriction J 𝒪 U).mapHomotopyCategory (up ℤ)) ⋙
      (show HomotopyCategory (LocalizedRingedSiteModules J 𝒪 U) (up ℤ) ⥤
          DerivedCategory (LocalizedRingedSiteModules J 𝒪 U) from
        @DerivedCategory.Qh (LocalizedRingedSiteModules J 𝒪 U) _ _ _))
    (HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ))]

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod
local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

/-- The right derived restriction functor from `D(\mathcal O)` to `D(\mathcal O_U)`. -/
private noncomputable abbrev localizedRestrictionDerived (U : C) :
    DMod ⥤ DerivedCategory (ModLoc U) :=
  Functor.totalRightDerived
    (((localizedRestriction J 𝒪 U).mapHomotopyCategory (up ℤ)) ⋙
      (show HomotopyCategory (ModLoc U) (up ℤ) ⥤
          DerivedCategory (ModLoc U) from
        @DerivedCategory.Qh (ModLoc U) _ _ _))
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso Mod (up ℤ))

/-- An object of `D(\mathcal O)` locally has finite tor dimension if every object admits a cover
on whose members the restriction has finite tor amplitude in some interval. -/
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ a b : ℤ, ∀ (ℱ : ModLoc I.Y) (i : ℤ), i ∉ Set.Icc a b →
      IsZero
        ((DerivedCategory.homologyFunctor (ModLoc I.Y) i).obj
          (((localizedRestrictionDerived I.Y).obj E) ⊗
            ((DerivedCategory.singleFunctor (ModLoc I.Y) (0 : ℤ)).obj ℱ)))

end LocalTorDimension

section Main

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, (localizedRestriction J 𝒪 U).PreservesZeroMorphisms]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [∀ U : C, CategoryWithHomology (LocalizedRingedSiteModules J 𝒪 U)]
variable [∀ U : C, MonoidalCategory (DerivedCategory (LocalizedRingedSiteModules J 𝒪 U))]
variable [∀ U : C, (localizedRestriction J 𝒪 U).Additive]
variable [∀ U : C,
  Functor.HasRightDerivedFunctor
    (((localizedRestriction J 𝒪 U).mapHomotopyCategory (up ℤ)) ⋙
      (show HomotopyCategory (LocalizedRingedSiteModules J 𝒪 U) (up ℤ) ⥤
          DerivedCategory (LocalizedRingedSiteModules J 𝒪 U) from
        @DerivedCategory.Qh (LocalizedRingedSiteModules J 𝒪 U) _ _ _))
    (HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ))]

local notation "DMod" => DerivedCategory (RingedSiteModules J 𝒪)

-- Proof sketch: for the forward implication, unfold perfectness and work on a cover where `E` is
-- represented by a strictly perfect complex; this yields pseudo-coherence and local finite tor
-- dimension. For the reverse implication, refine covers so that locally `E` has tor amplitude in
-- some interval `[a, b]`; pseudo-coherence gives the corresponding local approximation by strictly
-- perfect complexes, and the bounded tor-amplitude criterion then implies local perfectness.
/-- Lemma 21.47.4: for an object `E` of `D(\mathcal O)` on a ringed site, `E` is perfect if and
only if it is pseudo-coherent and locally has finite Tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DMod) :
    DerivedCategory.IsPerfect E ↔
      DerivedCategory.IsPseudoCoherent E ∧
        LocallyHasFiniteTorDimension E := sorry

end Main

end SheafOfModules.RingedSite
