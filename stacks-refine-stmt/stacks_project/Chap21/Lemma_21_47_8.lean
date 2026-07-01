import stacks_project.Chap21.Lemma_21_47_4

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

set_option checkBinderAnnotations false

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
abbrev RingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

/-- The module category on the localized ringed site `(\mathcal C/U, J.over U, \mathcal O_U)`. -/
abbrev LocalizedRingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :=
  SheafOfModules (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪).over U)

/-- Restriction of `\mathcal O`-modules to the localized ringed site over `U`. -/
abbrev localizedRestriction (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :
    RingedSiteModules J 𝒪 ⥤ LocalizedRingedSiteModules J 𝒪 U :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪).over U))

variable [∀ U : C, (localizedRestriction J 𝒪 U).PreservesZeroMorphisms]
variable [∀ U : C, CategoryWithHomology (LocalizedRingedSiteModules J 𝒪 U)]

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod
local notation "SitePerfect" => DerivedCategory.IsPerfect

-- Proof sketch: use Lemma `21.47.4` to rewrite perfectness as pseudo-coherence plus local finite
-- Tor dimension. Pseudo-coherence descends to both summands by Lemma `21.45.6`, and local finite
-- Tor dimension descends coverwise by applying Lemma `21.46.8` on each member of a cover.
/-- Lemma 21.47.8: if a binary biproduct `K ⊞ L` is perfect, then both summands are perfect. -/
theorem isPerfect_summands_of_biprod
    (K L : DMod) (hKL : SitePerfect (K ⊞ L)) :
    SitePerfect K ∧ SitePerfect L := sorry

-- Proof sketch: apply `isPerfect_summands_of_biprod` to the perfectness of `K ⊞ L` and take the
-- left projection of the resulting conjunction.
/-- The left-projection companion to `isPerfect_summands_of_biprod`. -/
theorem isPerfect_left_of_biprod
    (K L : DMod) (hKL : SitePerfect (K ⊞ L)) :
    SitePerfect K := sorry

-- Proof sketch: apply `isPerfect_summands_of_biprod` to the perfectness of `K ⊞ L` and take the
-- right projection of the resulting conjunction.
/-- The right-projection companion to `isPerfect_summands_of_biprod`. -/
theorem isPerfect_right_of_biprod
    (K L : DMod) (hKL : SitePerfect (K ⊞ L)) :
    SitePerfect L := sorry

end

end SheafOfModules.RingedSite
