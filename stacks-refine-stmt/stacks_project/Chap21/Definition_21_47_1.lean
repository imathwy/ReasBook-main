import Mathlib
import stacks_project.Chap21.Definition_21_44_1

open CategoryTheory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

/-- Restriction of `\mathcal O`-modules from `(\mathcal C, \mathcal O)` to the localized ringed
site `(\mathcal C/U, J.over U, \mathcal O_U)`. -/
private abbrev localizedRestriction (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :
    RingedSiteModules J 𝒪 ⥤ LocalizedRingedSiteModules J 𝒪 U :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

variable [∀ U : C, (localizedRestriction J 𝒪 U).PreservesZeroMorphisms]

/-- Restriction of complexes of `\mathcal O`-modules to the localized ringed site over `U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (ModLoc U) ℤ :=
  (localizedRestriction J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)

namespace CochainComplex

/-- Definition 21.47.1: a complex of `\mathcal O`-modules on a ringed site is perfect if every
object of the site admits a covering on whose members the restricted complex is quasi-isomorphic
to a strictly perfect complex. -/
def IsPerfect (E : Cpx) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
        IsStrictlyPerfect E' ∧ QuasiIso α

end CochainComplex

variable [J.WEqualsLocallyBijective AddCommGrpCat]

namespace DerivedCategory

local notation "DMod" => DerivedCategory Mod

/-- The derived-category notion of perfection is the existence of a perfect representative
complex. -/
def IsPerfect (E : DMod) : Prop :=
  ∃ K : Cpx,
    ∃ _ : E ≅
        ((DerivedCategory.Q : Cpx ⥤ DMod).obj K),
      CochainComplex.IsPerfect K

end DerivedCategory

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, (localizedRestriction J 𝒪 U).PreservesZeroMorphisms]

-- Proof sketch: `CochainComplex.IsPerfect` is defined by the local existence, on a cover of each
-- object, of a quasi-isomorphism from a strictly perfect complex after passing to the localized
-- ringed sites.
/-- Unfolding `CochainComplex.IsPerfect` gives the local strictly-perfect approximation criterion
on coverings of the ringed site. -/
theorem cochainComplex_isPerfect_iff
    (E : CochainComplex (RingedSiteModules J 𝒪) ℤ) :
    CochainComplex.IsPerfect E ↔
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        ∃ E' : CochainComplex (LocalizedRingedSiteModules J 𝒪 I.Y) ℤ,
          ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
            CochainComplex.IsStrictlyPerfect E' ∧ QuasiIso α := Iff.rfl

end

end SheafOfModules.RingedSite
