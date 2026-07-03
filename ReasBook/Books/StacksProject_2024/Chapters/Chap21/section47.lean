import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_47_1 (from Chap21) -/
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

/-! ### Lemma_21_47_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (Mod : Type w) [Category.{v} Mod] [Abelian Mod]
variable (ModLoc : C → Type w)
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]

/- The parameter `strictlyPerfect U` stands for the strict-perfectness predicate on complexes of
`\mathcal O_U`-modules. -/
variable (strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop)

/- The parameter `localizedRestrictionDerived U` stands for the derived restriction functor
`D(\mathcal O) → D(\mathcal O_U)`. -/
variable (localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U))

/- The parameter `complexIsPerfect` stands for perfectness on complexes of `\mathcal O`-modules. -/
variable (complexIsPerfect : CochainComplex Mod ℤ → Prop)

/- The parameter `derivedIsPerfect` stands for perfectness on `D(\mathcal O)`. -/
variable (derivedIsPerfect : DerivedCategory Mod → Prop)

section

variable {J : GrothendieckTopology C}
variable {Mod : Type w} [Category.{v} Mod] [Abelian Mod]
variable {ModLoc : C → Type w}
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]
variable {strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop}
variable {localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U)}
variable {complexIsPerfect : CochainComplex Mod ℤ → Prop}
variable {derivedIsPerfect : DerivedCategory Mod → Prop}

-- Proof sketch: because `X` is final, any object of the site admits a cover obtained by pulling
-- back the chosen cover of `X`. The given strictly perfect local models on that cover then yield
-- the local strictly perfect representatives required by the definition of perfectness.
/-- Lemma 21.47.2 (1): if a derived `\mathcal O`-module becomes on a covering of a final object
isomorphic in the localized derived categories to strictly perfect complexes, then it is perfect.
-/
theorem isPerfect_of_exists_cover_on_finalObject
    (E : DerivedCategory Mod) (X : C) (_hX : IsTerminal X)
    (hcover :
      ∃ T : J.Cover X, ∀ I : T.Arrow,
        ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
          strictlyPerfect I.Y E' ∧
            ∃ α :
              ((DerivedCategory.Q :
                  CochainComplex (ModLoc I.Y) ℤ ⥤
                    DerivedCategory (ModLoc I.Y)).obj E') ⟶
                (localizedRestrictionDerived I.Y).obj E,
              IsIso α) :
    derivedIsPerfect E := sorry

-- Proof sketch: unfold the definition of derived perfectness to choose one perfect representative
-- of `E`. Any other complex representing `E` is isomorphic to that representative in the derived
-- category, so the local strictly perfect models transport across the representing isomorphism.
/-- Lemma 21.47.2 (2): if `E` is perfect, then every complex representing `E` is perfect. -/
theorem cochainComplex_isPerfect_of_represents_isPerfect
    (E : DerivedCategory Mod) (K : CochainComplex Mod ℤ)
    (e : ((DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DerivedCategory Mod).obj K) ≅ E)
    (hE : derivedIsPerfect E) :
    complexIsPerfect K := sorry

end

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_47_3 (from Chap21) -/
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

/-! ### Lemma_21_47_4 (from Chap21) -/
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

/-! ### Lemma_21_47_5 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section PerfectObjects

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, ((J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- Restriction of modules to the localized ringed site over `U`. -/
private abbrev localizedPerfectRestriction (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    RingedSiteModules J 𝒪 ⥤ RingedSiteModules (J.over U) (𝒪.over U) :=
  SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝒪).over U))

end PerfectObjects

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [∀ U : C, ((JC.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : D, ((JD.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))]
variable [∀ U : C, HasWeakSheafify (JC.over U) AddCommGrpCat.{u}]
variable [∀ U : D, HasWeakSheafify (JD.over U) AddCommGrpCat.{u}]
variable [∀ U : C, ((JC.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]
variable [∀ U : D, ((JD.over U).WEqualsLocallyBijective AddCommGrpCat.{u})]

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [∀ U : C, (localizedPerfectRestriction JC 𝒪' U).PreservesZeroMorphisms]
variable [∀ U : D, (localizedPerfectRestriction JD 𝒪 U).PreservesZeroMorphisms]

variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]
variable [(pullbackFunctor F φ).Additive]

local notation "DModC" => DerivedCategory (RingedSiteModules JC 𝒪')

-- Proof sketch: choose a perfect representative complex for `E`. Pull that representative back
-- termwise along the morphism of ringed sites; strict perfectness is preserved under pullback, and
-- the induced morphism remains a quasi-isomorphism. The pulled-back representative therefore shows
-- that `Lf^* E` is perfect.
/-- Lemma 21.47.5: for the site-presented morphism of ringed sites determined by `F` and `φ`,
the derived pullback of a perfect object is again perfect. -/
theorem leftDerivedPullback_isPerfect
    (E : DModC) (hE : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((leftDerivedPullback F φ).obj E) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_47_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]

/- The parameter `IsPerfect` stands for perfectness on `D(\mathcal O)` from the preceding
development of perfect complexes on ringed sites. -/
variable (IsPerfect : DMod → Prop)

-- Proof sketch: combine Lemma `21.47.4`, which characterizes perfect objects by pseudo-coherence
-- and local finite Tor dimension, with Lemma `21.45.4 (1)` for pseudo-coherence and Lemma
-- `21.46.6 (1)` for Tor-amplitude in a distinguished triangle.
/-- Lemma 21.47.6 (1): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `K` and `L` are
perfect, then `M` is perfect. -/
theorem isPerfect_obj₃_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := sorry

-- Proof sketch: reduce perfectness using Lemma `21.47.4`, then apply Lemma `21.45.4 (2)` to the
-- pseudo-coherent part and Lemma `21.46.6 (2)` to the local finite Tor-dimension part.
/-- Lemma 21.47.6 (2): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `K` and `M` are
perfect, then `L` is perfect. -/
theorem isPerfect_obj₂_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsPerfect T.obj₁) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₂ := sorry

-- Proof sketch: once more use Lemma `21.47.4` to express perfectness as pseudo-coherence plus
-- local finite Tor dimension, then apply Lemma `21.45.4 (3)` and Lemma `21.46.6 (3)` to the
-- distinguished triangle.
/-- Lemma 21.47.6 (3): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `L` and `M` are
perfect, then `K` is perfect. -/
theorem isPerfect_obj₁_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₁ := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_47_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules :=
  SheafOfModules
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [MonoidalCategory DMod]

/- The parameter `IsPerfectObject` stands for the perfect-object predicate on `D(\mathcal O)` from
the surrounding perfect-complex formalization. -/
variable (IsPerfectObject : DMod → Prop)

-- Proof sketch: this is the closure statement for the perfect-object predicate under the derived
-- tensor product; in the textbook it is obtained from the pseudo-coherence and Tor-amplitude
-- criteria of Lemmas `21.47.4`, `21.45.5`, and `21.46.7`.
/-- Lemma 21.47.7: if `K` and `L` are perfect objects of `D(\mathcal O)`, then their derived
tensor product `K \otimes_{\mathcal O}^{\mathbf L} L` is again perfect. In this item file, the
perfectness predicate is abstracted as `IsPerfectObject`. -/
theorem tensor_isPerfect_of_isPerfect
    (hTensor :
      ∀ K L : DMod,
        IsPerfectObject K → IsPerfectObject L → IsPerfectObject (K ⊗ L))
    (K L : DMod)
    (hK : IsPerfectObject K)
    (hL : IsPerfectObject L) :
    IsPerfectObject (K ⊗ L) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_47_8 (from Chap21) -/
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
