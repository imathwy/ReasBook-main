import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Definition_18_40_4
import StacksProject_2024.Chap21.Lemma_21_20_4
import StacksProject_2024.Chap21.Definition_21_47_1
import StacksProject_2024.Chap21.RingedSiteDerivedBasic

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction localizedRestrictionDerived)
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace SheafOfModules.RingedSite

section

open RingedSite.DerivedCategory
open RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "ModX" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "Mod(" 𝒪' ")" => ringedSiteModuleCategory J 𝒪'

/- Domain-style sampling for Lemma 21.49.2:
- primary domain: invertible objects in the monoidal derived category of modules on a ringed
  site, together with Chapter 21 perfectness and the Chapter 18 invertible-module owner;
- sampled owner declarations:
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `RingedSite.DerivedCategory.IsPerfect`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `j[U]⁻¹`,
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.localizedRestriction`;
- best owner abstraction:
  the source-facing statements should reuse the bundled ringed-site owners only where they are
  mathematically primary: invertibility on `ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)`,
  perfectness on the same owner, and localized restriction on the chapter surface `j[U]⁻¹`;
- primitive data:
  an object `M : D(\mathcal O)`, a factor decomposition of `M`, and localized shifted invertible
  modules on members of a cover;
- derived API:
  the three source-facing statements of Lemma `21.49.2`.

Source/core/bridge triage:
- `source-facing`: `LocallyIsomorphicToShiftedInvertibleModule` and the three numbered
  statements;
- `core/canonical`: `Functor.IsEquivalence (tensorRight ℒ)`,
  `RingedSite.DerivedCategory.IsPerfect`, `ModuleCat`, `ModuleDerived`,
  `RingedSite.ofCommRingSheaf J 𝒪`, `localizedRestriction`, and
  `localizedRestrictionDerived` with notation `j[U]⁻¹`;
- `bridge/view`: localized restriction of factor sheaves `factorSheaf n ↦ (factorSheaf n).over U`
  and the exact derived restriction functor `j[U]⁻¹`; there is no second owner alias for
  `LocallyIsomorphicToShiftedInvertibleModule`, since the source-facing predicate already lives on
  the canonical `ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)` owner. -/

variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalCategory (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]
variable [HasCountableCoproducts (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]
variable [instMonoidalModuleCat :
  ∀ 𝒪' : Sheaf J CommRingCat.{max u v},
    MonoidalCategory (ringedSiteModuleCategory J 𝒪')]

local instance :
    Abelian (ModuleCat X) :=
  SheafOfModules.instAbelian
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local notation "single0" =>
  DerivedCategory.singleFunctor ModX (0 : ℤ)

/-- The factor support is locally finite when only finitely many restricted factor sheaves remain
nonzero on each member of a covering. -/
def HasLocallyFiniteFactorSupport
    (factorSheaf : ℤ → Sheaf J CommRingCat.{max u v}) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    Set.Finite
      {n : ℤ |
        ¬ IsZero ((factorSheaf n).over I.Y)}

/-- The canonical derived object attached to factor sheaves, a product decomposition of the
structure sheaf, and their shifted module summands. -/
noncomputable def factorDecompositionObject
    (factorSheaf : ℤ → Sheaf J CommRingCat.{max u v})
    (productIso : 𝒪 ≅ ∏ᶜ factorSheaf)
    (factorModule : (n : ℤ) → Mod(factorSheaf n)) :
    DMod :=
  ∐ fun n : ℤ ↦
    ((single0).obj
      ((restrictionAlong (productIso.hom ≫ Pi.π factorSheaf n)).obj
        (factorModule n)))⟦-n⟧

/-- All factor modules in a decomposition are invertible on their respective factor sheaves. -/
def HasInvertibleFactorModules
    (factorSheaf : ℤ → Sheaf J CommRingCat.{max u v})
    (factorModule : (n : ℤ) → Mod(factorSheaf n)) : Prop :=
  ∀ n : ℤ,
    let _ : MonoidalCategory (ringedSiteModuleCategory J (factorSheaf n)) :=
      instMonoidalModuleCat (factorSheaf n)
    Functor.IsEquivalence (tensorRight (factorModule n))

/-- A derived `𝒪`-module admits an invertible factor decomposition if the structure sheaf
splits as a product of factor sheaves carrying invertible modules whose shifted direct sum is
isomorphic to the given object, with locally finite support on every cover member. -/
def HasInvertibleFactorDecomposition
    (M : DMod) : Prop :=
  ∃ factorSheaf : ℤ → Sheaf J CommRingCat.{max u v},
    ∃ productIso : 𝒪 ≅ ∏ᶜ factorSheaf,
      ∃ factorModule : (n : ℤ) → Mod(factorSheaf n),
        HasInvertibleFactorModules factorSheaf factorModule ∧
          IsIsomorphic M (factorDecompositionObject factorSheaf productIso factorModule) ∧
          HasLocallyFiniteFactorSupport factorSheaf

namespace HasInvertibleFactorDecomposition

omit [CategoryWithHomology (ModuleCat X)] [MonoidalCategory DMod] in
/-- Unpack a chosen invertible factor decomposition into its source-facing data. -/
theorem exists_data
    {M : DMod}
    (hM : HasInvertibleFactorDecomposition M) :
    ∃ factorSheaf : ℤ → Sheaf J CommRingCat.{max u v},
      ∃ productIso : 𝒪 ≅ ∏ᶜ factorSheaf,
        ∃ factorModule : (n : ℤ) → Mod(factorSheaf n),
          HasInvertibleFactorModules factorSheaf factorModule ∧
            IsIsomorphic M (factorDecompositionObject factorSheaf productIso factorModule) ∧
            HasLocallyFiniteFactorSupport factorSheaf :=
  hM

end HasInvertibleFactorDecomposition

/- Lemma 21.49.2 (1): invertibility in the derived category is equivalent to the existence of an
invertible derived factor decomposition. -/
@[stacks 0FPY]
theorem isInvertible_iff_exists_factorDecomposition
    (M : DMod) :
    Functor.IsEquivalence (tensorRight M) ↔
      HasInvertibleFactorDecomposition M := by
  constructor
  · intro hM
    refine ⟨?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
  · intro hM
    sorry

end

section

open RingedSite.DerivedCategory
open RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C,
  CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
variable [MonoidalCategory (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]
variable [∀ U : C,
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]

local notation "DMod" => ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)

/-- Lemma 21.49.2 (2): an invertible object of the derived category is perfect. -/
@[stacks 0FPY]
theorem isPerfect_of_isInvertible
    {M : DMod}
    (hM : Functor.IsEquivalence (tensorRight M)) :
    M.IsPerfect := by
  sorry

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]
variable [∀ U : C,
  MonoidalCategory (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]

local notation "DMod" => ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)
local notation "ModLoc" U =>
  ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U)
local notation "single0[" U "]" =>
  DerivedCategory.singleFunctor (ModLoc U) (0 : ℤ)
local notation "j[" U "]⁻¹" =>
  localizedRestrictionDerived (RingedSite.ofCommRingSheaf J 𝒪) U

local instance (U : C) :
    MonoidalCategory (ModLoc U) :=
  inferInstance

local instance :
    Abelian (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪)) :=
  SheafOfModules.instAbelian
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local instance (U : C) :
    Abelian (ModLoc U) :=
  SheafOfModules.instAbelian
    ((RingedSite.ofCommRingSheaf J 𝒪).localization U).structureSheaf

/-- A derived `𝒪`-module is locally a shifted invertible module if every object of the
site admits a covering on whose members the restricted object is isomorphic to an invertible local
module placed in a single degree. -/
def LocallyIsomorphicToShiftedInvertibleModule
    (M : DMod) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ n : ℤ,
      ∃ ℒ : ModLoc I.Y,
      Functor.IsEquivalence (tensorRight ℒ) ∧
        IsIsomorphic
          ((j[I.Y]⁻¹).obj M)
          (((single0[I.Y]).obj ℒ)⟦-n⟧)

namespace LocallyIsomorphicToShiftedInvertibleModule

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] [MonoidalCategory DMod]
  [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive] in
/-- On each `U`, local shifted-invertibility yields a cover and local shifted invertible models. -/
theorem exists_cover_data
    {M : DMod}
    (hM : LocallyIsomorphicToShiftedInvertibleModule M)
    (U : C) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ n : ℤ,
        ∃ ℒ : ModLoc I.Y,
          Functor.IsEquivalence (tensorRight ℒ) ∧
            IsIsomorphic
              ((j[I.Y]⁻¹).obj M)
              (((single0[I.Y]).obj ℒ)⟦-n⟧) :=
  hM U

end LocallyIsomorphicToShiftedInvertibleModule

/-- Lemma 21.49.2 (3): on a locally ringed site, invertibility is equivalent to being locally a
shifted invertible module. -/
@[stacks 0FPY]
theorem isInvertible_iff_locallyIsomorphicToShiftedInvertibleModule_of_isLocallyRingedSite
    [IsLocallyRingedSite 𝒪]
    (M : DMod) :
    Functor.IsEquivalence (tensorRight M) ↔
      LocallyIsomorphicToShiftedInvertibleModule M := by
  sorry

end

end SheafOfModules.RingedSite
