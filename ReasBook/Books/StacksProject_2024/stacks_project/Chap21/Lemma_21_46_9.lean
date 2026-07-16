import StacksProject_2024.stacks_project.Chap18.IdealQuotientSheaf
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSite.Hom
open scoped RingedSiteDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

open RingedSite.Hom

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "DMod" => ModuleDerived X

variable (I : Subobject (unitModule J 𝒪))

local notation "X⟮" n "⟯" =>
  RingedSite.ofCommRingSheaf J (idealPowerQuotientCommRingSheaf I (n : ℕ))
local notation "DMod⟮" n "⟯" => ModuleDerived (X⟮n⟯)

/-- The canonical same-site morphism `X⟮n⟯ ⟶ X` induced by
`𝒪 ⟶ 𝒪 / I^n`. -/
noncomputable abbrev idealPowerQuotientProjection (n : ℕ+) :
    X⟮n⟯ ⟶ X :=
  sameSiteHom (idealPowerQuotientCommRingSheafProjection I (n : ℕ))

/- Domain-style sampling for Lemma 21.46.9:
- primary domain: tor-amplitude and bounded-above behavior under same-site derived base change
  from `𝒪` to the quotient-power sheaves `𝒪 / I^n`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.idealPowerQuotientCommRingSheaf`,
  `SheafOfModules.RingedSite.idealPowerQuotientCommRingSheafProjection`,
  `RingedSite.Hom.modulePullbackDerived`,
  `CategoryTheory.DerivedCategory.IsLE`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`;
- best owner abstraction:
  the source-facing quotient-power tower should be expressed by the actual quotient sheaves
  `idealPowerQuotientCommRingSheaf I n` and their canonical projections
  `idealPowerQuotientCommRingSheafProjection I n : 𝒪 ⟶ 𝒪 / I^n`,
  with the derived base-change object owned canonically by the same-site ringed-site pullback
  `modulePullbackDerived (sameSiteHom (idealPowerQuotientCommRingSheafProjection I n))`;
- primitive data:
  the ambient commutative ring sheaf `𝒪`, an ideal sheaf `I`, and a derived object `K`;
- derived API:
  the bounded-above and tor-amplitude propagation statements for the canonical quotient-power
  derived pullbacks.

Source/core/bridge triage:
- `source-facing`: Lemma 21.46.9 itself, about the quotient-power family
  `K ⊗^L_𝒪 (𝒪 / I^n)`;
- `core/canonical`: the quotient-power sheaf owner `idealPowerQuotientCommRingSheaf`, its
  projection `idealPowerQuotientCommRingSheafProjection`, and the site-presented derived pullback
  owner `modulePullbackDerived (sameSiteHom (idealPowerQuotientCommRingSheafProjection I n))`,
  and the boundedness/tor-amplitude owners `IsLE` and `HasTorAmplitudeIn`;
- `bridge/view`: the file-local same-site quotient-power morphisms
  `idealPowerQuotientProjection I n` and their derived pullbacks
  `idealPowerQuotientPullbackDerived I n`.
-/

variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalCategoryStruct
  (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]
variable [((𝟭 C).sheafPushforwardContinuous CommRingCat.{u} J J).IsRightAdjoint]

/-- The derived pullback functor along `idealPowerQuotientProjection I n`,
modeling base change from `𝒪` to `𝒪 / I^n`. -/
noncomputable abbrev idealPowerQuotientPullbackDerived (n : ℕ+) :
    DMod ⥤ DMod⟮n⟯ :=
  modulePullbackDerived (idealPowerQuotientProjection I n)

variable [hCategoryWithHomology : ∀ n : ℕ+,
  CategoryWithHomology (ModuleCat (X⟮n⟯))]

/-- Lemma 21.46.9 (1): the displayed stagewise derived pullback is the canonical
base change of `K` to `𝒪 / I^n`, i.e. the derived tensor product of `K` with
`𝒪 / I^n` over `𝒪`. Any explicit upper bound for the mod-`I` stage works uniformly for every
quotient-power stage. -/
@[stacks 0942]
theorem derivedTensor_idealQuotientPowers_isLE
    (K : DMod) {b : ℤ}
    (hModI : ((idealPowerQuotientPullbackDerived I (1 : ℕ+)).obj K).IsLE b)
    (n : ℕ+) :
    ((idealPowerQuotientPullbackDerived I n).obj K).IsLE b := by
  sorry

/-- Lemma 21.46.9 (1): if the mod-`I` stage
`K ⊗^L_𝒪 (𝒪 / I)` is bounded above, then the same is true uniformly for all quotient-power stages
`K ⊗^L_𝒪 (𝒪 / I^n)`. -/
@[stacks 0942]
theorem derivedTensor_idealQuotientPowers_uniformly_boundedAbove
    (K : DMod)
    (hModI : ∃ b : ℤ, ((idealPowerQuotientPullbackDerived I (1 : ℕ+)).obj K).IsLE b) :
    ∃ b : ℤ, ∀ n : ℕ+, ((idealPowerQuotientPullbackDerived I n).obj K).IsLE b := by
  rcases hModI with ⟨b, hb⟩
  exact ⟨b, fun n ↦ derivedTensor_idealQuotientPowers_isLE I K hb n⟩

/-- Lemma 21.46.9 (2): if the mod-`I` stage `K ⊗^L_𝒪 (𝒪 / I)` has tor-amplitude in `[a, b]`,
then every quotient-power stage `K ⊗^L_𝒪 (𝒪 / I^n)` has tor-amplitude in `[a, b]`. -/
@[stacks 0942]
theorem derivedTensor_idealQuotientPowers_hasTorAmplitudeIn
    (K : DMod)
    (a b : ℤ)
    [MonoidalCategory (DMod⟮(1 : ℕ+)⟯)]
    (hModI : HasTorAmplitudeIn ((idealPowerQuotientPullbackDerived I (1 : ℕ+)).obj K) a b)
    (n : ℕ+)
    [MonoidalCategory (DMod⟮n⟯)] :
    HasTorAmplitudeIn ((idealPowerQuotientPullbackDerived I n).obj K) a b := by
  sorry

end

end SheafOfModules.RingedSite
