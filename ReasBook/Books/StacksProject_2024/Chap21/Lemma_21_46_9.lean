import Mathlib
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap21.Definition_21_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => RingedSite.Hom.ModuleCat X
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]
variable [CategoryWithHomology Mod]

local instance instHasDerivedCategoryMod : HasDerivedCategory Mod :=
  HasDerivedCategory.standard Mod

/- Domain-style sampling for Lemma 21.46.9:
- primary domain: bounded-above and tor-amplitude bounds for derived reduction along the quotient
  family `\mathcal O / \mathcal I^n`;
- sampled owner declarations:
  `CategoryTheory.DerivedCategory.IsLE`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the bounded-above owner datum here is the existence of an upper bound `∃ b, IsLE b`, while the
  stronger source-facing conclusion still records a single explicit uniform cohomological bound
  `(quotientBaseChange n).IsLE b`;
  tor-amplitude is already owned by `HasTorAmplitudeIn`;
- primitive data:
  the family `quotientBaseChange`, the bounded-above owner hypothesis on the mod-`I` stage, and
  the interval endpoints `a`, `b`;
- derived API:
  the source-facing propagation statements from the mod-`I` stage to all quotient-power stages.

Source/core/bridge triage:
- `source-facing`: the two propagation theorems matching Lemma 21.46.9;
  - `core/canonical`: `DerivedCategory.IsLE` and `HasTorAmplitudeIn`;
- `bridge/view`: this file, which states the source propagation results directly in terms of those
  owner predicates rather than duplicating their entrywise homology tests.
-/

/- Lemma 21.46.9 (1): let `idealQuotient n` model the ambient `\mathcal O`-module
`\mathcal O / \mathcal I^n` for `n ≥ 1`. If `K \otimes_{\mathcal O}^{\mathbf L}
(\mathcal O / \mathcal I)` is bounded above, then the family
`K \otimes_{\mathcal O}^{\mathbf L} (\mathcal O / \mathcal I^n)` is uniformly bounded above for
all `n ≥ 1`. -/
theorem derivedTensor_idealQuotientPowers_uniformly_boundedAbove
    (quotientBaseChange : ℕ → DMod)
    (h₁ : ∃ b : ℤ, (quotientBaseChange 1).IsLE b) :
    ∃ b : ℤ, ∀ n : ℕ, 1 ≤ n → (quotientBaseChange n).IsLE b
  := by
    sorry

section QuotientPowerTorAmplitude

variable (quotientSheaf : ℕ → Sheaf J CommRingCat.{max u v})

private abbrev quotientRingedSite (n : ℕ) : RingedSite :=
  RingedSite.ofCommRingSheaf J (quotientSheaf n)

private abbrev quotientModuleCat (n : ℕ) :=
  RingedSite.Hom.ModuleCat (quotientRingedSite quotientSheaf n)

private abbrev quotientDerived (n : ℕ) :=
  RingedSite.Hom.ModuleDerived (quotientRingedSite quotientSheaf n)

variable [hAbelianModQ : ∀ n : ℕ, Abelian (quotientModuleCat quotientSheaf n)]
variable [hCategoryWithHomologyModQ : ∀ n : ℕ, CategoryWithHomology (quotientModuleCat quotientSheaf n)]
variable [hMonoidalDModQ : ∀ n : ℕ, MonoidalCategory (quotientDerived quotientSheaf n)]

local instance instAbelianModQ (n : ℕ) :
    Abelian (quotientModuleCat quotientSheaf n) :=
  hAbelianModQ n

local instance instCategoryWithHomologyModQ (n : ℕ) :
    CategoryWithHomology (quotientModuleCat quotientSheaf n) :=
  hCategoryWithHomologyModQ n

local instance instMonoidalDerivedModQ (n : ℕ) :
    MonoidalCategory (quotientDerived quotientSheaf n) :=
  hMonoidalDModQ n

local instance instHasDerivedCategoryModQ (n : ℕ) :
    HasDerivedCategory (quotientModuleCat quotientSheaf n) :=
  HasDerivedCategory.standard (quotientModuleCat quotientSheaf n)

/- Lemma 21.46.9 (2): let `quotientSheaf n` model the quotient ringed site
`\mathcal O / \mathcal I^n` for `n ≥ 1`, and let `quotientBaseChange n` model
`K \otimes_{\mathcal O}^{\mathbf L} (\mathcal O / \mathcal I^n)` as an object of
`D(\mathcal O / \mathcal I^n)`. If the mod-`I` stage has tor-amplitude in `[a, b]`, then every
quotient-power stage has tor-amplitude in `[a, b]`. -/
theorem derivedTensor_idealQuotientPowers_hasTorAmplitudeIn
    (quotientBaseChange :
      ∀ n : ℕ, RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J (quotientSheaf n)))
    (a b : ℤ)
    (h₁ : HasTorAmplitudeIn
      (RingedSite.ofCommRingSheaf J (quotientSheaf 1))
      (quotientBaseChange 1) a b) :
    ∀ n : ℕ, 1 ≤ n →
      HasTorAmplitudeIn (RingedSite.ofCommRingSheaf J (quotientSheaf n))
        (quotientBaseChange n) a b
  := by
    sorry

end QuotientPowerTorAmplitude

end

end SheafOfModules.RingedSite
