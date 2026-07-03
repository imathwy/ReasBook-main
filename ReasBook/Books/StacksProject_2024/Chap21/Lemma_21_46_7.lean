import Mathlib
import StacksProject_2024.Chap21.Definition_21_17_13
import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Definition_21_46_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.7:
- primary domain: tor-amplitude in `D(\mathcal O)` under the derived tensor product on a ringed
  site;
- sampled owner declarations:
  `RingedSiteModules`,
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_derivedTensorProduct`;
- best owner abstraction: the ambient owner is `RingedSiteModules J 𝒪`, the source-facing
  predicate is `HasTorAmplitudeIn` on `DerivedCategory (RingedSiteModules J 𝒪)`, and the tensor
  owner is the canonical derived tensor product notation `K ⊗^L L`;
- primitive data: the objects `K`, `L` of `D(\mathcal O)` and their tor-amplitude bounds;
- derived API: the induced tor-amplitude bound for `K ⊗^L L`.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude bound for the tensor product on the ringed site;
- `core/canonical`: `HasTorAmplitudeIn` together with `derivedTensorProduct`;
- `bridge/view`: this theorem, which records closure of the source-facing predicate under the
  canonical tensor owner.

The previous file restated the definition of tor-amplitude inline. This refinement removes that
duplicate wheel and states the lemma directly with the chapter owner abstractions.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [hAbelian : Abelian (RingedSiteModules J 𝒪)]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules J 𝒪))]
variable [HasCountableCoproducts (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules J 𝒪)]
variable [HasColimits (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ M : RingedSiteModules J 𝒪, ((curriedTensor (RingedSiteModules J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules J 𝒪))]

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

local instance instPreadditiveMod : Preadditive Mod :=
  hAbelian.toPreadditive

variable {a b c d : ℤ}

-- Proof sketch: test the tor-amplitude conditions for `K` and `L` against an arbitrary
-- degree-zero module, reassociate the iterated derived tensor product, and combine the intervals
-- `[a, b]` and `[c, d]` via the Tor spectral sequence.
/-- Lemma 21.46.7: if `K` has tor-amplitude in `[a, b]` and `L` has tor-amplitude in `[c, d]`,
then `K \otimes_{\mathcal O}^{\mathbf L} L` has tor-amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_tensor
    (K L : DMod)
    (hK : HasTorAmplitudeIn K a b)
    (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := sorry

end

end SheafOfModules.RingedSite
