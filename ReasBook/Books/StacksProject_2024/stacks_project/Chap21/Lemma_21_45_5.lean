import StacksProject_2024.Chap21.Definition_21_17_13_Core
import StacksProject_2024.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)
open scoped RingedSiteDerivedTensor
noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom
namespace ModuleDerived

section

/- Domain-style sampling for Lemma 21.45.5:
- primary domain: pseudo-coherence for derived `𝒪_X`-modules on a commutative ringed
  site and its stability under the canonical derived tensor product;
- sampled owner declarations:
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent`,
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent`,
  `ModuleDerived`,
  `DerivedCategory.IsLE`,
  `RingedSiteDerivedTensor`;
- best owner abstraction:
  `source-facing`: the tensor-closure statements for `K.IsMPseudoCoherent n` and
    `K.IsPseudoCoherent` on the derived tensor product `K ⊗^L L` in `ModuleDerived X`;
  `core/canonical`: the owner predicates `IsMPseudoCoherent`, `IsPseudoCoherent`, the bundled
    owner `ModuleDerived X`, the derived tensor owner `derivedTensorProduct`, and the
    bounded-above owner `K.IsLE a`;
  `bridge/view`: the textbook notation `K ⊗^L L`, provided by `RingedSiteDerivedTensor`; the
    later comparison with the ambient monoidal tensor belongs to the separate bridge file
    `Lemma_21_48_5`, not to this source-facing tensor-closure theorem;
- primitive vs. derived:
  primitive data are the bundled ringed site `X`, the derived objects `K`, `L`, the integers
  `n`, `m`, `a`, `b`, the pseudo-coherence hypotheses, the bounded-above hypotheses, and the
  derived tensor object;
  derived API is the pair of tensor-closure conclusions on the same owners.

Source/core/bridge triage:
- `source-facing`: Lemma 21.45.5 itself;
- `core/canonical`: `ModuleDerived X`,
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent`,
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent`, `DerivedCategory.IsLE`, and
  `SheafOfModules.RingedSite.derivedTensorProduct`;
- `bridge/view`: the source-facing notation `K ⊗^L L`, together with the later comparison
  isomorphism to the localized monoidal tensor from `Lemma_21_48_5`, and the ringed-space
  specialization in Chapter 20.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [HasBinaryProducts C]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [CategoryWithHomology (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L
    (curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪))]
variable [∀ U : C,
  CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪
local notation "DMod" => ModuleDerived X

local instance :
    Abelian Mod :=
  SheafOfModules.instAbelian (RingedSite.ofCommRingSheaf J 𝒪).structureSheaf

variable {K L : DMod} {n m a b : ℤ}

 /- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent and belongs to `D^{≤ a}`, and `L` is
`m`-pseudo-coherent and belongs to `D^{≤ b}`, then `K ⊗^L L` is
`max (m + a) (n + b)`-pseudo-coherent. The bounded-above hypotheses are expressed by the owner
predicates `K.IsLE a` and `L.IsLE b`. -/
@[stacks 09J3]
theorem IsMPseudoCoherent.tensor
    (hK : K.IsMPseudoCoherent n)
    (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m)
    (hLLE : L.IsLE b) :
    ((K ⊗^L L : DMod)).IsMPseudoCoherent (max (m + a) (n + b)) := by
  sorry

/- Lemma 21.45.5 (2): if `K` and `L` are pseudo-coherent, then `K ⊗^L L` is pseudo-coherent. -/
@[stacks 09J3]
theorem IsPseudoCoherent.tensor
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    ((K ⊗^L L : DMod)).IsPseudoCoherent := by
  sorry

end

end ModuleDerived
end RingedSite.Hom
