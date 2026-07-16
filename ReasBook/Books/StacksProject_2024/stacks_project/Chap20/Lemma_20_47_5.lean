import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1
import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14_Core
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Lemma 20.47.5:
- primary domain: pseudo-coherence for derived `𝒪_X`-modules on a ringed space and its
  stability under the canonical derived tensor product;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent`,
  `AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.tensor`,
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent.tensor`;
- best owner abstraction:
  `source-facing`: the Chapter 20 tensor-closure statements for the ringed-space predicates
    `K.IsMPseudoCoherent n` and `K.IsPseudoCoherent`;
  `core/canonical`: the existing Chapter 20 owners `IsMPseudoCoherent`, `IsPseudoCoherent`, and
    the canonical derived tensor object `K ⊗^L L`;
  `bridge/view`: the opens-site specialization of the ringed-site tensor-closure theorems from
    Chapter 21, which guides proofs but should not introduce a second public wrapper layer.
- primitive vs. derived:
  primitive data are the derived objects `K`, `L`, the bounds `n`, `m`, `a`, `b`, the
  pseudo-coherence hypotheses, the bounded-above hypotheses, and the canonical derived tensor
  product; the tensor-closure conclusions are derived API on the existing owners.

Source/core/bridge triage:
- `source-facing`: Lemma 20.47.5 for derived `𝒪_X`-modules on a ringed space;
- `core/canonical`: `ModuleDerived.IsMPseudoCoherent`, `ModuleDerived.IsPseudoCoherent`, and
  `derivedTensorProduct`;
- `bridge/view`: the later proof route through the ringed-site specialization.
-/

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "DModX" => ModuleDerived X

variable {K L : DModX} {n m a b : ℤ}

namespace ModuleDerived

/-- Lemma 20.47.5 (1): if `K` is `n`-pseudo-coherent and belongs to `D^{≤ a}`, and `L` is
`m`-pseudo-coherent and belongs to `D^{≤ b}`, then `K ⊗^L L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 09J3]
theorem IsMPseudoCoherent.tensor
    (hK : ModuleDerived.IsMPseudoCoherent K n)
    (hKLE : K.IsLE a)
    (hL : ModuleDerived.IsMPseudoCoherent L m)
    (hLLE : L.IsLE b) :
    ModuleDerived.IsMPseudoCoherent (K ⊗^L L) (max (m + a) (n + b)) := by
  sorry

/-- Lemma 20.47.5 (2): the derived tensor product of two pseudo-coherent objects of `D(𝒪_X)` is
pseudo-coherent. -/
@[stacks 09J3]
theorem IsPseudoCoherent.tensor
    (hK : ModuleDerived.IsPseudoCoherent K)
    (hL : ModuleDerived.IsPseudoCoherent L) :
    ModuleDerived.IsPseudoCoherent (K ⊗^L L) := by
  sorry

end ModuleDerived

end

end AlgebraicGeometry.RingedSpace
