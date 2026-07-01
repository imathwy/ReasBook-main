import Mathlib
import stacks_project.Chap21.Definition_21_17_13
import stacks_project.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod

/- Domain-style sampling for Lemma 21.45.5:
- primary domain: pseudo-coherence for derived `\mathcal O`-modules on a ringed site and its
  behavior under derived tensor product;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `SheafOfModules.RingedSite.DerivedCategory.IsMPseudoCoherent`,
  `SheafOfModules.RingedSite.DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the source-facing theorem should use the ambient module-category owner
  `ringedSiteModuleCategory J 𝒪` and its derived category `DerivedCategory Mod`, together with the
  intrinsic predicates `K.IsMPseudoCoherent m` and `K.IsPseudoCoherent` and the canonical Chapter
  21 derived tensor object `K ⊗^L L`;
- primitive data: the ringed site, the derived objects `K` and `L`, the integer bounds
  `n m a b`, and the homology-vanishing hypotheses;
- derived API: tensor-product closure theorems for `m`-pseudo-coherence and pseudo-coherence.

Source/core/bridge triage:
- `source-facing`: Lemma 21.45.5 itself, asserting pseudo-coherence for a derived tensor product;
- `core/canonical`: the owner predicates `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`, the owner `derivedTensorProduct` with notation `K ⊗^L L`,
  and the chapter owner `ringedSiteModuleCategory J 𝒪` with its derived category
  `DerivedCategory Mod`;
- `bridge/view`: the bounded-above representative and local strictly perfect model arguments used
  in proofs, which should not be promoted to a second public owner layer.
-/

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [HasCountableCoproducts Mod]
variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [HasColimits Mod]
variable [(curriedTensor Mod).Additive]
variable [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
variable [∀ (K L : CochainComplex Mod ℤ), CochainComplex.HasMapBifunctor K L (curriedTensor Mod)]

-- Proof sketch: apply the local strictly perfect approximation criterion from Definition
-- `21.45.1` to `K` and `L` on a common covering, tensor the local models, and use the Tor spectral
-- sequence together with the vanishing hypotheses to obtain the bound `max (m + a, n + b)`.
/-- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology above `a` and `L`
is `m`-pseudo-coherent with vanishing cohomology above `b`, then
`K \otimes_{\mathcal O}^{\mathbf L} L` is `max (m + a, n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DMod) (n m a b : ℤ)
    (hK : K.IsMPseudoCoherent n)
    (hKvanish : ∀ i : ℤ, a < i → IsZero ((H i).obj K))
    (hL : L.IsMPseudoCoherent m)
    (hLvanish : ∀ j : ℤ, b < j → IsZero ((H j).obj L)) :
    (K ⊗^L L).IsMPseudoCoherent (max (m + a) (n + b)) :=
  sorry

-- Proof sketch: choose pseudo-coherent representatives for `K` and `L`, replace them locally by
-- bounded-above strictly perfect models as in the textbook proof, and apply part `(1)` degreewise
-- to conclude that the canonical derived tensor object is pseudo-coherent.
/-- Lemma 21.45.5 (2): if `K` and `L` are pseudo-coherent, then
`K \otimes_{\mathcal O}^{\mathbf L} L` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    (K ⊗^L L).IsPseudoCoherent :=
  sorry

end

end SheafOfModules.RingedSite
