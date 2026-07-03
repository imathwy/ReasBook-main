import Mathlib
import stacks_project.Chap20.Definition_20_26_14
import stacks_project.Chap20.Definition_20_47_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped RingedSpaceDerivedTensor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- The derived tensor product on `D(\mathcal O_X)` with ambient ringed space fixed by the local
context. -/
private abbrev derivedTensorObj (K L : DModX) : DModX :=
  (derivedTensorProduct L).obj K

local notation:70 K:70 " ⊗^L " L:71 => derivedTensorObj K L

-- Proof sketch: work locally on an open neighborhood where `K` and `L` admit strictly perfect
-- approximations in degrees `n` and `m`. Tensor those representatives termwise, use the local
-- vanishing hypotheses to control the Tor spectral sequence, and conclude that the induced map to
-- the restricted derived tensor product is an isomorphism above
-- `max (m + a, n + b)` and an epimorphism in degree `max (m + a, n + b)`.
/-- Lemma 20.47.5 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology sheaves above `a`
and `L` is `m`-pseudo-coherent with vanishing cohomology sheaves above `b`, then the derived
tensor product `K \otimes_{\mathcal O_X}^{\mathbf L} L` is
`max (m + a, n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DModX) (n m a b : ℤ)
    (hK : IsMPseudoCoherent K n)
    (hKvanish : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) i).obj K))
    (hL : IsMPseudoCoherent L m)
    (hLvanish : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) j).obj L)) :
    IsMPseudoCoherent (K ⊗^L L) (max (m + a) (n + b)) := sorry

-- Proof sketch: pseudo-coherence gives local `m`-pseudo-coherence for every `m`, and locally one
-- first replaces `K` and `L` by bounded-above strictly perfect complexes. Applying part `(1)` to
-- those local bounded-above presentations yields local `m`-pseudo-coherence for every `m` of the
-- derived tensor product, hence pseudo-coherence.
/-- Lemma 20.47.5 (2): the derived tensor product of two pseudo-coherent objects of
`D(\mathcal O_X)` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DModX)
    (hK : IsPseudoCoherent K)
    (hL : IsPseudoCoherent L) :
    IsPseudoCoherent (K ⊗^L L) := sorry

end

end AlgebraicGeometry.RingedSpace
