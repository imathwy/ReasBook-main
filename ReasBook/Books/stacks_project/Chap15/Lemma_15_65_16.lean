import Mathlib
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.16:
- primary domain: pseudo-coherence in `D(R)` and its behavior under the Chapter 15 derived tensor
  product owner;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: this file is `source-facing`, but its statements should stay directly on
  the canonical owners `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, the tensor notation
  `K ⊗[R]^L L`, and the homology functor owner `H`;
- primitive vs. derived:
  primitive data are the objects `K`, `L`, the bounds `n m a b`, and the homology-vanishing
  assumptions;
  derived API is the preservation of `m`-pseudo-coherence and pseudo-coherence under the canonical
  tensor owner.
-/

-- Proof sketch: choose bounded-above finite-projective models for `K` and `L` with the stated
-- cohomological control, compute the derived tensor product by the total tensor complex of these
-- models, and use the Tor spectral sequence to obtain isomorphisms above
-- `max (m + a) (n + b)` together with surjectivity in that degree.
/-- Lemma 15.65.16 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology in degrees
strictly above `a`, and `L` is `m`-pseudo-coherent with vanishing cohomology in degrees strictly
above `b`, then `K ⊗[R]^L L` is `max (m + a) (n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DMod) (n m a b : ℤ)
    (hK : K.IsMPseudoCoherent n)
    (hKvanish : ∀ i : ℤ, a < i → IsZero ((H i).obj K))
    (hL : L.IsMPseudoCoherent m)
    (hLvanish : ∀ j : ℤ, b < j → IsZero ((H j).obj L)) :
    (K ⊗[R]^L L).IsMPseudoCoherent (max (m + a) (n + b)) := sorry

-- Proof sketch: by Lemma `15.65.5`, pseudo-coherent objects admit bounded-above termwise finite
-- projective models, so they satisfy the hypotheses of part `(1)` for suitable cohomological
-- bounds; applying part `(1)` then yields pseudo-coherence of the derived tensor product.
/-- Lemma 15.65.16 (2): if `K` and `L` are pseudo-coherent, then
`K ⊗[R]^L L` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    (K ⊗[R]^L L).IsPseudoCoherent := sorry

end

end CategoryTheory
