import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_9_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_4_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced only ambient ideal-sheaf/subscheme API. The local
-- Chapter 31 owners already fixed nearby are `EffectiveCartierDivisorApproximation` from
-- `Lemma_31_15_8`, `embeddedPoints` from `Definition_31_4_1`, and `Regular` from
-- `Chap28/Definition_28_9_1`, so the source statement is best exposed as the bridge from an
-- approximation to an actual effective Cartier divisor under the no-embedded-points and
-- codimension-one-component hypotheses.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- If a closed subscheme `Z ⊆ X` admits an effective Cartier divisor approximation and `Z` has
no embedded points, then the approximation is already equal to `Z` provided every irreducible
component of `Z` has codimension `1` in `X`, formalized by the ambient stalk dimension condition
at generic points of irreducible components of `Z.subscheme`. -/
theorem isEffectiveCartierDivisor_of_effectiveCartierDivisorApproximation_of_embeddedPoints_eq_empty_of_genericPointsOfIrreducibleComponents_stalk_ringKrullDim_eq_one
    (Z D : X.IdealSheafData) [EffectiveCartierDivisorApproximation D Z]
    (hembedded : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (hcodim :
      ∀ ξ : Z.subscheme, ξ ∈ genericPointsOfIrreducibleComponents Z.subscheme →
        ringKrullDim (X.presheaf.stalk (Z.subschemeι.base ξ)) = 1) :
    IsEffectiveCartierDivisor Z := sorry

/-- Lemma 31.15.9: let `Z ⊆ X` be a closed subscheme of a Noetherian scheme. Assume `Z` has no
embedded points, every irreducible component of `Z` has codimension `1` in `X`, and either every
local ring `\mathcal O_{X,x}` for `x ∈ Z` is a unique factorization domain or `X` is regular.
Then `Z` is an effective Cartier divisor. Here the codimension-one hypothesis is formalized by
requiring `ringKrullDim (\mathcal O_{X,\xi}) = 1` at each generic point `ξ` of an irreducible
component of `Z.subscheme`. -/
@[stacks 0BXH]
theorem isEffectiveCartierDivisor_of_embeddedPoints_eq_empty_of_genericPointsOfIrreducibleComponents_stalk_ringKrullDim_eq_one_of_stalks_uniqueFactorizationMonoid_or_regular
    (Z : X.IdealSheafData)
    (hembedded : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (hcodim :
      ∀ ξ : Z.subscheme, ξ ∈ genericPointsOfIrreducibleComponents Z.subscheme →
        ringKrullDim (X.presheaf.stalk (Z.subschemeι.base ξ)) = 1)
    (hUFD_or_regular :
      (∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨
        AlgebraicGeometry.Scheme.Regular X) :
    IsEffectiveCartierDivisor Z := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
