import Mathlib
import StacksProject_2024.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the scheme-level quotient instance
-- `AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`; the source-facing Stacks statement
-- is the locally-ringed-space closed-immersion owner `RingedSpace.IsClosedImmersion`.

/-- Example 26.8.1: for a ring `R` and an ideal `I ⊆ R`, the morphism of affine schemes
`Spec(R/I) → Spec R` induced by the quotient map is a closed immersion of locally ringed spaces. -/
@[stacks 01IG]
instance RingedSpace.IsClosedImmersion.specMap_quotient
    (R : Type u) [CommRing R] (I : Ideal R) :
    RingedSpace.IsClosedImmersion
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).toShHom := sorry

end AlgebraicGeometry
