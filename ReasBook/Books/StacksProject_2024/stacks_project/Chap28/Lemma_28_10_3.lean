import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Order AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` returned the canonical ring-dimension owners
-- `IsLocalization.AtPrime.ringKrullDim_eq_height` and
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`; local Chapter 5 files use `coheight` on
-- `IrreducibleCloseds` for codimension.

variable (X : Scheme.{u})

/-- Lemma 28.10.3: if `Y` is an irreducible closed subset of a scheme `X` and `ξ` is a generic
point of `Y`, then the codimension of `Y` in `X`, expressed canonically as `coheight Y`, equals
the Krull dimension of the local ring `X.presheaf.stalk ξ`. -/
theorem codim_irreducibleClosed_eq_ringKrullDim_stalk_of_isGenericPoint
    (Y : IrreducibleCloseds X) {ξ : X} (hξ : IsGenericPoint ξ (Y : Set X)) :
    coheight Y = ringKrullDim (X.presheaf.stalk ξ) := sorry

end AlgebraicGeometry.Scheme
