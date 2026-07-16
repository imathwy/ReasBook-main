import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the ideal-sheaf-data owner
-- `Scheme.IdealSheafData` and its functorial pullback `D.comap f`; local Chapter 31 precedent
-- uses `[IsEffectiveCartierDivisor D]` for effective Cartier divisors and
-- `UniqueFactorizationMonoid (X.presheaf.stalk x)` for the stalkwise UFD hypothesis.

/-- Lemma 31.28.2: let `X` be a locally Noetherian scheme, let `U ⊆ X` be an open subscheme,
and let `D ⊆ U` be an effective Cartier divisor. If every stalk `\mathcal O_{X,x}` at a point
of `X \ U` is a unique factorization domain, then `D` extends to an effective Cartier divisor
`D' ⊆ X`; equivalently, the restriction of `D'` to `U` is `D`. -/
@[stacks 0BD8]
theorem exists_isEffectiveCartierDivisor_extension_of_stalks_uniqueFactorizationMonoid
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (D : U.toScheme.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D' : X.IdealSheafData,
      IsEffectiveCartierDivisor D' ∧ D = D'.comap U.ι := sorry

end AlgebraicGeometry.Scheme
