import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced mathlib's relative-normalization API
`Scheme.Hom.normalization`, `Scheme.Hom.toNormalization`, and
`Scheme.Hom.fromNormalization`, together with the pointwise owner
`Scheme.Hom.QuasiFiniteAt`. Local Chapter 29 precedent records source-side finite type as
`Scheme.Hom.FiniteType`. -/

/-- Theorem 29.56.1 (Algebraic version of Zariski's Main Theorem): if
`f : Y ⟶ X` is affine and of finite type, and `X'` is the normalization of `X` in `Y`,
then there is an open subscheme `U' ⊆ X'` such that the inverse image
`(f')⁻¹(U') ⟶ U'` is an isomorphism and `(f')⁻¹(U')` is exactly the locus where `f`
is quasi-finite. -/
@[stacks 03GT]
theorem Scheme.Hom.exists_open_isIso_toNormalization_restrict_preimage_eq_quasiFiniteAt
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] [Scheme.Hom.FiniteType f] :
    ∃ U' : f.normalization.Opens,
      IsIso (f.toNormalization ∣_ U') ∧
        ((f.toNormalization ⁻¹ᵁ U' : Y.Opens) : Set Y) = { y : Y | f.QuasiFiniteAt y } := sorry

end AlgebraicGeometry
