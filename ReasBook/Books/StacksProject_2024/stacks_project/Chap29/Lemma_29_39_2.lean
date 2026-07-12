import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- `lean_leansearch` recalled `Scheme.IsQuasiAffine`, `LocallyOfFiniteType`, and `IsImmersion`,
-- while local Chapter 28/29 precedent already uses the relative affine-space owner
-- `AffineSpace (Fin n) S` with projection notation `↘`. The source is therefore recorded directly
-- as an existence theorem for an immersion over `S` into relative affine `n`-space.

/-- Lemma 29.39.2: let `π : X ⟶ S` be a morphism of schemes. Assume that `X` is quasi-affine and
`π` is locally of finite type. Then there exist `n ≥ 0` and an immersion `i : X ⟶ \mathbf A^n_S`
over `S`. -/
@[stacks 04II]
theorem exists_immersion_to_affineSpace_of_isQuasiAffine_locallyOfFiniteType
    {X S : Scheme.{u}} (π : X ⟶ S) (hX : X.IsQuasiAffine) [LocallyOfFiniteType π] :
    ∃ (n : ℕ) (i : X ⟶ AffineSpace (Fin n) S),
      IsImmersion i ∧ (i ≫ (AffineSpace (Fin n) S ↘ S) = π) := sorry

end AlgebraicGeometry
