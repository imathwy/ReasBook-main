import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme predicate `IsAffine`;
-- local closed-subscheme precedent represents closed subschemes by `Scheme.IdealSheafData`.

/-- Lemma 32.11.3: let `X` be a scheme which is set-theoretically the union of finitely
many affine closed subschemes. Then `X` is affine. -/
@[stacks 09NL]
theorem isAffine_of_finite_affine_closedSubscheme_cover
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (Z : ι → X.IdealSheafData)
    [∀ j, IsAffine (Z j).subscheme]
    (hcover : ∀ x : X, ∃ j : ι, x ∈ (Z j).support) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
