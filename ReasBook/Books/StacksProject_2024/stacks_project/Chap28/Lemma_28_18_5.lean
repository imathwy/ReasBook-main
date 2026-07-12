import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib theorem
-- `Scheme.isPullback_toSpecΓ_toSpecΓ`, whose assumptions are stronger than the textbook wording.
-- The source-facing statement below keeps the Stacks hypotheses explicit for this item and records
-- the corresponding cartesian square for an open immersion of quasi-affine schemes.

/-- Lemma 28.18.5: if `j : U ⟶ V` is an open immersion of quasi-affine schemes, then the square
formed by `j`, the canonical maps `U.toSpecΓ` and `V.toSpecΓ`, and
`Spec.map (Scheme.Hom.appTop j)` is cartesian. -/
@[stacks 0ARY]
theorem isPullback_toSpecΓ_of_isOpenImmersion
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (hU : U.IsQuasiAffine) (hV : V.IsQuasiAffine) :
    IsPullback j U.toSpecΓ V.toSpecΓ (Spec.map (Scheme.Hom.appTop j)) := sorry

end AlgebraicGeometry.Scheme.Hom
