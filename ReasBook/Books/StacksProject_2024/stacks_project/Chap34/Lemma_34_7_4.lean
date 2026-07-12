import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.affineCover`,
-- `Scheme.OpenCover.affineRefinement`, and `Scheme.AffineCover`; local Chapter 34 precedent
-- represents fppf covers by `Scheme.fppfPrecoverage`.

/-- Lemma 34.7.4: an fppf cover of an affine scheme admits a finite refinement by affine schemes,
and the refining affine schemes may be chosen as open affines of the original covering schemes. -/
@[stacks 021P]
theorem existsFiniteAffineOpenRefinementOfFppfCover
    {T : Scheme} [IsAffine T] (𝒰 : T.Cover Scheme.fppfPrecoverage) :
    ∃ (𝒱 : T.AffineCover
        ((@Flat) ⊓ (@LocallyOfFinitePresentation : MorphismProperty Scheme))) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := sorry

end AlgebraicGeometry
