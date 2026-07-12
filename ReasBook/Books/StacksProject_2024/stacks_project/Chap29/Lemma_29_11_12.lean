import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-morphism owner
-- `AlgebraicGeometry.IsAffineHom`, the separated-diagonal bridge
-- `AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal`, and the affine-property diagonal
-- infrastructure. The source item is therefore recorded as relative and absolute `IsAffineHom`
-- consequences rather than via a wrapper definition.

section

variable {X Y S : Scheme.{u}}

/-- Lemma 29.11.12 (1): if `g : X ⟶ Y` is a morphism over `S`, the composite `X ⟶ S` is affine,
and the diagonal `Y ⟶ Y ×[S] Y` is affine, then `g` is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffineHom_comp_of_affineDiagonal
    (g : X ⟶ Y) (f : Y ⟶ S) [IsAffineHom (g ≫ f)] [IsAffineHom (pullback.diagonal f)] :
    IsAffineHom g := sorry

/-- Lemma 29.11.12 (2): if `g : X ⟶ Y` is a morphism over `S`, the composite `X ⟶ S` is affine,
and `Y` is separated over `S`, then `g` is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffineHom_comp_of_isSeparated
    (g : X ⟶ Y) (f : Y ⟶ S) [IsAffineHom (g ≫ f)] [IsSeparated f] :
    IsAffineHom g := sorry

/-- Lemma 29.11.12 (3): a morphism from an affine scheme to a scheme with affine diagonal is
affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffine_of_affineDiagonal
    (g : X ⟶ Y) [IsAffine X] [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    IsAffineHom g := sorry

/-- Lemma 29.11.12 (4): a morphism from an affine scheme to a separated scheme is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffine_of_isSeparated
    (g : X ⟶ Y) [IsAffine X] [Y.IsSeparated] :
    IsAffineHom g := sorry

end

end AlgebraicGeometry
