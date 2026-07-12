import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsSeparated`,
-- `Scheme.IsSeparated`, `IsAffineOpen`, and the closed-immersion/product API. Nearby Chapter 26
-- precedent uses `Scheme.Hom.isAffineOpen_inter_of_isSeparated` for affine intersections over a
-- common affine target and `prod.lift`/`Scheme.Hom.resLE` for the product map of open subschemes.

variable {X S : Scheme.{u}}

/-- Lemma 26.21.16 (1): if `f : X ⟶ S` is separated and `S` is a separated scheme, then the
intersection of any two affine open subschemes of `X` is affine. -/
@[stacks 01KW]
theorem Scheme.Hom.isAffineOpen_inter_of_isSeparated_of_target_isSeparated
    (f : X ⟶ S) [IsSeparated f] [S.IsSeparated]
    (U V : X.affineOpens) :
    IsAffineOpen ((U : X.Opens) ⊓ (V : X.Opens)) := sorry

/-- Lemma 26.21.16 (2): under the same hypotheses, the intersection open subscheme
`U ∩ V` maps as a closed subscheme of the product `U × V`. -/
@[stacks 01KW]
theorem Scheme.Hom.isClosedImmersion_inter_to_prod_of_isSeparated_of_target_isSeparated
    (f : X ⟶ S) [IsSeparated f] [S.IsSeparated]
    (U V : X.affineOpens) :
    IsClosedImmersion
      (prod.lift
        (Scheme.Hom.resLE (𝟙 X) (U : X.Opens) ((U : X.Opens) ⊓ (V : X.Opens))
          (inf_le_left : (U : X.Opens) ⊓ (V : X.Opens) ≤ (U : X.Opens)))
        (Scheme.Hom.resLE (𝟙 X) (V : X.Opens) ((U : X.Opens) ⊓ (V : X.Opens))
          (inf_le_right : (U : X.Opens) ⊓ (V : X.Opens) ≤ (V : X.Opens)))) := sorry

end AlgebraicGeometry
