import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-morphism theorem
-- `AlgebraicGeometry.isAffineHom_of_isInducing`; the source hypothesis "homeomorphism onto a
-- closed subset" is exactly the topological condition `Topology.IsClosedEmbedding` on `f.base`.

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.45.4: if a morphism of schemes is a homeomorphism onto a closed subset of the target,
then it is affine. In the current Lean API this hypothesis is expressed as the underlying map on
topological spaces being a closed embedding. -/
theorem isAffineHom_of_base_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding ⇑(ConcreteCategory.hom f.base)) :
    IsAffineHom f := sorry

end

end AlgebraicGeometry
