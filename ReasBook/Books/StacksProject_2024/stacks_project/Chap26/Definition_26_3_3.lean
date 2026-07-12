import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Tactic.Recall

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : LocallyRingedSpace.{u}) (U : Opens X)

-- Canonical owner recall: the open subspace attached to `U` is the restriction
-- `X.restrict U.isOpenEmbedding`, and its inclusion into `X` is `X.ofRestrict U.isOpenEmbedding`.

/- Definition 26.3.3: for an open subset `U ⊆ X` of a locally ringed space `X`, the open
subspace of `X` associated to `U` is the canonical restriction
`X.restrict U.isOpenEmbedding`. -/
recall LocallyRingedSpace.restrict
#check X.restrict U.isOpenEmbedding

/- Companion recall: the restricted locally ringed space comes with the canonical inclusion
`X.ofRestrict U.isOpenEmbedding : X.restrict U.isOpenEmbedding ⟶ X`. -/
recall LocallyRingedSpace.ofRestrict
#check X.ofRestrict U.isOpenEmbedding

end AlgebraicGeometry
