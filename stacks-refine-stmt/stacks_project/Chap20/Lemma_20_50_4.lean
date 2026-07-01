import Mathlib
import stacks_project.Chap20.Definition_20_49_1
import stacks_project.Chap20.Lemma_20_42_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: work locally on `X` using compatibility of both sides with localization. Replace
-- the perfect object `K` by a strictly perfect representative, then argue by distinguished
-- triangles and stupid truncations to reduce to a finite free module sheaf in one degree, where
-- the comparison is the evident isomorphism.
/-- Lemma 20.50.4: let `(X, \mathcal O_X)` be a ringed space and let `K`, `L`, `M ∈ D(\mathcal
O_X)`. If `K` is perfect, then the canonical map
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)` from Lemma `20.42.9` is an
isomorphism. -/
theorem isIso_tensorInternalHomToIteratedInternalHom_of_isPerfect
    {K L M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (tensorInternalHomToIteratedInternalHom K L M) := sorry

end

end AlgebraicGeometry.RingedSpace
