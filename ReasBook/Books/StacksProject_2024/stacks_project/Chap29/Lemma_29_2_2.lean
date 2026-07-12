import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Z Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X)

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-side API
-- `AlgebraicGeometry.IsClosedImmersion.lift`,
-- `AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, and
-- `AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData`. The source criterion is therefore
-- stated directly in terms of the kernel ideal sheaves `i.ker` and `i'.ker`, with isomorphism
-- over `X` expressed in the canonical over-category `Over X`.

/-- Lemma 29.2.2 (1): for closed immersions `i : Z ⟶ X` and `i' : Z' ⟶ X`, the morphism `i`
factors through `i'` over `X` if and only if the kernel ideal sheaf of `i'` is contained in the
kernel ideal sheaf of `i`. -/
@[stacks 01QP]
theorem closedImmersion_exists_factor_iff_ker_le
    [IsClosedImmersion i] [IsClosedImmersion i'] :
    (∃ a : Z ⟶ Z', a ≫ i' = i) ↔ i'.ker ≤ i.ker := sorry

/-- Lemma 29.2.2 (2): if closed immersions `i : Z ⟶ X` and `i' : Z' ⟶ X` satisfy
`a ≫ i' = i`, then the factor map `a : Z ⟶ Z'` is itself a closed immersion. -/
@[stacks 01QP]
theorem isClosedImmersion_of_closedImmersion_factor
    [IsClosedImmersion i] [IsClosedImmersion i'] {a : Z ⟶ Z'}
    (ha : a ≫ i' = i) :
    IsClosedImmersion a := sorry

/-- Lemma 29.2.2 (3): for closed immersions `i : Z ⟶ X` and `i' : Z' ⟶ X`, the schemes `Z` and
`Z'` are isomorphic over `X` if and only if their kernel ideal sheaves in `\mathcal O_X`
coincide. -/
@[stacks 01QP]
theorem closedImmersion_overIso_iff_ker_eq
    [IsClosedImmersion i] [IsClosedImmersion i'] :
    Nonempty (Over.mk i ≅ Over.mk i') ↔ i.ker = i'.ker := sorry

end

end AlgebraicGeometry
