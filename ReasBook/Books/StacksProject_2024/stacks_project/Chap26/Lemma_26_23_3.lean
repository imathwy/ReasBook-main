import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` and nearby Chapter 26/29 precedent identify
-- `AlgebraicGeometry.IsSeparated.isSeparated_of_mono` as the canonical owner-side theorem for this
-- source statement.

variable {X Y : Scheme.{u}}

/-- Lemma 26.23.3: a monomorphism of schemes is separated. -/
@[stacks 01L4]
theorem Scheme.Hom.isSeparated_of_mono (f : X ⟶ Y) [Mono f] :
    IsSeparated f := sorry

end AlgebraicGeometry
