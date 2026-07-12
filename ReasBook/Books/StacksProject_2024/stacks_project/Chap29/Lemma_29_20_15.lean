import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical separatedness bridge
`AlgebraicGeometry.IsSeparated.isSeparated_of_mono` and the scheme-morphism owners
`LocallyOfFiniteType` and `LocallyQuasiFinite`; no exact imported theorem for the combined
Stacks statement was found, so the two source conclusions are recorded as atomic bridges. -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.20.15 (1): a locally finite type monomorphism of schemes is separated. -/
@[stacks 0CT8]
theorem isSeparated_of_locallyOfFiniteType_of_mono [LocallyOfFiniteType f] [Mono f] :
    IsSeparated f := sorry

/-- Lemma 29.20.15 (2): a locally finite type monomorphism of schemes is locally quasi-finite. -/
@[stacks 0CT8]
theorem locallyQuasiFinite_of_locallyOfFiniteType_of_mono [LocallyOfFiniteType f] [Mono f] :
    LocallyQuasiFinite f := sorry

end AlgebraicGeometry
