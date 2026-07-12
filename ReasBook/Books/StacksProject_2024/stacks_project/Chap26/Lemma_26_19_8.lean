import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical theorem
-- `AlgebraicGeometry.isClosedMap_iff_specializingMap`. Definition 5.19.4 identifies
-- "specializations lift along `f`" with `SpecializingMap f.base`, so no local wrapper is needed.

/- Lemma 26.19.8: a quasi-compact morphism of schemes is closed if and only if
specializations lift along it. This is exactly the canonical theorem
`AlgebraicGeometry.isClosedMap_iff_specializingMap`. -/
recall AlgebraicGeometry.isClosedMap_iff_specializingMap

section

variable {X S : Scheme} (f : X ⟶ S) [QuasiCompact f]

#check (AlgebraicGeometry.isClosedMap_iff_specializingMap f :
    IsClosedMap f.base ↔ SpecializingMap f.base)

end
