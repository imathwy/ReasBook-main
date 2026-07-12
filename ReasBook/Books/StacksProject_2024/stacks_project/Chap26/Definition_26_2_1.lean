import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (X Y : LocallyRingedSpace.{u})
variable (x : X)
variable (f : X ⟶ Y)

-- Semantic recall: `lean_leansearch` and direct mathlib source inspection both point to the
-- canonical owners `AlgebraicGeometry.LocallyRingedSpace`,
-- `AlgebraicGeometry.LocallyRingedSpace.Hom`, and the residue-field API in
-- `Mathlib/Geometry/RingedSpace/LocallyRingedSpace(.ResidueField).lean`.
/- Source/core/bridge triage:
- `source-facing`: a locally ringed space, its local ring and residue field at a point, and the
  induced stalk and residue-field maps of a morphism.
- `core/canonical`: `LocallyRingedSpace`, `LocallyRingedSpace.Hom`,
  `LocallyRingedSpace.Hom.stalkMap`, and `LocallyRingedSpace.residueFieldMap`.
- `bridge/view`: the pointwise surfaces `X.residueField x`, `f.stalkMap x`, and
  `LocallyRingedSpace.residueFieldMap f x` used by later chapter files. -/

/- Definition 26.2.1 (1): the Stacks definition of a locally ringed space is the canonical
mathlib owner `AlgebraicGeometry.LocallyRingedSpace`, whose stalk-locality field is part of the
structure. -/
recall LocallyRingedSpace

/- Definition 26.2.1 (2): for a locally ringed space `X` and a point `x : X`, the local ring at
`x` is the stalk `X.presheaf.stalk x`; its maximal ideal is `IsLocalRing.maximalIdeal
(X.presheaf.stalk x)`; and its residue field is `X.residueField x`. -/
recall LocallyRingedSpace.residueField
#check (inferInstance : IsLocalRing (X.presheaf.stalk x))
#check (IsLocalRing.maximalIdeal (X.presheaf.stalk x) : Ideal (X.presheaf.stalk x))
#check X.residueField x

/- Definition 26.2.1 (3): a morphism of locally ringed spaces is the canonical owner
`AlgebraicGeometry.LocallyRingedSpace.Hom`, and it induces canonical maps on stalks and residue
fields; the induced residue-field map is the canonical owner
`AlgebraicGeometry.LocallyRingedSpace.residueFieldMap`, and the local homomorphism condition is
available as a typeclass instance on the stalk map. -/
recall LocallyRingedSpace.Hom
recall LocallyRingedSpace.Hom.stalkMap
recall LocallyRingedSpace.residueFieldMap
recall LocallyRingedSpace.isLocalHomStalkMap
#check f.stalkMap x
#check LocallyRingedSpace.residueFieldMap f x
#check (inferInstance : IsLocalHom (f.stalkMap x).hom)

end AlgebraicGeometry
