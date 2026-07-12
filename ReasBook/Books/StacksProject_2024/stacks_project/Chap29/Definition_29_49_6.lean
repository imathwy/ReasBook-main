import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsIntegral X]

/- Semantic recall: `lean_leansearch` surfaced the canonical owner
`AlgebraicGeometry.Scheme.functionField` together with the field instance
`AlgebraicGeometry.instFieldCarrierFunctionField`. This item is therefore a direct recall of the
existing scheme-side owner `R(X)`, not a place for a redundant local alias. -/

/- Definition 29.49.6: let `X` be an integral scheme. The function field, or the field of rational
functions of `X`, is the canonical owner `X.functionField`, written in the Stacks Project as
`R(X)`. -/
recall AlgebraicGeometry.Scheme.functionField
    (X : Scheme.{u}) [IrreducibleSpace X] : CommRingCat

/- Companion recall: for an integral scheme `X`, the canonical owner `X.functionField` carries its
field structure. -/
recall AlgebraicGeometry.instFieldCarrierFunctionField
    (X : Scheme.{u}) [IsIntegral X] : Field ↥X.functionField

end
