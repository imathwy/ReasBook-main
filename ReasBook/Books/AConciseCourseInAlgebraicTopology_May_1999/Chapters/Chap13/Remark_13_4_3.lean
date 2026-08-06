module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.ComplexShapeSigns

public section

open ComplexShape

-- The canonical total-complex symmetry API used by this remark is provided by mathlib:
-- `π_symm` records preservation of total degree under `(p, q) ↦ (q, p)`,
-- `symmetryEquiv` is the induced fiberwise transport, and
-- `σ_def` gives the resulting Koszul sign `(p * q).negOnePow`.

/- Remark 13.4.3: in the symmetry underlying the product-chain isomorphism, the transposition of
the suspension coordinates `(p, q) ↦ (q, p)` preserves the total degree and contributes the
Koszul sign `(p * q).negOnePow`, i.e. `(-1)^(p*q)`. Thus the sign in the product-chain
isomorphism reflects the transposition of suspension coordinates. -/
#check π_symm
#check symmetryEquiv
#check σ_def
