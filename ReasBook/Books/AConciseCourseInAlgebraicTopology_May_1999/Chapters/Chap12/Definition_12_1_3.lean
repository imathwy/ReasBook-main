import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory

universe u

-- Semantic recall: `lean_leansearch` surfaced `HomologicalComplex.cycles`; local mathlib inspection
-- shows that the textbook boundaries are packaged by `HomologicalComplex.toCycles`, while the
-- `ShortComplex.ModuleCat` bridge identifies this abstract morphism with the concrete map into a
-- kernel used for the usual quotient presentation of homology.

variable (R : Type u) [CommRing R]
variable (X : ChainComplex (ModuleCat R) ℕ) (i : ℕ)

/- Definition 12.1.3. For a chain complex `X`, cycles in degree `i` are the canonical object
`X.cycles i`. Boundaries are represented by the induced morphism
`X.toCycles (i + 1) i : X.X (i + 1) ⟶ X.cycles i`, whose image is the textbook `B_i(X) ⊆ Z_i(X)`;
`(X.sc i).toCycles_moduleCatCyclesIso_hom` identifies this with the concrete `ModuleCat` map into
the kernel presentation of cycles. The homology module is the canonical object `X.homology i`, and
`(X.sc i).moduleCatHomologyIso` together with
`X.homologyIsCokernel (i + 1) i` records that it is the quotient `Z_i(X) / B_i(X)`. -/
#check X.cycles i
#check X.toCycles (i + 1) i
#check (X.sc i).toCycles_moduleCatCyclesIso_hom
#check X.homology i
#check (X.sc i).moduleCatHomologyIso
#check (X.homologyIsCokernel (i + 1) i (by simp))
