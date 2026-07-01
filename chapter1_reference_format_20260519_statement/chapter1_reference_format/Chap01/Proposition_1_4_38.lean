import Mathlib

open Polynomial

universe u

/- Proposition 1.4.38: the canonical owner of this statement is `AdjoinRoot.isRoot_root`, which
shows that the distinguished element `AdjoinRoot.root P` is a root of the image of `P` in
`AdjoinRoot P`. The textbook's irreducible-field-extension phrasing is a specialization of this
more primitive quotient-ring statement; irreducibility is only needed to regard `AdjoinRoot P`
as a field, not for the root property itself. -/
recall AdjoinRoot.isRoot_root {R : Type u} [CommRing R] (P : R[X]) :
  (P.map (AdjoinRoot.of P)).IsRoot (AdjoinRoot.root P)

section

variable {K : Type u} [Field K]

/- In the field case, the canonical quotient map `AdjoinRoot.of P` is the algebra map, so the
source-facing formulation is exactly the field specialization of `AdjoinRoot.isRoot_root`. -/
#check
  (show (P : K[X]) → (P.map (algebraMap K (AdjoinRoot P))).IsRoot (AdjoinRoot.root P) from
    fun P ↦ by simpa using (AdjoinRoot.isRoot_root P))

end
