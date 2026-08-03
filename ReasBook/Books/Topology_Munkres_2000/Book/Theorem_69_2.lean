module

import Mathlib.GroupTheory.CoprodI

open Monoid.CoprodI

/-
Theorem 69.2. The free product of two free groups is free on the disjoint union of
their chosen bases. More generally, `FreeGroupBasis.coprodI` constructs a basis of
an indexed free product with index type `Σ i, X i`, the canonical tagged disjoint
union of the factor basis indices.
-/
#check FreeGroupBasis.coprodI
