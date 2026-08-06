import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open scoped FundamentalGroupoid

variable (X : Type u) [TopologicalSpace X]

/- Lemma 2.5.3 (1): for a topological space `X`, the fundamental groupoid
`πₓ (TopCat.of X)` carries the canonical groupoid structure whose inverses are represented by
path reversal. -/
#check (inferInstance : Groupoid (πₓ (TopCat.of X)))

/- Lemma 2.5.3 (2): the assignment sending a topological space to its fundamental groupoid is the
canonical functor `π : TopCat ⥤ Grpd`. -/
#check (π : TopCat ⥤ Grpd)
