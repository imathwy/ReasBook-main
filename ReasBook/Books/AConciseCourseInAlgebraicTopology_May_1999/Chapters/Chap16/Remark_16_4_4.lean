import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Tactic.Recall

universe u

open CategoryTheory

-- Semantic recall via `lean_leansearch`: `SSet` is the canonical mathlib owner for simplicial
-- sets, while `TopCat.toSSet` and `SSet.toTop` formalize the combinatorial/topological bridge.

/- Remark 16.4.4. Simplicial methods are formalized in mathlib through simplicial objects and,
in particular, simplicial sets `SSet`; the functors `TopCat.toSSet` and `SSet.toTop` formalize
the standard singular/geometric-realization bridge between topological spaces and simplicial
sets used throughout algebraic topology. -/
#check (SimplicialObject (Type u) : Type (u + 1))
recall SSet : Type (u + 1)
recall TopCat.toSSet : TopCat ⥤ SSet
recall SSet.toTop : SSet ⥤ TopCat
