import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe u

-- Semantic recall via `lean_leansearch`: `SSet` in
-- `Mathlib.AlgebraicTopology.SimplicialSet.Basic` is the canonical mathlib owner for simplicial
-- sets, with underlying raw owner `CategoryTheory.SimplicialObject (Type u)`.

/- Definition 16.4.1. A simplicial set is canonically formalized in mathlib by `SSet`, the type
of simplicial objects in `Type u`, i.e. `CategoryTheory.SimplicialObject (Type u)`, with face and
degeneracy maps satisfying the simplicial identities. -/
#check (SSet : Type (u + 1))
#check (CategoryTheory.SimplicialObject (Type u) : Type (u + 1))
