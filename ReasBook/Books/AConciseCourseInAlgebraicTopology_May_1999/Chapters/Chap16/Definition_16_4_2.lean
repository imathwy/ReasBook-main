import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Topology.Category.TopCat.Basic

universe u

open CategoryTheory

-- Semantic recall via `lean_leansearch`: mathlib formalizes simplicial spaces as simplicial
-- objects in `TopCat`, with the face and degeneracy operators given by the canonical maps `δ`
-- and `σ` in `TopCat`.

variable (X : SimplicialObject TopCat.{u})

/- Definition 16.4.2. A simplicial space is canonically formalized in mathlib by
`SimplicialObject TopCat`, the type of simplicial objects in `TopCat`, i.e.
sequences of spaces with continuous face and degeneracy maps satisfying the simplicial identities.
-/
#check (SimplicialObject TopCat.{u} : Type (u + 1))
#check X.δ
#check X.σ
