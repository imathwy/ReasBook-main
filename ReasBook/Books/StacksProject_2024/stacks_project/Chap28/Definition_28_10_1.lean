import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall / analogue check:
-- `lean_leansearch` returned the canonical global owner `topologicalKrullDim`; the project-local
-- Chapter 5 file `Definition_5_10_1` provides the companion local owner `topologicalKrullDimAt`,
-- and `Chap28/Lemma_28_10_2` already states the next dimension lemmas directly with these owners.

/- Definition 28.10.1: for a scheme `X`, the dimension of `X` is the topological Krull dimension
of its underlying topological space, and the dimension at a point `x : X` is the local
topological Krull dimension `topologicalKrullDimAt x`. Both notions are already owned by the
canonical global/local topological dimension API, so this item is a pure recall block. -/
section

variable (X : Scheme.{u}) (x : X)

recall topologicalKrullDim
recall topologicalKrullDimAt

end

end AlgebraicGeometry
