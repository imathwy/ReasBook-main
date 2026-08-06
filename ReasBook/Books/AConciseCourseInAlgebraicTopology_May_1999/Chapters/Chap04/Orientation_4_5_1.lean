import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

-- Semantic recall: the orientation item only needs the ambient freeness predicate
-- `IsFreeGroup`; the actual Nielsen-Schreier theorem surface is recalled separately in
-- `Theorem_4_5_2.lean`.

/- Orientation 4.5.1

A subgroup of a free group is free; in the repository, the ambient notion of
freeness is mathlib's predicate `IsFreeGroup G`, while the actual Nielsen-Schreier
instance is recalled separately in `Theorem_4_5_2.lean`. The discussion of graphs
and covering spaces records the proof route, not extra source-facing data.
-/
/- The ambient source-facing predicate for free groups is `IsFreeGroup G`. -/
#check IsFreeGroup
