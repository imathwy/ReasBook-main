import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

-- Semantic recall: `FundamentalGroup` and `IsFreeGroup` are already the canonical mathlib
-- surfaces for the chapter's introductory discussion of graph applications to fundamental groups
-- and free groups.

/- Orientation 4.1.1

This chapter introduces graphs through their homotopy-theoretic applications.
For the later statements in this chapter, the canonical mathlib surfaces are the
fundamental group `FundamentalGroup X x` of a topological space `X` at a
basepoint `x` and the predicate `IsFreeGroup G`, so this item is a direct recall
block rather than a duplicate wrapper declaration.
-/
#check FundamentalGroup

/- The chapter's ambient free-group predicate is mathlib's canonical proposition
`IsFreeGroup G`. -/
#check IsFreeGroup
