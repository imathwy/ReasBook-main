import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2

open scoped Topology Topology.Homotopy

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for based
-- homotopy groups, and local Chapter 9 precedent packages the inclusion-induced maps from the pair
-- long exact sequence through explicit continuous maps together with their induced homotopy-group
-- morphisms. The direct map `π_ n(A, x) → π_ n(X, x)` is
-- `pairSubspaceInclusionHomotopyGroupMap A x n`, while the loop-space models used in
-- Theorem 9.2.2 are `pairLoopSubspaceInclusionHomotopyGroupMap A x q` in positive degrees and
-- `pairLoopSubspaceInclusionPiZeroMap A x` in degree `1`. Likewise,
-- `pairLoopToRelativeHomotopyGroupMap A x q` and `pairLoopToRelativePiZeroMap A x` record the map
-- `π_ n(X, x) → π_ n(X, A, x)` in positive degrees and degree `1`, respectively.

/- Remark 9.2.5: the map `π_ n(A, x) → π_ n(X, x)` is the map induced by the inclusion
`(A, x) ↪ (X, x)`, and the map `π_ n(X, x) → π_ n(X, A, x)` is the map induced by the inclusion
`(X, x, x) ↪ (X, A, x)`. In the local Chapter 9 API the first family is recorded by the inclusion
`pairSubspaceInclusion A`, its direct induced map `pairSubspaceInclusionHomotopyGroupMap A x n`,
and the loop-space models `pairLoopSubspaceInclusionHomotopyGroupMap A x q` and
`pairLoopSubspaceInclusionPiZeroMap A x` used in Theorem 9.2.2. The second family is recorded by
the underlying path-space map `pairLoopToRelativePathSpaceMap A x`, the degree-`1` map
`pairLoopToRelativePiZeroMap A x`, and the positive-degree model
`pairLoopToRelativeHomotopyGroupMap A x q` under the standard loop/path-space identifications from
Theorem 9.2.2. -/
#check pairSubspaceInclusion

#check pairSubspaceInclusionHomotopyGroupMap

#check pairLoopSubspaceInclusionMap

#check pairLoopSubspaceInclusionHomotopyGroupMap

#check pairLoopSubspaceInclusionPiZeroMap

#check pairLoopToRelativePathSpaceMap

#check pairLoopToRelativePiZeroMap

#check pairLoopToRelativeHomotopyGroupMap
