import Mathlib.Tactic.Recall
import Mathlib.Topology.CWComplex.Classical.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex` in
-- `Mathlib.Topology.CWComplex.Classical.Basic` is the canonical owner for Whitehead-style CW
-- structures, with the absolute-space skeleta and attaching-cell lemmas already provided in the
-- same API.

/- Definition 10.1.2: the source definition of a CW complex is formalized in mathlib by
`Topology.CWComplex C` for a CW structure on a subspace `C : Set X`; for a space `X` itself, one
uses `C = Set.univ`. The checks below therefore use the absolute `Topology.CWComplex` API
directly, encoding that a CW complex is the union of its skeleta, has `0`-cells given by points,
and is built by attaching higher-dimensional cells along their boundaries. -/
recall Topology.CWComplex {X : Type u} [TopologicalSpace X] (C : Set X) : Type (u + 1)

#check Topology.CWComplex.iUnion_skeleton_eq_complex
#check Topology.CWComplex.closedCell_zero_eq_singleton
#check Topology.CWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ
#check Topology.CWComplex.cellFrontier_subset_skeleton
