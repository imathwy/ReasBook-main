import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic search tool `lean_leansearch` was unavailable in this environment; verified locally
-- against mathlib's `t2_iff_isClosed_diagonal`.
/-
Remark 5.1.20: a space `X` is Hausdorff precisely when its diagonal
`Δ_X = {(x, x)}` is closed in the ordinary product `X × X`.
-/
recall t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (Set.diagonal X)
