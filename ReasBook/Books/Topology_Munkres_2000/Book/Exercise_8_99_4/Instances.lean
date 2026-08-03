module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Order.Basic

public section

/-- The dictionary order topology on the lexicographically ordered real plane. -/
instance realProdLexTopologicalSpace : TopologicalSpace (ℝ ×ₗ ℝ) :=
  Preorder.topology (ℝ ×ₗ ℝ)
