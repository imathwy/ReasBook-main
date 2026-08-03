module

public import Topology_Munkres_2000.Book.Example_3_11.Order

@[expose] public section

open Prod.Lex

/-- Example 3.11 (1): In the dictionary order on `ℝ × ℝ`, increasing the second
coordinate while fixing the first increases the point. -/
theorem realPlaneLex_lt_of_same_fst {p q : LexPlane} (hfst : p.1 = q.1)
    (hsnd : p.2 < q.2) : p < q :=
  lt_iff.mpr (.inr ⟨hfst, hsnd⟩)

/-- Example 3.11 (2): In the dictionary order on `ℝ × ℝ`, increasing the first
coordinate increases the point regardless of the second coordinate. -/
theorem realPlaneLex_lt_of_fst_lt {p q : LexPlane} (hfst : p.1 < q.1) : p < q :=
  lt_iff.mpr (.inl hfst)
