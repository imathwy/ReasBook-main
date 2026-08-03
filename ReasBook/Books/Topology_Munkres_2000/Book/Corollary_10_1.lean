module

public import Mathlib.SetTheory.Ordinal.Basic

public section

/-- Corollary 10.1. There exists an uncountable well-ordered set. -/
theorem existsUncountableWellOrder : ∃ W : WellOrder.{1}, Uncountable W.α :=
  ⟨⟨Cardinal, WellOrderingRel, inferInstance⟩, inferInstance⟩
