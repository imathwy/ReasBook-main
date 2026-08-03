module

public import Topology_Munkres_2000.Book.Example_24_1.LinearContinuum
public import Topology_Munkres_2000.Book.Theorem_27_1
public import Mathlib.Topology.Compactness.Lindelof

public section

namespace OrderedSquare

/-- The ordered square is compact. -/
instance instCompactSpace : CompactSpace Iₒ² := by
  -- The least-upper-bound property makes the interval from bottom to top compact.
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  letI : BoundedOrder Iₒ² :=
    inferInstanceAs (BoundedOrder LexUnitSquare)
  letI : LeastUpperBoundProperty Iₒ² :=
    LinearContinuum.leastUpperBoundProperty
  refine ⟨?_⟩
  simpa only [Set.Icc_bot_top] using
    (isCompact_Icc : IsCompact (Set.Icc (⊥ : Iₒ²) ⊤))

end OrderedSquare
