module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Mathlib.Topology.Sequences

public section

universe u

/-- Theorem 28.2 (1). In a metrizable space, compactness is equivalent to limit point
compactness. -/
theorem compactSpace_iff_limitPointCompactSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    CompactSpace X ↔ LimitPointCompactSpace X := by
  constructor
  · intro h
    exact (limitPointCompactSpace_iff_countablyCompactSpace X).2
      ⟨h.isCompact_univ.isCountablyCompact⟩
  · intro h
    have h_countablyCompact := (limitPointCompactSpace_iff_countablyCompactSpace X).1 h
    exact compactSpace_iff_seqCompactSpace.2
      ⟨h_countablyCompact.isCountablyCompact_univ.isSeqCompact⟩

/-- Theorem 28.2 (2). In a metrizable space, limit point compactness is equivalent to
sequential compactness. -/
theorem limitPointCompactSpace_iff_seqCompactSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    LimitPointCompactSpace X ↔ SeqCompactSpace X := by
  constructor
  · intro h
    have h_countablyCompact := (limitPointCompactSpace_iff_countablyCompactSpace X).1 h
    exact ⟨h_countablyCompact.isCountablyCompact_univ.isSeqCompact⟩
  · intro h
    exact (limitPointCompactSpace_iff_countablyCompactSpace X).2
      ⟨h.isSeqCompact_univ.isCountablyCompact⟩

-- Mathlib's direct equivalence between compactness and sequential compactness.
#check compactSpace_iff_seqCompactSpace
