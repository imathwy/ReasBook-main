module

public import Topology_Munkres_2000.Book.Exercise_24_1
public import Topology_Munkres_2000.Book.Exercise_24_12

public section

open Set

/-- Example 9.0.1 (1): The closed unit interval is not homeomorphic to the open
unit interval, as distinguished by compactness. -/
theorem closedIntervalNotHomeomorphicOpenInterval :
    ¬ Nonempty (Icc (0 : ℝ) 1 ≃ₜ Ioo (0 : ℝ) 1) := by
  rintro ⟨e⟩
  exact openIntervalNotHomeomorphicClosed ⟨e.symm⟩

/-- Example 9.0.1 (2): The real line is not homeomorphic to the long line, as
distinguished by second countability. -/
theorem realLineNotHomeomorphicLongLine :
    ¬ Nonempty (ℝ ≃ₜ LongLine) := by
  rintro ⟨e⟩
  exact LongLine.noEmbeddingIntoSecondCountable ⟨e.symm, e.symm.isEmbedding⟩

/-- Example 9.0.1 (3): The real line is not homeomorphic to the Euclidean plane,
as distinguished by connectedness after deleting a point. -/
theorem realLineNotHomeomorphicPlane :
    ¬ Nonempty (ℝ ≃ₜ (Fin 2 → ℝ)) := by
  rintro ⟨e⟩
  exact euclideanSpaceNotHomeomorphicReal 2 (by decide) ⟨e.symm⟩
