module

public import Topology_Munkres_2000.Book.Example_26_2.Sequence
public import Mathlib.Topology.Category.LightProfinite.Sequence

public section

open LightProfinite OnePoint

/-- The image of the canonical embedding of `OnePoint ℕ` in `ℝ` is the reciprocal
sequence subspace. -/
theorem range_natUnionInftyEmbedding :
    Set.range LightProfinite.natUnionInftyEmbedding = reciprocalSequenceSubspace := by
  unfold reciprocalSequenceSubspace
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    cases p with
    | infty => simp [LightProfinite.natUnionInftyEmbedding]
    | coe n =>
        refine Set.mem_insert_iff.mpr (.inr ⟨⟨n + 1, Nat.succ_pos n⟩, ?_⟩)
        simp [LightProfinite.natUnionInftyEmbedding]
  · simp only [Set.mem_insert_iff, Set.mem_range]
    rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨∞, by simp [LightProfinite.natUnionInftyEmbedding]⟩
    · refine ⟨OnePoint.some ((n : ℕ) - 1), ?_⟩
      simp [LightProfinite.natUnionInftyEmbedding]

/-- Exercise 29.8: The one-point compactification of the positive integers is
homeomorphic to the real subspace consisting of zero and the reciprocals of
positive integers. -/
noncomputable def onePointNatHomeomorphReciprocalSequence :
    OnePoint ℕ ≃ₜ reciprocalSequenceSubspace :=
  Homeomorph.trans isClosedEmbedding_natUnionInftyEmbedding.isEmbedding.toHomeomorph
    (Homeomorph.setCongr range_natUnionInftyEmbedding)
