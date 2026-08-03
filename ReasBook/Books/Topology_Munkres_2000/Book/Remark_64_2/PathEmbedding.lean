module

public import Mathlib.Topology.Path

public section

universe u

namespace Path

/-- Helper for Remark 64.2: concatenating two embedded paths that meet only at their common
endpoint gives another embedded path. -/
lemma trans_isEmbedding_of_range_inter_eq_singleton {X : Type u} [TopologicalSpace X]
    [T2Space X] {a b c : X} (γ : Path a b) (δ : Path b c)
    (hγ : Topology.IsEmbedding γ) (hδ : Topology.IsEmbedding δ)
    (hinter : Set.range γ ∩ Set.range δ = {b}) :
    Topology.IsEmbedding (γ.trans δ) := by
  -- Compactness of the interval reduces the topological claim to injectivity.
  refine ((γ.trans δ).continuous.isClosedEmbedding ?_).isEmbedding
  intro t u htu
  simp only [Path.trans_apply] at htu
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · by_cases hu : (u : ℝ) ≤ 1 / 2
    · -- On the first half, injectivity of `γ` identifies the rescaled parameters.
      rw [dif_pos ht, dif_pos hu] at htu
      have hscaled := congrArg Subtype.val (hγ.injective htu)
      apply Subtype.ext
      dsimp at hscaled ⊢
      linarith
    · -- Crossing from the first path to the second can occur only at the glued endpoint.
      rw [dif_pos ht, dif_neg hu] at htu
      have hcommon : γ ⟨2 * t,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ ∈
          Set.range γ ∩ Set.range δ := by
        constructor
        · exact Set.mem_range_self _
        · refine ⟨⟨2 * u - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hu).le, u.2.2⟩⟩, ?_⟩
          exact htu.symm
      rw [hinter, Set.mem_singleton_iff] at hcommon
      have htEnd := congrArg Subtype.val (hγ.injective
        (hcommon.trans (Path.target γ).symm))
      have huStart := congrArg Subtype.val (hδ.injective
        ((htu.symm.trans hcommon).trans (Path.source δ).symm))
      apply Subtype.ext
      dsimp at htEnd huStart ⊢
      linarith
  · by_cases hu : (u : ℝ) ≤ 1 / 2
    · -- The opposite crossing case likewise forces both parameters to the midpoint.
      rw [dif_neg ht, dif_pos hu] at htu
      have hcommon : δ ⟨2 * t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ ∈
          Set.range γ ∩ Set.range δ := by
        constructor
        · refine ⟨⟨2 * u,
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1, hu⟩⟩, ?_⟩
          exact htu.symm
        · exact Set.mem_range_self _
      rw [hinter, Set.mem_singleton_iff] at hcommon
      have htStart := congrArg Subtype.val (hδ.injective
        (hcommon.trans (Path.source δ).symm))
      have huEnd := congrArg Subtype.val (hγ.injective
        ((htu.symm.trans hcommon).trans (Path.target γ).symm))
      apply Subtype.ext
      dsimp at htStart huEnd ⊢
      linarith
    · -- On the second half, injectivity of `δ` identifies the rescaled parameters.
      rw [dif_neg ht, dif_neg hu] at htu
      have hscaled := congrArg Subtype.val (hδ.injective htu)
      apply Subtype.ext
      dsimp at hscaled ⊢
      linarith

end Path
