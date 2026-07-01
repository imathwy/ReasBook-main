import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M]

/-- Theorem 2.29 (Level Sets of Smooth Functions): if `K` is a closed subset of a smooth
manifold `M`, then there exists a smooth nonnegative function `f : M → ℝ` such that
`f ⁻¹' {0} = K`. -/
theorem exists_nonneg_smooth_zero_set_eq_of_isClosed
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] {K : Set M} (hK : IsClosed K) :
    ∃ f : C^∞⟮I, M; ℝ⟯, (∀ x, 0 ≤ f x) ∧ f ⁻¹' {0} = K := by
  rcases exists_contMDiff_zero_iff_one_iff_of_isClosed I hK isClosed_empty
      (by simp) with
    ⟨f, hf, hf_range, hzero, _⟩
  refine ⟨⟨f, hf⟩, fun x ↦ (hf_range ⟨x, rfl⟩).1, ?_⟩
  ext x
  simp [hzero x]
