import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_23 (from Chap02/Sec02_10) -/
open scoped ContDiff Manifold

universe uι uE uH uM

variable
  {ι : Type uι}
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]

-- Semantic search note: the MCP tool `lean_leansearch` was unavailable in this environment; local
-- precedent and `#check` confirmed `SmoothPartitionOfUnity.exists_isSubordinate` as the canonical
-- owner theorem.

/-- Theorem 2.23 (Existence of Partitions of Unity): every indexed open cover of a smooth manifold
admits a smooth partition of unity subordinate to it. -/
theorem exists_smoothPartitionOfUnity_isSubordinate
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (U : ι → Set M) (hU_open : ∀ i, IsOpen (U i)) (hU_cover : Set.univ ⊆ ⋃ i, U i) :
    ∃ f : SmoothPartitionOfUnity ι I M Set.univ, f.IsSubordinate U := sorry
