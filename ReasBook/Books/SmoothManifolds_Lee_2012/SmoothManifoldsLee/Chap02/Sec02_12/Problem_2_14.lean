import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe uE uH uM

open scoped Manifold ContDiff

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/- Problem 2-14: this is exactly the canonical smooth-separation theorem already provided by
`exists_contMDiff_zero_iff_one_iff_of_isClosed`. The bundled `C^∞⟮I, M; ℝ⟯` view and preimage
equalities are derived reformulations, not the owner declaration. -/
recall exists_contMDiff_zero_iff_one_iff_of_isClosed
