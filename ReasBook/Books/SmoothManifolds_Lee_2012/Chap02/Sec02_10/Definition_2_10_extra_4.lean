import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe uι uE uH uM

/- Definition 2.10-extra-4 (source-facing, recalling the canonical owner): a partition of unity
subordinate to an indexed open cover is formalized by `PartitionOfUnity.IsSubordinate`. -/
recall PartitionOfUnity.IsSubordinate
  {ι : Type uι} {M : Type uM} [TopologicalSpace M] {s : Set M}
  (f : PartitionOfUnity ι M s) (U : ι → Set M) : Prop

/- The smooth variant is formalized by `SmoothPartitionOfUnity.IsSubordinate`. -/
recall SmoothPartitionOfUnity.IsSubordinate
  {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) : Prop
