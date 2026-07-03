import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uι uM

variable {ι : Type uι} {n : ℕ} [NeZero n] {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

/- Exercise 2.24: on a smooth manifold with boundary, every open cover admits a smooth partition of
unity subordinate to it. This is the boundary-model specialization of the canonical owner theorem
`SmoothPartitionOfUnity.exists_isSubordinate`, with `I = 𝓡∂ n` and `s = Set.univ`. -/
#check
  (SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ n) isClosed_univ :
    ∀ U : ι → Set M, (∀ i, IsOpen (U i)) → Set.univ ⊆ ⋃ i, U i →
      ∃ f : SmoothPartitionOfUnity ι (𝓡∂ n) M Set.univ, f.IsSubordinate U)
