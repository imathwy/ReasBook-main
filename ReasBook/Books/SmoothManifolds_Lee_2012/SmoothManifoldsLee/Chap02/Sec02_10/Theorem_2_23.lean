import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uι uM

-- Domain sampling pass: this item lies in the smooth-manifold/partition-of-unity domain. The
-- core/canonical owner is mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, and the
-- canonical subordinate predicate is `SmoothPartitionOfUnity.IsSubordinate`. This `Ch2` facade
-- keeps only the two textbook `s = Set.univ` specializations and uses the owner declaration
-- directly, rather than routing through a chapter-level bridge theorem.

variable {ι : Type uι}

variable {n : ℕ} {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

/- Theorem 2.23 (1): on a smooth manifold without boundary, every indexed open cover admits a
smooth partition of unity subordinate to it. -/
#check
  (SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n) isClosed_univ :
    ∀ U : ι → Set M, (∀ i, IsOpen (U i)) → Set.univ ⊆ ⋃ i, U i →
      ∃ f : SmoothPartitionOfUnity ι (𝓡 n) M Set.univ, f.IsSubordinate U)

variable {n : ℕ} [NeZero n] {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

/- Theorem 2.23 (2): on a smooth manifold with boundary, every indexed open cover admits a smooth
partition of unity subordinate to it. -/
#check
  (SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ n) isClosed_univ :
    ∀ U : ι → Set M, (∀ i, IsOpen (U i)) → Set.univ ⊆ ⋃ i, U i →
      ∃ f : SmoothPartitionOfUnity ι (𝓡∂ n) M Set.univ, f.IsSubordinate U)
