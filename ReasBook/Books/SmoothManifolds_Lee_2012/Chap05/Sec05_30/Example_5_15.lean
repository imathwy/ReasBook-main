import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Example_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

section

variable (n : ℕ)

/- Example 5.15 is a bridge/view item, not a new owner: the source-facing owner for the unit
sphere as an embedded submanifold was already established in Example 5.9, and the smooth-embedding
formulation is the canonical projection `IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val`. -/
recall unitSphere_isEmbeddedSubmanifold (n : ℕ) :
    IsEmbeddedSubmanifold
      (𝓡 (n + 1))
      (𝓡 n)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/- Example 5.15, in smooth-embedding language, is exactly the subtype-inclusion projection
furnished by the embedded-submanifold owner above. -/
#check (unitSphere_isEmbeddedSubmanifold n).isSmoothEmbedding_subtype_val

end
