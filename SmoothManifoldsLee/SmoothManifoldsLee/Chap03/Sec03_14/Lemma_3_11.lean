import Mathlib
import Mathlib.Geometry.Manifold.Instances.Real

-- Semantic search tool unavailable in this environment; local recall used mathlib's
-- `ModelWithCorners.hasMFDerivAt` and the repository precedent in `Chap04/Sec04_27/Problem_4_1`.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

/-- Lemma 3.11: for any boundary point `a` of `ℍ^n`, the differential of the inclusion
`Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)` at `a` is an isomorphism. -/
theorem mfderiv_half_space_inclusion_isInvertible_of_boundary_eq_zero
    (n : ℕ) [NeZero n] (a : EuclideanHalfSpace n)
    (ha : a.1 0 = 0) :
    (mfderiv (𝓡∂ n) (𝓡 n)
      (fun x : EuclideanHalfSpace n ↦ x.1) a).IsInvertible := sorry
