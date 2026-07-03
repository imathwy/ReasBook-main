import Mathlib
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_11 (from Chap03/Sec03_14) -/
open scoped Manifold

/-- Lemma 3.11: for any boundary point `a` of `ℍ^n`, the differential of the inclusion
`Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)` at `a` is an isomorphism. -/
theorem mfderiv_half_space_inclusion_isInvertible_of_boundary_eq_zero
    (n : ℕ) [NeZero n] (a : EuclideanHalfSpace n)
    (ha : a.1 0 = 0) :
    (mfderiv (𝓡∂ n) (𝓡 n)
      (fun x : EuclideanHalfSpace n ↦ x.1) a).IsInvertible := sorry
