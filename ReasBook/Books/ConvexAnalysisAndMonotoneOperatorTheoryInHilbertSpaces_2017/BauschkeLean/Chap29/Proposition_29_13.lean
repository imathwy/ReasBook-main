import BauschkeLean.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

section

variable {N : ℕ}
variable {C : Set (EuclideanSpace ℝ (Fin N))}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

/-- Proposition 29.13: let `C` be a nonempty closed convex subset of `ℝ^N` such that, for every
`ξ ∈ C` and every coordinate `i`, the vector obtained from `ξ` by replacing its `i`-th coordinate
by `0` still belongs to `C`. Then each coordinate of the metric projection `P[C, hC_cheb]`
has nonnegative product with the corresponding coordinate of the original point. -/
theorem mul_projectionPoint_nonneg_of_zeroCoordinate_mem_of_nonempty_isClosed_convex
    (hzero : ∀ ξ ∈ C, ∀ i : Fin N,
      ξ - EuclideanSpace.single i (ξ i) ∈ C)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    0 ≤ x i * (P_C x) i := by
  set p := P_C x with hp
  -- The source proof compares the projection point with the competitor obtained by
  -- zeroing its `i`-th coordinate.
  have hp_mem : p ∈ C := by
    rw [hp]
    exact projectionPoint_mem C hC_cheb x
  -- The projection characterization gives the variational inequality against every
  -- competitor in `C`.
  have hp_nonpos :
      ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
    rw [hp]
    exact
      ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl).2
  -- Apply that inequality to the point obtained by replacing the `i`-th coordinate
  -- of `p` with `0`.
  have hzero_inner :
      ⟪p - EuclideanSpace.single i (p i) - p, x - p⟫_ℝ ≤ 0 :=
    hp_nonpos _ (hzero _ hp_mem i)
  -- Only the `i`-th coordinate survives in the inner product with the zeroed vector.
  have hcoord :
      ⟪p - EuclideanSpace.single i (p i) - p, x - p⟫_ℝ =
        -(p i * (x i - p i)) := by
    calc
      ⟪p - EuclideanSpace.single i (p i) - p, x - p⟫_ℝ
          = ⟪-EuclideanSpace.single i (p i), x - p⟫_ℝ := by
              congr 1
              abel
      _ = -⟪EuclideanSpace.single i (p i), x - p⟫_ℝ := by
        rw [inner_neg_left]
      _ = -(p i * (x i - p i)) := by
        simpa using congrArg Neg.neg
          (EuclideanSpace.inner_single_left i (p i) (x - p))
  -- Rearranging the variational inequality yields the desired sign condition.
  have hmul_sub_nonneg : 0 ≤ (p i) * (x i - p i) := by
    rw [hcoord] at hzero_inner
    exact neg_nonpos.mp hzero_inner
  calc
    0 ≤ (p i) * (x i - p i) + (p i) ^ 2 := add_nonneg hmul_sub_nonneg (sq_nonneg _)
    _ = x i * p i := by
      ring

end
