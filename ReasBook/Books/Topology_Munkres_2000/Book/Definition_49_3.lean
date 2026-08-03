module

public import Topology_Munkres_2000.Book.Definition_49_3.PiecewiseLinear

public section

open Set

namespace UnitIntervalPiecewiseLinear

/-- Definition 49.3: A function admitting a finite broken-line presentation is continuous. -/
theorem IsPiecewiseLinear.continuous {g : Icc (0 : ℝ) 1 → ℝ}
    (hg : IsPiecewiseLinear g) : Continuous g := by
  -- Expose the finite broken-line certificate and paste its affine pieces.
  rw [isPiecewiseLinear_iff] at hg
  rcases hg with ⟨k, knots, slopes, hknots, hzero, hone, hlinear⟩
  let segments : Fin (k + 1) → Set (Icc (0 : ℝ) 1) :=
    fun i ↦ Icc (knots i.castSucc) (knots i.succ)
  refine (locallyFinite_of_finite segments).continuous ?_ ?_ ?_
  · -- Adjacent knot intervals cover the complete unit interval.
    exact iUnion_adjacentIcc_eq_univ k knots hknots.monotone hzero hone
  · -- Each segment is closed in the unit-interval subtype.
    intro i
    exact isClosed_Icc
  · -- On every segment the certificate identifies `g` with an affine map.
    intro i
    exact continuousOn_of_eq_affine fun t ht ↦ hlinear i t ht.1 ht.2

/-- A steep piecewise-linear function is continuous. -/
theorem IsSteep.continuous {g : Icc (0 : ℝ) 1 → ℝ} {α : ℝ}
    (hg : IsSteep g α) : Continuous g :=
  hg.isPiecewiseLinear.continuous


end UnitIntervalPiecewiseLinear
