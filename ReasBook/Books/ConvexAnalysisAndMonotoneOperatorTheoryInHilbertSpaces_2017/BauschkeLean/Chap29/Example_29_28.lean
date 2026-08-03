import BauschkeLean.Chap29.Example_29_28.ProbabilitySimplex
import BauschkeLean.Chap29.Proposition_29_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {N : ℕ}

local notation "C" => Set.lpClosedUnitBall N 1
local notation "Δₚ" => (probabilitySimplex : Set (EuclideanSpace ℝ (Fin N)))

section

variable (N) (hN : 0 < N)

local notation "P_C" => P[C, isChebyshev_lpClosedUnitBall_one N]
local notation "P_Δ" => P[Δₚ, isChebyshev_probabilitySimplex_fin N hN]

namespace probabilitySimplex

/-- Helper for Example 29.28: multiply each coordinate by a prescribed scalar. -/
private def coordinateSignMul (σ : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm fun i ↦ σ i * z i

/-- Helper for Example 29.28: `coordinateSignMul` acts coordinatewise. -/
@[simp] private theorem coordinateSignMul_apply
    (σ : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    coordinateSignMul (N := N) σ z i = σ i * z i := by
  simp [coordinateSignMul]

/-- Helper for Example 29.28: coordinatewise sign multiplication distributes over subtraction. -/
private theorem coordinateSignMul_sub
    (σ : Fin N → ℝ) (u v : EuclideanSpace ℝ (Fin N)) :
    coordinateSignMul (N := N) σ (u - v) =
      coordinateSignMul (N := N) σ u - coordinateSignMul (N := N) σ v := by
  -- Compare the two vectors coordinatewise.
  ext i
  simp [coordinateSignMul, sub_eq_add_neg, mul_add]

/-- Helper for Example 29.28: multiplying each coordinate by `±1` keeps a point inside the `ℓ¹`
unit ball. -/
private theorem coordinateSignMul_mem_lpClosedUnitBall
    {σ : Fin N → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∈ C) :
    coordinateSignMul (N := N) σ z ∈ C := by
  -- Coordinatewise signs preserve every absolute value in the `ℓ¹` norm.
  rw [Set.mem_lpClosedUnitBall_iff] at hz ⊢
  have hz_sum : ∑ i, |z i| ≤ 1 := by
    simpa [EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1] using hz
  rw [EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1]
  calc
    ∑ i, |coordinateSignMul (N := N) σ z i| = ∑ i, |σ i * z i| := by
      simp [coordinateSignMul]
    _ = ∑ i, |z i| := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases hσ i with hsi | hsi <;> simp [hsi]
    _ ≤ 1 := hz_sum

/-- Helper for Example 29.28: multiplying each coordinate by `±1` preserves the Euclidean norm. -/
private theorem coordinateSignMul_norm_eq
    {σ : Fin N → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (z : EuclideanSpace ℝ (Fin N)) :
    ‖coordinateSignMul (N := N) σ z‖ = ‖z‖ := by
  -- The Euclidean norm is the `ℓ²` norm of the coordinate tuple, and signs do not affect squares.
  calc
    ‖coordinateSignMul (N := N) σ z‖
        = √(∑ i, ‖coordinateSignMul (N := N) σ z i‖ ^ 2) := by
            simpa [Real.norm_eq_abs] using
              PiLp.norm_eq_of_L2
                (WithLp.toLp 2 ((EuclideanSpace.equiv (Fin N) ℝ)
                  (coordinateSignMul (N := N) σ z)))
    _ = √(∑ i, ‖z i‖ ^ 2) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rcases hσ i with hsi | hsi <;> simp [hsi]
    _ = ‖z‖ := by
          simpa [Real.norm_eq_abs] using
            (PiLp.norm_eq_of_L2 (WithLp.toLp 2 ((EuclideanSpace.equiv (Fin N) ℝ) z))).symm

/-- Helper for Example 29.28: multiplying each coordinate by `±1` preserves Euclidean distance. -/
private theorem coordinateSignMul_dist_eq
    {σ : Fin N → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (u v : EuclideanSpace ℝ (Fin N)) :
    dist (coordinateSignMul (N := N) σ u) (coordinateSignMul (N := N) σ v) = dist u v := by
  -- Rewrite the distance through the norm of the transformed difference.
  rw [dist_eq_norm, dist_eq_norm, ← coordinateSignMul_sub]
  simpa using coordinateSignMul_norm_eq (N := N) hσ (u - v)

/-- Helper for Example 29.28: the `l^1` unit ball contains the origin. -/
private theorem lpClosedUnitBall_one_nonempty :
    Set.Nonempty C := by
  -- The origin has `l^1` norm `0`, so it lies in the unit ball.
  refine ⟨0, by simp [Set.mem_lpClosedUnitBall_iff, EuclideanSpace.lpNorm]⟩

/-- Helper for Example 29.28: the `l^1` unit ball is closed. -/
private theorem lpClosedUnitBall_one_closed :
    IsClosed C := by
  -- View `l^1` as the usual norm after transporting to `PiLp`.
  let L :=
    ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
      (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  have hcont :
      Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[1]) := by
    simpa [EuclideanSpace.lpNorm, L] using
      (continuous_norm.comp L.continuous :
        Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖))
  simpa [Set.lpClosedUnitBall, Set.preimage, Set.setOf_mem_eq] using
    isClosed_Iic.preimage hcont

/-- Helper for Example 29.28: the `l^1` unit ball is convex. -/
private theorem lpClosedUnitBall_one_convex :
    Convex ℝ C := by
  -- The unit ball is a norm sublevel set.
  let L :=
    ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
      (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  have hnorm_conv :
      ConvexOn ℝ Set.univ (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[1]) := by
    simpa [EuclideanSpace.lpNorm, L] using
      (convexOn_univ_norm :
        ConvexOn ℝ Set.univ (fun z : PiLp 1 (fun _ : Fin N ↦ ℝ) ↦ ‖z‖)).comp_linearMap
        L.toLinearMap
  simpa [Set.lpClosedUnitBall, Set.setOf_mem_eq] using hnorm_conv.convex_le (1 : ℝ)

/-- Helper for Example 29.28: zeroing a coordinate keeps a point inside the `l^1` unit ball. -/
private theorem zeroCoordinate_mem_lpClosedUnitBall
    {ξ : EuclideanSpace ℝ (Fin N)} (hξ : ξ ∈ C) (i : Fin N) :
    ξ - EuclideanSpace.single i (ξ i) ∈ C := by
  -- Zeroing the `i`-th coordinate removes one nonnegative summand from the `ℓ¹` norm.
  rw [Set.mem_lpClosedUnitBall_iff] at hξ ⊢
  have hξ_sum : ∑ j, |ξ j| ≤ 1 := by
    simpa [EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1] using hξ
  rw [EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1]
  calc
    ∑ j, |(ξ - EuclideanSpace.single i (ξ i)) j|
        = Finset.sum (Finset.univ.erase i) (fun j ↦ |ξ j|) := by
            calc
              ∑ j, |(ξ - EuclideanSpace.single i (ξ i)) j|
                  = Finset.sum (Finset.univ.erase i)
                      (fun j ↦ |(ξ - EuclideanSpace.single i (ξ i)) j|) +
                      |(ξ - EuclideanSpace.single i (ξ i)) i| := by
                        symm
                        exact Finset.sum_erase_add (s := Finset.univ)
                          (f := fun j ↦ |(ξ - EuclideanSpace.single i (ξ i)) j|)
                          (a := i) (Finset.mem_univ i)
              _ = Finset.sum (Finset.univ.erase i)
                    (fun j ↦ |(ξ - EuclideanSpace.single i (ξ i)) j|) := by
                    simp
              _ = Finset.sum (Finset.univ.erase i) (fun j ↦ |ξ j|) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
                    simp [EuclideanSpace.single, hji]
    _ ≤ Finset.sum (Finset.univ.erase i) (fun j ↦ |ξ j|) + |ξ i| := by
          exact le_add_of_nonneg_right (abs_nonneg _)
    _ = ∑ j, |ξ j| := by
          exact Finset.sum_erase_add (s := Finset.univ) (f := fun j ↦ |ξ j|)
            (a := i) (Finset.mem_univ i)
    _ ≤ 1 := hξ_sum

/-- Helper for Example 29.28: on a coordinatewise nonnegative vector, the `ℓ¹` norm is the
coordinate sum. -/
private theorem lpNorm_one_eq_sum_of_nonneg
    {ξ : EuclideanSpace ℝ (Fin N)} (hξ : ∀ i, 0 ≤ ξ i) :
    ‖ξ‖_[1] = ∑ i, ξ i := by
  -- Every absolute value disappears once the coordinates are known to be nonnegative.
  rw [EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact abs_of_nonneg (hξ i)

/-- Helper for Example 29.28: coordinates that vanish in the nonnegative datum also vanish in the
`l^1`-ball projection. -/
private theorem projectionPoint_lpClosedUnitBall_apply_eq_zero_of_nonneg_of_eq_zero
    {y : EuclideanSpace ℝ (Fin N)} {i : Fin N} (hyi : y i = 0) :
    (P_C y) i = 0 := by
  -- Route correction: use the one-coordinate sign symmetry fixing `y`, rather than the stalled
  -- coordinate inequality chain.
  let σ : Fin N → ℝ := fun j ↦ if j = i then -1 else 1
  have hσ : ∀ j, σ j = 1 ∨ σ j = -1 := by
    intro j
    by_cases hji : j = i
    · right
      simp [σ, hji]
    · left
      simp [σ, hji]
  have hfix_y : coordinateSignMul (N := N) σ y = y := by
    -- The flipped coordinate is exactly the zero coordinate of `y`.
    ext j
    by_cases hji : j = i
    · subst hji
      simp [σ, hyi]
    · simp [σ, hji]
  have hflip_mem : coordinateSignMul (N := N) σ (P_C y) ∈ C := by
    -- The `ℓ¹` ball is invariant under coordinatewise sign changes.
    exact coordinateSignMul_mem_lpClosedUnitBall (N := N) hσ (projectionPoint_mem C
      (isChebyshev_lpClosedUnitBall_one N) y)
  have hflip_best : IsBestApproximation y C (coordinateSignMul (N := N) σ (P_C y)) := by
    -- The flipped point has the same distance to `y`, so uniqueness forces it to be the
    -- projection itself.
    refine ⟨hflip_mem, ?_⟩
    calc
      dist y (coordinateSignMul (N := N) σ (P_C y))
          = dist (coordinateSignMul (N := N) σ y)
              (coordinateSignMul (N := N) σ (P_C y)) := by
              rw [hfix_y]
      _ = dist y (P_C y) := coordinateSignMul_dist_eq (N := N) hσ y (P_C y)
      _ = Metric.infDist y C := (projectionPoint_isBestApproximation C
            (isChebyshev_lpClosedUnitBall_one N) y).2
  have hflip_eq :
      coordinateSignMul (N := N) σ (P_C y) = P_C y := by
    exact eq_projectionPoint_of_isBestApproximation C
      (isChebyshev_lpClosedUnitBall_one N) hflip_best
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin N) ↦ z i) hflip_eq
  have hσi : σ i = -1 := by simp [σ]
  have hcoord' : -(P_C y) i = (P_C y) i := by
    simpa [coordinateSignMul_apply, hσi] using hcoord
  linarith

/-- Helper for Example 29.28: the projection of a nonnegative vector onto the `ℓ¹` unit ball has
nonnegative coordinates and preserves zero coordinates. -/
private theorem projectionPoint_lpClosedUnitBall_coordinateFacts_of_nonneg
    {y : EuclideanSpace ℝ (Fin N)} (hy : ∀ i, 0 ≤ y i) :
    (∀ i, 0 ≤ (P_C y) i) ∧ ∀ {i}, y i = 0 → (P_C y) i = 0 := by
  constructor
  · intro i
    by_cases hyi : y i = 0
    · -- Zero coordinates stay zero by the sign-symmetry argument above.
      have hzero :=
        projectionPoint_lpClosedUnitBall_apply_eq_zero_of_nonneg_of_eq_zero
          (N := N) hyi
      simp [hzero]
    · have hyi_pos : 0 < y i := lt_of_le_of_ne (hy i) (by
        intro h0
        exact hyi h0.symm)
      have hmul :
          0 ≤ y i * (P_C y) i := by
        simpa using
          mul_projectionPoint_nonneg_of_zeroCoordinate_mem_of_nonempty_isClosed_convex
            (hC_nonempty := lpClosedUnitBall_one_nonempty (N := N))
            (hC_closed := lpClosedUnitBall_one_closed (N := N))
            (hC_convex := lpClosedUnitBall_one_convex (N := N))
            (hzero := fun ξ hξ j ↦ zeroCoordinate_mem_lpClosedUnitBall (N := N) hξ j)
            (x := y) (i := i)
      nlinarith [hmul]
  · intro i hi
    exact projectionPoint_lpClosedUnitBall_apply_eq_zero_of_nonneg_of_eq_zero
      (N := N) hi

/-- Helper for Example 29.28: the projection of a nonnegative vector onto the `l^1` unit ball
remains coordinatewise nonnegative. -/
private theorem projectionPoint_lpClosedUnitBall_nonneg_of_nonneg
    {y : EuclideanSpace ℝ (Fin N)} (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ (P_C y) i := by
  -- Reuse the combined coordinate package and keep only its nonnegativity component.
  exact (projectionPoint_lpClosedUnitBall_coordinateFacts_of_nonneg (N := N) hy).1

/-- Helper for Example 29.28: if a nonnegative point lies outside the `l^1` unit ball, then its
projection lies on the boundary `||p||_[1] = 1`. -/
private theorem projectionPoint_lpClosedUnitBall_boundary_of_nonneg_of_not_mem
    {y : EuclideanSpace ℝ (Fin N)} (hy : ∀ i, 0 ≤ y i) (hy_out : y ∉ C) :
    ‖P_C y‖_[1] = 1 := by
  let p := P_C y
  have hp_mem : p ∈ C := by
    exact projectionPoint_mem C (isChebyshev_lpClosedUnitBall_one N) y
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    simpa [p] using (projectionPoint_lpClosedUnitBall_coordinateFacts_of_nonneg (N := N) hy).1
  have hy_sum_gt : 1 < ∑ i, y i := by
    have hy_ball_false : ¬ ∑ i, y i ≤ 1 := by
      intro hy_sum_le
      apply hy_out
      rw [Set.mem_lpClosedUnitBall_iff, lpNorm_one_eq_sum_of_nonneg (N := N) hy]
      exact hy_sum_le
    linarith
  have hp_sum_le : ∑ i, p i ≤ 1 := by
    have hp_ball : ‖p‖_[1] ≤ 1 := by
      simpa [Set.mem_lpClosedUnitBall_iff] using hp_mem
    rw [lpNorm_one_eq_sum_of_nonneg (N := N) hp_nonneg] at hp_ball
    exact hp_ball
  by_cases hp_sum : ∑ i, p i = 1
  · -- Once the projected point is nonnegative, the `ℓ¹` norm is exactly the coordinate sum.
    rw [lpNorm_one_eq_sum_of_nonneg (N := N) hp_nonneg]
    simpa [p] using hp_sum
  · have hp_sum_lt : ∑ i, p i < 1 := lt_of_le_of_ne hp_sum_le hp_sum
    have hdenom_pos : 0 < ∑ i, y i - ∑ i, p i := by
      linarith
    let α : ℝ := (1 - ∑ i, p i) / (∑ i, y i - ∑ i, p i)
    have hα_pos : 0 < α := by
      dsimp [α]
      exact div_pos (sub_pos.mpr hp_sum_lt) hdenom_pos
    have hα_lt_one : α < 1 := by
      dsimp [α]
      have hnum_lt_denom : 1 - ∑ i, p i < ∑ i, y i - ∑ i, p i := by
        linarith
      exact (div_lt_one hdenom_pos).2 hnum_lt_denom
    let q : EuclideanSpace ℝ (Fin N) := AffineMap.lineMap p y α
    have hq_nonneg : ∀ i, 0 ≤ q i := by
      -- The convex combination stays in the positive orthant.
      intro i
      dsimp [q]
      rw [AffineMap.lineMap_apply_module]
      simp [smul_eq_mul]
      nlinarith [hp_nonneg i, hy i, hα_pos.le, hα_lt_one.le]
    have hq_sum : ∑ i, q i = 1 := by
      -- Choose the segment parameter so that the coordinate sum reaches exactly the boundary value.
      have hline :
          ∑ i, q i = (1 - α) * ∑ i, p i + α * ∑ i, y i := by
        dsimp [q]
        rw [AffineMap.lineMap_apply_module]
        simp [smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_comm,
          sub_eq_add_neg, add_comm]
      have hsum_eval : (1 - α) * ∑ i, p i + α * ∑ i, y i = 1 := by
        dsimp [α]
        field_simp [hdenom_pos.ne']
        ring
      exact hline.trans hsum_eval
    have hq_mem : q ∈ C := by
      rw [Set.mem_lpClosedUnitBall_iff, lpNorm_one_eq_sum_of_nonneg (N := N) hq_nonneg]
      simp [hq_sum]
    have hp_ne_y : p ≠ y := by
      intro hpy
      apply hy_out
      simpa [p] using hpy ▸ hp_mem
    have hq_closer : dist y q < dist y p := by
      -- Any nontrivial point on the segment from `p` to `y` is strictly closer to `y` than `p` is.
      have hp_dist_pos : 0 < dist y p := by
        exact dist_pos.mpr hp_ne_y.symm
      calc
        dist y q = ‖1 - α‖ * dist p y := by
          dsimp [q]
          exact dist_right_lineMap p y α
        _ = (1 - α) * dist y p := by
          rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hα_lt_one), dist_comm]
        _ < 1 * dist y p := by
          exact mul_lt_mul_of_pos_right (sub_lt_self 1 hα_pos) hp_dist_pos
        _ = dist y p := by ring
    have hq_lt_inf : dist y q < Metric.infDist y C := by
      simpa [p] using hq_closer.trans_eq (projectionPoint_isBestApproximation C
        (isChebyshev_lpClosedUnitBall_one N) y).2
    exact (not_lt_of_ge (Metric.infDist_le_dist_of_mem hq_mem) hq_lt_inf).elim

/-- Helper for Example 29.28: every point of the probability simplex belongs to the `l^1`
unit ball. -/
private theorem probabilitySimplex_subset_lpClosedUnitBall
    {ξ : EuclideanSpace ℝ (Fin N)} (hξ : ξ ∈ Δₚ) :
    ξ ∈ C := by
  rcases mem_probabilitySimplex.mp hξ with ⟨hξ_nonneg, hξ_sum⟩
  -- On the simplex the `l^1` norm is exactly the coordinate sum.
  rw [Set.mem_lpClosedUnitBall_iff, EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1]
  calc
    ∑ i, |ξ i| = ∑ i, ξ i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact abs_of_nonneg (hξ_nonneg i)
    _ = 1 := hξ_sum
    _ ≤ 1 := le_rfl

/-- Helper for Example 29.28: for a nonnegative point outside the `l^1` unit ball, the
`l^1`-ball projection already lies in the source probability simplex. -/
private theorem projectionPoint_lpClosedUnitBall_mem_probabilitySimplex_of_nonneg_of_not_mem
    {y : EuclideanSpace ℝ (Fin N)} (hy : ∀ i, 0 ≤ y i) (hy_out : y ∉ C) :
    P_C y ∈ Δₚ := by
  have hp_nonneg : ∀ i, 0 ≤ (P_C y) i :=
    projectionPoint_lpClosedUnitBall_nonneg_of_nonneg (N := N) hy
  have hp_boundary :
      ‖P_C y‖_[1] = 1 :=
    projectionPoint_lpClosedUnitBall_boundary_of_nonneg_of_not_mem (N := N) hy hy_out
  -- The boundary identity turns into the simplex mass identity because every projected coordinate
  -- is nonnegative.
  refine mem_probabilitySimplex.mpr ⟨hp_nonneg, ?_⟩
  rw [lpNorm_one_eq_sum_of_nonneg (N := N) hp_nonneg] at hp_boundary
  exact hp_boundary

/-- Helper for Example 29.28: on a nonnegative point outside the `l^1` unit ball, the
`l^1`-ball projector agrees with the simplex projector. -/
private theorem
    projectionPoint_lpClosedUnitBall_eq_projectionPoint_probabilitySimplex_of_nonneg_of_not_mem
    {y : EuclideanSpace ℝ (Fin N)} (hy : ∀ i, 0 ≤ y i) (hy_out : y ∉ C) :
    P_C y = P_Δ y := by
  have hp_memΔ : P_C y ∈ Δₚ :=
    projectionPoint_lpClosedUnitBall_mem_probabilitySimplex_of_nonneg_of_not_mem
      (N := N) hy hy_out
  have hp_best_on_simplex : IsBestApproximation y Δₚ (P_C y) := by
    refine ⟨hp_memΔ, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hp_memΔ)⟩
    rw [Metric.le_infDist ⟨P_C y, hp_memΔ⟩]
    intro z hz
    calc
      dist y (P_C y) = Metric.infDist y C := (projectionPoint_isBestApproximation C
        (isChebyshev_lpClosedUnitBall_one N) y).2
      _ ≤ dist y z := Metric.infDist_le_dist_of_mem (probabilitySimplex_subset_lpClosedUnitBall
        (N := N) hz)
  exact eq_projectionPoint_of_isBestApproximation Δₚ
    (isChebyshev_probabilitySimplex_fin N hN) hp_best_on_simplex

/-- Example 29.28 (ℓ¹ unit ball): if `x` lies outside the `ℓ¹` unit ball
`C = Set.lpClosedUnitBall N 1`, then its metric projection onto `C` is obtained by projecting the
coordinatewise absolute-value vector onto the source probability simplex
`Δ = {ξ ∈ EuclideanSpace ℝ (Fin N) | (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = 1}` and then restoring the signs
coordinatewise. -/
theorem proj_lpClosedUnitBall_eq_sign_mul_proj_abs {x : EuclideanSpace ℝ (Fin N)} (hx : x ∉ C) :
    P_C x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i ↦
          Real.sign (x i) *
            P_Δ ((EuclideanSpace.equiv (Fin N) ℝ).symm fun j ↦ |x j|) i) := by
  -- Route correction: first identify the positive projection `P_C |x| = P_Δ |x|`, then transport
  -- it back to `x` through the coordinatewise `±1` action.
  let y : EuclideanSpace ℝ (Fin N) :=
    (EuclideanSpace.equiv (Fin N) ℝ).symm fun j ↦ |x j|
  let σ : Fin N → ℝ := fun i ↦ if x i < 0 then -1 else 1
  let p : EuclideanSpace ℝ (Fin N) := P_Δ y
  let q : EuclideanSpace ℝ (Fin N) := coordinateSignMul (N := N) σ p
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := by
    intro i
    by_cases hxi : x i < 0
    · right
      simp [σ, hxi]
    · left
      simp [σ, hxi]
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    simp [y]
  have hy_out : y ∉ C := by
    -- Replacing each coordinate by its absolute value keeps the `ℓ¹` norm unchanged.
    intro hy_mem
    apply hx
    rw [Set.mem_lpClosedUnitBall_iff, EuclideanSpace.lpNorm_apply, PiLp.norm_eq_of_L1]
    have hy_sum : ∑ i, y i ≤ 1 := by
      have hy_ball : ‖y‖_[1] ≤ 1 := by
        simpa [Set.mem_lpClosedUnitBall_iff] using hy_mem
      rw [lpNorm_one_eq_sum_of_nonneg (N := N) hy_nonneg] at hy_ball
      exact hy_ball
    simpa [y] using hy_sum
  have hp_pos :
      P_C y = p := by
    simpa [p, y] using
      projectionPoint_lpClosedUnitBall_eq_projectionPoint_probabilitySimplex_of_nonneg_of_not_mem
        (N := N) (hN := hN) hy_nonneg hy_out
  have hp_memΔ : p ∈ Δₚ := by
    dsimp [p]
    exact projectionPoint_mem Δₚ (isChebyshev_probabilitySimplex_fin N hN) y
  have hp_memC : p ∈ C := probabilitySimplex_subset_lpClosedUnitBall (N := N) hp_memΔ
  have hs_y : coordinateSignMul (N := N) σ y = x := by
    -- The chosen signs recover the original coordinates from their absolute values.
    ext i
    by_cases hxi : x i < 0
    · simp [coordinateSignMul, σ, y, hxi, abs_of_neg hxi]
    · simp [coordinateSignMul, σ, y, hxi, abs_of_nonneg (le_of_not_gt hxi)]
  have hs_x : coordinateSignMul (N := N) σ x = y := by
    -- Applying the same coordinatewise signs twice returns to the absolute-value vector.
    ext i
    by_cases hxi : x i < 0
    · simp [coordinateSignMul, σ, y, hxi, abs_of_neg hxi]
    · simp [coordinateSignMul, σ, y, hxi, abs_of_nonneg (le_of_not_gt hxi)]
  have hq_mem : q ∈ C := by
    simpa [q] using coordinateSignMul_mem_lpClosedUnitBall (N := N) hσ hp_memC
  have hp_bestC : IsBestApproximation y C p := by
    simpa [p, hp_pos] using projectionPoint_isBestApproximation C
      (isChebyshev_lpClosedUnitBall_one N) y
  have hq_best : IsBestApproximation x C q := by
    refine ⟨hq_mem, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hq_mem)⟩
    rw [Metric.le_infDist ⟨q, hq_mem⟩]
    intro w hw
    calc
      dist x q = dist y p := by
        simpa [q, hs_y] using coordinateSignMul_dist_eq (N := N) hσ y p
      _ = Metric.infDist y C := hp_bestC.2
      _ ≤ dist y (coordinateSignMul (N := N) σ w) := by
        exact Metric.infDist_le_dist_of_mem
          (coordinateSignMul_mem_lpClosedUnitBall (N := N) hσ hw)
      _ = dist x w := by
        simpa [hs_x] using coordinateSignMul_dist_eq (N := N) hσ x w
  have hproj_eq : P_C x = q := by
    symm
    exact eq_projectionPoint_of_isBestApproximation C
      (isChebyshev_lpClosedUnitBall_one N) hq_best
  have hp_zero :
      ∀ {i : Fin N}, x i = 0 → p i = 0 := by
    intro i hxi
    have hpc_zero :
        (P_C y) i = 0 := by
      exact
        (projectionPoint_lpClosedUnitBall_coordinateFacts_of_nonneg (N := N) hy_nonneg).2
        (by simp [y, hxi])
    simpa [p, hp_pos] using hpc_zero
  -- Replace the auxiliary sign action by the source coordinate formula involving `Real.sign`.
  ext i
  have hqi : q i = σ i * p i := by
    simp [q]
  rw [hproj_eq, hqi]
  by_cases hneg : x i < 0
  · simp [p, y, σ, hneg, Real.sign_of_neg hneg]
  · by_cases hzero : x i = 0
    · have hpi_zero : p i = 0 := hp_zero hzero
      simpa [p, y, σ, hzero] using hpi_zero
    · have hpos : 0 < x i := lt_of_le_of_ne (le_of_not_gt hneg) (by
          intro h0
          exact hzero h0.symm)
      simp [p, y, σ, hneg, Real.sign_of_pos hpos]

/-- Coordinatewise form of Example 29.28. -/
theorem proj_lpClosedUnitBall_eq_sign_mul_proj_abs_apply {x : EuclideanSpace ℝ (Fin N)}
    (hx : x ∉ C) (i : Fin N) :
    P_C x i =
      Real.sign (x i) * P_Δ ((EuclideanSpace.equiv (Fin N) ℝ).symm fun j ↦ |x j|) i := by
  -- Evaluate the vector identity from Example 29.28 at the coordinate `i`.
  simpa using congrArg (fun z : EuclideanSpace ℝ (Fin N) ↦ z i)
    (proj_lpClosedUnitBall_eq_sign_mul_proj_abs (N := N) (hN := hN) hx)

end probabilitySimplex

end

end
