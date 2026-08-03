import Mathlib
import BauschkeLean.Chap02.Example_2_32_1
import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap04.Text_4_21_1
import BauschkeLean.Chap20.Example_20_30

open Filter
open scoped InnerProductSpace Topology

local notation "L2" => ℓ²(ℕ, ℝ)

namespace Function

local notation "C" => Metric.closedBall (0 : L2) 1

private theorem closedUnitBall_nonempty :
    (Metric.closedBall (0 : L2) 1 : Set L2).Nonempty :=
  Metric.nonempty_closedBall.2 zero_le_one

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex
    closedUnitBall_nonempty
    (Metric.isClosed_closedBall : IsClosed C)
    (convex_closedBall (0 : L2) 1)

/-- The residual map `Id - P_C` for the closed unit ball `C` of `ℓ²(ℕ, ℝ)`. -/
noncomputable def l2ClosedUnitBallResidualMap : L2 → L2 :=
  id - P[C, hC]

local notation "W" => Prod.map (toWeakSpace ℝ L2) (toWeakSpace ℝ L2)

-- The standard unit vector `e_n` in `ℓ²(ℕ, ℝ)`.
private noncomputable def l2BasisVector (n : ℕ) : L2 :=
  lp.single 2 n 1

-- The 0-indexed Lean version of the textbook witness sequence `e_1 + e_{2n}`.
private noncomputable def l2CounterexampleSequence : ℕ → L2 :=
  fun n ↦ l2BasisVector 1 + l2BasisVector (2 * n + 2)

-- The weak limit of the witness sequence.
private noncomputable def l2CounterexampleLimit : L2 :=
  l2BasisVector 1

-- Proof sketch: the metric projection onto a nonempty closed convex set is firmly nonexpansive;
-- for the closed unit ball this makes the residual map `1 / 2`-averaged, so Example 20.30 gives
-- maximal monotonicity of the associated singleton-valued operator.
private theorem l2ClosedUnitBallResidualMap_isMaximallyMonotone :
    Maximal SetValuedOperator.IsMonotone l2ClosedUnitBallResidualMap.toSetValuedOperator := by
  have hproj :
      FirmlyNonexpansive (P[C, hC] : L2 → L2) :=
    firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex
      closedUnitBall_nonempty
      (Metric.isClosed_closedBall : IsClosed C)
      (convex_closedBall (0 : L2) 1)
  have hproj_on :
      FirmlyNonexpansiveOn (Set.univ : Set L2) (fun x : Set.univ ↦ P[C, hC] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using hproj
  have hresidual :
      FirmlyNonexpansive l2ClosedUnitBallResidualMap := by
    simpa [l2ClosedUnitBallResidualMap, residualMap,
      firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      (firmlyNonexpansiveOn_residualMap_iff (Set.univ : Set L2)
        (fun x : Set.univ ↦ P[C, hC] x)).2 hproj_on
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_averaged_le_half
    ((firmlyNonexpansive_iff_averaged_half).mp hresidual) le_rfl

/-- Helper for Example 20.39: the standard `ℓ²(ℕ, ℝ)` basis is orthonormal. -/
private theorem l2BasisVector_orthonormal :
    Orthonormal ℝ l2BasisVector := by
  -- Reduce orthonormality to the coordinate formula for `lp.single`.
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [l2BasisVector]
  · simp [l2BasisVector, lp.inner_single_left, hij]

/-- Helper for Example 20.39: outside the closed unit ball, projection rescales a vector to norm
`1` along the same ray. -/
private theorem projectionPoint_closedUnitBall_eq_inv_norm_smul_of_one_lt_norm {x : L2}
    (hx : 1 < ‖x‖) :
    P[C, hC] x = ‖x‖⁻¹ • x := by
  have hnormx_pos : 0 < ‖x‖ := lt_trans zero_lt_one hx
  have hnormx : ‖x‖ ≠ 0 := hnormx_pos.ne'
  have hp_inner : inner ℝ (‖x‖⁻¹ • x) x = ‖x‖ := by
    -- Expand the inner product after radial rescaling and simplify the scalar factor.
    calc
      inner ℝ (‖x‖⁻¹ • x) x = ‖x‖⁻¹ * inner ℝ x x := by
        rw [real_inner_smul_left]
      _ = ‖x‖⁻¹ * ‖x‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      _ = ‖x‖ := by
        rw [pow_two]
        ring_nf
        field_simp [hnormx]
  have hproj :
      ‖x‖⁻¹ • x = P[C, hC] x := by
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        closedUnitBall_nonempty
        (Metric.isClosed_closedBall : IsClosed C)
        (convex_closedBall (0 : L2) 1)).mpr ?_
    refine ⟨?_, ?_⟩
    · have hp_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
        calc
          ‖‖x‖⁻¹ • x‖ = |‖x‖⁻¹| * ‖x‖ := norm_smul _ _
          _ = ‖x‖⁻¹ * ‖x‖ := by
            rw [abs_of_pos (inv_pos.mpr hnormx_pos)]
          _ = 1 := by
            rw [inv_mul_cancel₀ hnormx]
      -- The rescaled point lies on the unit sphere, hence in the closed unit ball.
      simpa [Metric.mem_closedBall, dist_eq_norm, hp_norm]
    · intro y hy
      have hy_norm : ‖y‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      have hy_inner : inner ℝ y x ≤ ‖x‖ := by
        calc
          inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
          _ ≤ 1 * ‖x‖ := by gcongr
          _ = ‖x‖ := by ring
      have hcoef_nonneg : 0 ≤ 1 - ‖x‖⁻¹ := by
        have hinv_lt : ‖x‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
        linarith
      -- The projection characterization reduces the inequality to the Cauchy bound above.
      calc
        inner ℝ (y - ‖x‖⁻¹ • x) (x - ‖x‖⁻¹ • x)
            = (1 - ‖x‖⁻¹) * inner ℝ (y - ‖x‖⁻¹ • x) x := by
                rw [show x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x by
                  calc
                    x - ‖x‖⁻¹ • x = (1 : ℝ) • x - ‖x‖⁻¹ • x := by
                      rw [one_smul]
                    _ = (1 - ‖x‖⁻¹) • x := by
                      rw [sub_smul], real_inner_smul_right]
        _ ≤ 0 := by
          refine mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ?_
          calc
            inner ℝ (y - ‖x‖⁻¹ • x) x = inner ℝ y x - inner ℝ (‖x‖⁻¹ • x) x := by
              rw [inner_sub_left]
            _ ≤ 0 := by
              linarith [hy_inner, hp_inner]
  simpa using hproj.symm

/-- Helper for Example 20.39: every witness vector has norm `√2`. -/
private theorem l2CounterexampleSequence_norm_eq_sqrt_two (n : ℕ) :
    ‖l2CounterexampleSequence n‖ = Real.sqrt 2 := by
  have hneq : 1 ≠ 2 * n + 2 := by
    omega
  have hsq : ‖l2CounterexampleSequence n‖ ^ 2 = 2 := by
    -- Orthogonality of the two basis vectors makes the cross term vanish.
    rw [l2CounterexampleSequence, norm_add_sq_real]
    have h1 : ‖l2BasisVector 1‖ = 1 := l2BasisVector_orthonormal.norm_eq_one 1
    have h2 : ‖l2BasisVector (2 * n + 2)‖ = 1 :=
      l2BasisVector_orthonormal.norm_eq_one (2 * n + 2)
    have hinner : inner ℝ (l2BasisVector 1) (l2BasisVector (2 * n + 2)) = 0 :=
      l2BasisVector_orthonormal.inner_eq_zero hneq
    nlinarith
  have hsqrt := congrArg Real.sqrt hsq
  have hnorm_nonneg : 0 ≤ ‖l2CounterexampleSequence n‖ := norm_nonneg _
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_nonneg] using hsqrt

-- Proof sketch: every term of the witness sequence has norm `√2`, so projection onto the closed
-- unit ball rescales it by `1 / √2`; subtracting the projection gives the factor
-- `(1 - 1 / √2)`. This identifies the displayed pairs as graph points.
private theorem l2ClosedUnitBallResidualMap_witness_mem_graph (n : ℕ) :
    (l2CounterexampleSequence n,
      (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n) ∈
        l2ClosedUnitBallResidualMap.toSetValuedOperator.graph := by
  have hnorm : ‖l2CounterexampleSequence n‖ = Real.sqrt 2 :=
    l2CounterexampleSequence_norm_eq_sqrt_two n
  have hnorm_gt_one : 1 < ‖l2CounterexampleSequence n‖ := by
    simpa [hnorm] using Real.one_lt_sqrt_two
  have hproj :
      P[C, hC] (l2CounterexampleSequence n) =
        (1 / Real.sqrt 2 : ℝ) • l2CounterexampleSequence n := by
    -- The fixed norm `√2` turns the radial projector formula into a constant scalar factor.
    calc
      P[C, hC] (l2CounterexampleSequence n)
          = ‖l2CounterexampleSequence n‖⁻¹ • l2CounterexampleSequence n :=
        projectionPoint_closedUnitBall_eq_inv_norm_smul_of_one_lt_norm hnorm_gt_one
      _ = (1 / Real.sqrt 2 : ℝ) • l2CounterexampleSequence n := by
        simp [hnorm, one_div]
  -- Unfold the singleton-valued graph and rewrite the residual explicitly.
  rw [SetValuedOperator.mem_graph, Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  have hresidual :
      l2ClosedUnitBallResidualMap (l2CounterexampleSequence n) =
        (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n := by
    calc
      l2ClosedUnitBallResidualMap (l2CounterexampleSequence n)
          = l2CounterexampleSequence n - P[C, hC] (l2CounterexampleSequence n) := by
            simp [l2ClosedUnitBallResidualMap]
      _ = l2CounterexampleSequence n -
            (1 / Real.sqrt 2 : ℝ) • l2CounterexampleSequence n := by
            rw [hproj]
      _ = (1 - 1 / Real.sqrt 2 : ℝ) • l2CounterexampleSequence n := by
            simpa [one_smul] using
              (sub_smul (1 : ℝ) (1 / Real.sqrt 2 : ℝ) (l2CounterexampleSequence n)).symm
  simpa using hresidual.symm

-- Proof sketch: the shifted even-coordinate basis tail is orthonormal and hence weakly null;
-- adding `e_1` yields weak convergence of `x_n` to `e_1`, and scalar multiplication preserves weak
-- convergence of the second coordinate. Therefore the graph-point sequence converges in the
-- product weak topology.
private theorem l2ClosedUnitBallResidualMap_witness_tendsto_weakly :
    Tendsto
      (fun n ↦
        W
          (l2CounterexampleSequence n,
            (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n))
      atTop
      (𝓝 ((toWeakSpace ℝ L2) l2CounterexampleLimit,
        (toWeakSpace ℝ L2) ((1 - 1 / Real.sqrt 2) • l2CounterexampleLimit))) := by
  have htail_orthonormal : Orthonormal ℝ (fun n ↦ l2BasisVector (2 * n + 2)) := by
    -- Compose the standard basis with the injective even-tail index map.
    refine l2BasisVector_orthonormal.comp (fun n ↦ 2 * n + 2) ?_
    intro m n hmn
    have hmul : 2 * m = 2 * n := Nat.add_right_cancel hmn
    omega
  have htail :
      Tendsto (fun n ↦ toWeakSpace ℝ L2 (l2BasisVector (2 * n + 2))) atTop
        (𝓝 (0 : WeakSpace ℝ L2)) :=
    orthonormal_sequence_tendsto_zero_weakly (fun n ↦ l2BasisVector (2 * n + 2))
      htail_orthonormal
  have hconst :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ L2 (l2BasisVector 1)) atTop
        (𝓝 (toWeakSpace ℝ L2 (l2BasisVector 1))) :=
    tendsto_const_nhds
  have hfirst :
      Tendsto (fun n ↦ toWeakSpace ℝ L2 (l2CounterexampleSequence n)) atTop
        (𝓝 (toWeakSpace ℝ L2 l2CounterexampleLimit)) := by
    -- Weak convergence of `e_{2n}` to `0` survives translation by the constant vector `e_1`.
    simpa [l2CounterexampleSequence, l2CounterexampleLimit, toWeakSpace] using hconst.add htail
  have hsecond :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ L2 ((1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n))
        atTop
        (𝓝 ((toWeakSpace ℝ L2) ((1 - 1 / Real.sqrt 2) • l2CounterexampleLimit))) := by
    -- Scalar multiplication is continuous in the weak space, so it preserves the first limit.
    simpa [toWeakSpace] using hfirst.const_smul (1 - 1 / Real.sqrt 2 : ℝ)
  -- Assemble the coordinatewise weak limits into the product weak limit.
  simpa using hfirst.prodMk_nhds hsecond

-- Proof sketch: the limit vector `e_1` lies on the unit sphere, so its projection onto the
-- closed unit ball is itself and the residual vanishes there. Hence the graph value at `e_1` is
-- `0`, not `(1 - 1 / √2) • e_1`.
private theorem l2ClosedUnitBallResidualMap_witness_limit_not_mem_graph :
    (l2CounterexampleLimit,
      (1 - 1 / Real.sqrt 2) • l2CounterexampleLimit) ∉
        l2ClosedUnitBallResidualMap.toSetValuedOperator.graph := by
  rw [SetValuedOperator.mem_graph, Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  intro hmem
  have hlimit_mem_C : l2CounterexampleLimit ∈ C := by
    -- The weak limit is a unit basis vector, hence it belongs to the closed unit ball.
    simpa [Metric.mem_closedBall, dist_eq_norm, l2CounterexampleLimit, l2BasisVector]
  have hproj :
      P[C, hC] l2CounterexampleLimit = l2CounterexampleLimit := by
    -- Points in the closed unit ball are fixed by the projector.
    have hfixed :
        l2CounterexampleLimit ∈ Function.fixedPoints (P[C, hC]) := by
      rw [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
        closedUnitBall_nonempty
        (Metric.isClosed_closedBall : IsClosed C)
        (convex_closedBall (0 : L2) 1)]
      exact hlimit_mem_C
    simpa [Function.mem_fixedPoints_iff] using hfixed
  have hscalar_pos : 0 < (1 - 1 / Real.sqrt 2 : ℝ) := by
    have hdiv_lt_one : (1 / Real.sqrt 2 : ℝ) < 1 := by
      simpa [one_div] using inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
    linarith
  have hlimit_nonzero : l2CounterexampleLimit ≠ 0 := by
    have hnorm_ne_zero : ‖l2CounterexampleLimit‖ ≠ 0 := by
      simpa [l2CounterexampleLimit, l2BasisVector]
    exact norm_ne_zero_iff.mp hnorm_ne_zero
  have hscaled_nonzero :
      (1 - 1 / Real.sqrt 2 : ℝ) • l2CounterexampleLimit ≠ 0 :=
    smul_ne_zero (ne_of_gt hscalar_pos) hlimit_nonzero
  have hresidual_zero :
      l2ClosedUnitBallResidualMap l2CounterexampleLimit = 0 := by
    -- Inside the ball the projector fixes the point, so the residual vanishes.
    simp [l2ClosedUnitBallResidualMap, hproj]
  exact hscaled_nonzero (hmem.trans hresidual_zero)

-- Proof sketch: combine maximal monotonicity of the residual map with the explicit witness graph
-- sequence, its product-weak convergence, and the fact that the limit pair lies outside the graph.
/-- Example 20.39: for the closed unit ball of `ℓ²(ℕ, ℝ)`, subtracting the canonical metric
projection onto that ball yields a maximally monotone operator whose graph is not sequentially
closed in the product weak topology. -/
theorem l2ClosedUnitBallResidualMap_maximallyMonotone_and_graph_not_seqClosed_weakProduct :
    Maximal SetValuedOperator.IsMonotone l2ClosedUnitBallResidualMap.toSetValuedOperator ∧
      ¬ IsSeqClosed
        (W '' l2ClosedUnitBallResidualMap.toSetValuedOperator.graph) := by
  refine ⟨l2ClosedUnitBallResidualMap_isMaximallyMonotone, ?_⟩
  intro hseqClosed
  have hmem :
      ∀ n,
        W
            (l2CounterexampleSequence n,
              (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n) ∈
          W '' l2ClosedUnitBallResidualMap.toSetValuedOperator.graph := by
    intro n
    exact ⟨(l2CounterexampleSequence n, (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n),
      l2ClosedUnitBallResidualMap_witness_mem_graph n, rfl⟩
  have hlimit_mem :
      ((toWeakSpace ℝ L2) l2CounterexampleLimit,
        (toWeakSpace ℝ L2) ((1 - 1 / Real.sqrt 2) • l2CounterexampleLimit)) ∈
        W '' l2ClosedUnitBallResidualMap.toSetValuedOperator.graph :=
    hseqClosed hmem l2ClosedUnitBallResidualMap_witness_tendsto_weakly
  rcases hlimit_mem with ⟨p, hp, hpEq⟩
  have hW_injective : Function.Injective W :=
    (Prod.map_injective).2 ⟨(toWeakSpace ℝ L2).injective, (toWeakSpace ℝ L2).injective⟩
  have hp_eq :
      p = (l2CounterexampleLimit, (1 - 1 / Real.sqrt 2) • l2CounterexampleLimit) :=
    hW_injective hpEq
  rw [hp_eq] at hp
  exact l2ClosedUnitBallResidualMap_witness_limit_not_mem_graph hp

end Function
