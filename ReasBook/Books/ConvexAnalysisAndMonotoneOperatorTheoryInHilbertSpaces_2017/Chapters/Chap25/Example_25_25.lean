import BauschkeLean.Chap16.Example_16_51
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap21.Corollary_21_25
import BauschkeLean.Chap25.Example_25_14
import Mathlib.LinearAlgebra.Matrix.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction
open SetValuedOperator

namespace Set

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "x₀" => (!₂[(1 : ℝ), (0 : ℝ)] : ℝ²)
local notation "C" => Metric.closedBall x₀ ‖x₀‖
local notation "D" => (-(C : Set ℝ²))

/- Source/core/bridge triage:
- `source-facing`: Example 25.25 revisits the Example 25.1 normal-cone counterexample on the
  opposite tangent closed unit balls in `ℝ²`, records that each normal cone is `3*` monotone, and
  then shows that the Brézis--Haraux closure identity fails.
- `core/canonical`: the owner surfaces are `(N[C]).IsThreeStarMonotone`,
  `(N[D]).IsThreeStarMonotone`, `(N[C] + N[D]).range`, `(N[C]).range`, `(N[D]).range`, and the
  Chapter 21 surjectivity owner
  `SetValuedOperator.range_eq_univ_of_maximal_of_bounded_dom`.
- `bridge/view`: the concrete `ℝ²` fiber computation at the common tangent point is reused from
  `Chap16/Example_16_51`, while the source set `ℝ × {0}` is formalized as
  `{u : ℝ² | u 1 = 0}` inside `EuclideanSpace ℝ (Fin 2)`. -/
-- Semantic recall: `lean_leansearch` did not return a useful item-specific theorem, so the API
-- choice was verified against the local Chapter 25 owners
-- `Set.normalCone_isThreeStarMonotone` and
-- `SetValuedOperator.closure_range_add_eq_closure_range_sum_of_isThreeStarMonotone`.

private theorem x₀_norm_eq_one : ‖x₀‖ = 1 := by
  have hsq : ‖x₀‖ ^ 2 = 1 := by
    norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hnonneg : 0 ≤ ‖x₀‖ := norm_nonneg x₀
  nlinarith

private theorem neg_x₀_eq_left_unit_vector :
    -x₀ = (!₂[(-1 : ℝ), (0 : ℝ)] : ℝ²) := by
  ext i
  fin_cases i <;> norm_num

private theorem D_eq_closedBall_neg_x₀ :
    D = Metric.closedBall (-x₀) ‖x₀‖ := by
  ext y
  have hdist : dist (-y) x₀ = dist y (-x₀) := by
    simpa using (dist_neg_neg y (-x₀))
  constructor
  · intro hy
    rw [Set.mem_neg, Metric.mem_closedBall] at hy
    rw [Metric.mem_closedBall]
    rw [← hdist]
    exact hy
  · intro hy
    rw [Set.mem_neg, Metric.mem_closedBall]
    rw [Metric.mem_closedBall] at hy
    rw [hdist]
    exact hy

private theorem origin_mem_C : (0 : ℝ²) ∈ C := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp

private theorem origin_mem_D : (0 : ℝ²) ∈ D := by
  change -(0 : ℝ²) ∈ C
  simpa only [neg_zero] using origin_mem_C

private theorem normalCone_dom_eq (S : Set ℝ²) :
    SetValuedOperator.dom (N[S] : SetValuedOperator ℝ² ℝ²) = S := by
  ext x
  by_cases hx : x ∈ S
  · constructor
    · intro _
      exact hx
    · intro _
      change (N[S] x).Nonempty
      refine ⟨0, ?_⟩
      simp [Set.normalCone_of_mem hx]
  · constructor
    · intro hxdom
      change (N[S] x).Nonempty at hxdom
      rw [Set.normalCone_of_not_mem hx] at hxdom
      simp at hxdom
    · intro hxS
      exact (hx hxS).elim

private theorem closedBall_inter_neg_closedBall_eq_singleton_origin :
    C ∩ D = ({0} : Set ℝ²) := by
  rw [D_eq_closedBall_neg_x₀, neg_x₀_eq_left_unit_vector, x₀_norm_eq_one]
  simpa [Set.inter_comm] using
    ERealFunction.leftRightClosedUnitBall_inter_eq_singleton_origin

private theorem sum_normalCone_at_origin_eq_horizontal_axis :
    (N[C] + N[D]) (0 : ℝ²) = {u : ℝ² | u 1 = 0} := by
  have hsubdC : ∂ ι[C] = N[C] :=
    subdifferential_setIndicator_eq_normalCone C ⟨0, origin_mem_C⟩
  have hsubdD : ∂ ι[D] = N[D] :=
    subdifferential_setIndicator_eq_normalCone D ⟨0, origin_mem_D⟩
  calc
    (N[C] + N[D]) (0 : ℝ²) = N[C] (0 : ℝ²) + N[D] (0 : ℝ²) := by
      rfl
    _ = (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) := by
      rw [← congrFun hsubdC (0 : ℝ²), ← congrFun hsubdD (0 : ℝ²)]
    _ = {u : ℝ² | u 1 = 0} := by
      rw [D_eq_closedBall_neg_x₀, neg_x₀_eq_left_unit_vector, x₀_norm_eq_one]
      simpa [add_comm] using
        ERealFunction.sum_subdifferential_closedBallIndicators_at_origin

private theorem normalCone_range_eq_univ_of_closedBall
    (S : Set ℝ²) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    (hS_bounded : Bornology.IsBounded S) :
    SetValuedOperator.range (N[S] : SetValuedOperator ℝ² ℝ²) = Set.univ := by
  have hmax : Maximal IsMonotone (N[S] : SetValuedOperator ℝ² ℝ²) :=
    Set.normalCone_isMaximallyMonotone hS_nonempty hS_closed hS_convex
  exact range_eq_univ_of_maximal_of_bounded_dom
    (N[S] : SetValuedOperator ℝ² ℝ²) hmax (by simpa [normalCone_dom_eq S] using hS_bounded)

/-- Example 25.25 (1): in the concrete `ℝ²` realization of Example 25.1, the normal cone `N[C]`
for `C = Metric.closedBall !₂[(1, 0)] ‖!₂[(1, 0)]‖` is `3*` monotone. -/
theorem normalCone_closedBall_unit_vector_isThreeStarMonotone :
    let A : SetValuedOperator ℝ² ℝ² := N[C]
    A.IsThreeStarMonotone := by
  dsimp
  simpa using
    (Set.normalCone_isThreeStarMonotone :
      SetValuedOperator.IsThreeStarMonotone (N[C] : SetValuedOperator ℝ² ℝ²))

/-- Example 25.25 (2): in the same Example 25.1 realization, the normal cone `N[D]` for the
opposite closed ball `D = -C` is `3*` monotone. -/
theorem normalCone_neg_closedBall_unit_vector_isThreeStarMonotone :
    let A : SetValuedOperator ℝ² ℝ² := N[D]
    A.IsThreeStarMonotone := by
  dsimp
  simpa using
    (Set.normalCone_isThreeStarMonotone :
      SetValuedOperator.IsThreeStarMonotone (N[D] : SetValuedOperator ℝ² ℝ²))

/-- Example 25.25 (3): for the opposite tangent closed unit balls from Example 25.1,
`closure (ran (N[C] + N[D])) = ℝ × {0}`, formalized as
`closure (((N[C]) + (N[D])).range) = {u : ℝ² | u 1 = 0}`. -/
theorem closure_range_normalCone_closedBall_add_neg_eq_horizontal_axis :
    let A : SetValuedOperator ℝ² ℝ² := N[C]
    let B : SetValuedOperator ℝ² ℝ² := N[D]
    closure ((A + B).range) = {u : ℝ² | u 1 = 0} := by
  dsimp
  have hrange :
      SetValuedOperator.range
          ((N[C] : SetValuedOperator ℝ² ℝ²) + (N[D] : SetValuedOperator ℝ² ℝ²)) =
        {u : ℝ² | u 1 = 0} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro u hu
      rcases (mem_range_iff (N[C] + N[D]) u).1 hu with ⟨x, hu⟩
      rcases Set.mem_add.mp hu with ⟨uC, huC, uD, huD, rfl⟩
      have hxC : x ∈ C := by
        rw [← normalCone_dom_eq C]
        exact (mem_dom_iff N[C] x).2 ⟨uC, huC⟩
      have hxD : x ∈ D := by
        rw [← normalCone_dom_eq D]
        exact (mem_dom_iff N[D] x).2 ⟨uD, huD⟩
      have hx0 : x = 0 := by
        have hxCD : x ∈ C ∩ D := ⟨hxC, hxD⟩
        have hxSingleton : x ∈ ({0} : Set ℝ²) := by
          rw [← closedBall_inter_neg_closedBall_eq_singleton_origin]
          exact hxCD
        simpa using hxSingleton
      subst hx0
      have hu0 : uC + uD ∈ (N[C] + N[D]) (0 : ℝ²) :=
        Set.mem_add.mpr ⟨uC, huC, uD, huD, rfl⟩
      rw [sum_normalCone_at_origin_eq_horizontal_axis] at hu0
      simpa using hu0
    · intro u hu
      have hu0 : u ∈ (N[C] + N[D]) (0 : ℝ²) := by
        rw [sum_normalCone_at_origin_eq_horizontal_axis]
        exact hu
      exact (mem_range_iff (N[C] + N[D]) u).2 ⟨0, hu0⟩
  have hclosed : IsClosed ({u : ℝ² | u 1 = 0} : Set ℝ²) :=
    by
      simpa using
        isClosed_eq
          (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1) continuous_const
  rw [hrange, hclosed.closure_eq]

/-- Example 25.25 (4): for the same pair of normal cones,
`closure (ran N[C] + ran N[D]) = ℝ²`, formalized as
`closure ((N[C]).range + (N[D]).range) = Set.univ`. -/
theorem closure_range_sum_normalCone_closedBall_neg_eq_univ :
    let A : SetValuedOperator ℝ² ℝ² := N[C]
    let B : SetValuedOperator ℝ² ℝ² := N[D]
    closure (A.range + B.range) = (Set.univ : Set ℝ²) := by
  dsimp
  have hC_nonempty : Set.Nonempty C := ⟨0, origin_mem_C⟩
  have hD_nonempty : Set.Nonempty D := ⟨0, origin_mem_D⟩
  have hC_range :
      SetValuedOperator.range (N[C] : SetValuedOperator ℝ² ℝ²) = (Set.univ : Set ℝ²) :=
    normalCone_range_eq_univ_of_closedBall C hC_nonempty Metric.isClosed_closedBall
      (convex_closedBall x₀ ‖x₀‖) Metric.isBounded_closedBall
  have hD_range :
      SetValuedOperator.range (N[D] : SetValuedOperator ℝ² ℝ²) = (Set.univ : Set ℝ²) := by
    refine normalCone_range_eq_univ_of_closedBall D hD_nonempty ?_ ?_ ?_
    · simpa [D_eq_closedBall_neg_x₀] using
        (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (-x₀) ‖x₀‖ : Set ℝ²))
    · simpa [D_eq_closedBall_neg_x₀] using
        (convex_closedBall (-x₀) ‖x₀‖ :
          Convex ℝ (Metric.closedBall (-x₀) ‖x₀‖ : Set ℝ²))
    · simpa [D_eq_closedBall_neg_x₀] using
        (Metric.isBounded_closedBall :
          Bornology.IsBounded (Metric.closedBall (-x₀) ‖x₀‖ : Set ℝ²))
  rw [hC_range, hD_range]
  simp

/-- Example 25.25 (5): consequently the two closures differ, so the conclusion of Theorem 25.24
cannot hold here without the maximal-monotonicity hypothesis on `N[C] + N[D]`. -/
theorem closure_range_normalCone_closedBall_add_neg_ne_closure_range_sum :
    let A : SetValuedOperator ℝ² ℝ² := N[C]
    let B : SetValuedOperator ℝ² ℝ² := N[D]
    closure ((A + B).range) ≠ closure (A.range + B.range) := by
  dsimp
  rw [closure_range_normalCone_closedBall_add_neg_eq_horizontal_axis,
    closure_range_sum_normalCone_closedBall_neg_eq_univ]
  intro hEq
  have hmem : (!₂[(0 : ℝ), (1 : ℝ)] : ℝ²) ∈ ({u : ℝ² | u 1 = 0} : Set ℝ²) := by
    rw [hEq]
    simp
  simp at hmem

end Set
