import Mathlib.Algebra.Order.Floor.Ring
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

/-- The basepoint `0 : ℝ` lies in the fiber of `Real.fourierChar` over `1 : Circle`. -/
-- Proof sketch: evaluate `Real.fourierChar` at `0` and simplify to `1`.
theorem mem_fourierChar_unit_fiber_zero :
    (0 : ℝ) ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) := by
  -- Evaluating `Real.fourierChar` at `0` lands at the basepoint of the circle.
  simp

/-- The canonical endpoint of the lift of a based loop class in `S¹` through
`Real.fourierChar : ℝ → S¹`, starting at `0`. -/
def circleFundamentalGroupLiftEndpoint
    (γ : FundamentalGroup Circle (1 : Circle)) :
    Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) :=
  real_fourierChar_isCoveringMap.monodromy (FundamentalGroup.toPath γ)
    ⟨0, mem_fourierChar_unit_fiber_zero⟩

/-- Definition 1.5.8: the map `j : π₁(S^1, 1) → ℤ` sends a loop class to the integer endpoint of
the unique lift through `Real.fourierChar : ℝ → S¹` starting at `0`. -/
def circleFundamentalGroupLiftIndex
    (γ : FundamentalGroup Circle (1 : Circle)) : ℤ :=
  Int.floor (circleFundamentalGroupLiftEndpoint γ : ℝ)

/-- A real number lies in the fiber of `Real.fourierChar` over `1 : Circle` exactly when it is
an integer. -/
lemma mem_fourierChar_unit_fiber_iff (x : ℝ) :
    x ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [Real.fourierChar_apply'] at hx
    rcases (Circle.exp_eq_one).1 hx with ⟨n, hn⟩
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      positivity
    have hx_eq : x * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hn
    exact ⟨n, mul_right_cancel₀ h2pi hx_eq⟩
  · rintro ⟨n, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, Real.fourierChar_apply']
    simpa [mul_assoc, mul_comm, mul_left_comm] using Circle.exp_two_pi_mul_int n

private lemma floor_eq_self_of_mem_fourierChar_unit_fiber (x : ℝ)
    (hx : x ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle)) :
    ((Int.floor x : ℤ) : ℝ) = x := by
  rcases (mem_fourierChar_unit_fiber_iff x).1 hx with ⟨n, rfl⟩
  norm_num

/-- The lift index, viewed in `ℝ`, is exactly the canonical lifted endpoint. -/
theorem circleFundamentalGroupLiftIndex_eq_endpoint
    (γ : FundamentalGroup Circle (1 : Circle)) :
    ((circleFundamentalGroupLiftIndex γ : ℤ) : ℝ) = circleFundamentalGroupLiftEndpoint γ := by
  exact floor_eq_self_of_mem_fourierChar_unit_fiber _
    (circleFundamentalGroupLiftEndpoint γ).2

/-- The canonical lifted endpoint is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: unfold `circleFundamentalGroupLiftEndpoint`, evaluate monodromy on the path class
-- of `γ`, and identify the result with the endpoint of `real_fourierChar_isCoveringMap.liftPath`.
theorem circleFundamentalGroupLiftEndpoint_spec (γ : Path (1 : Circle) 1) :
    (circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  -- Monodromy on the path class is definitionally the endpoint of the lifted path.
  rfl

/-- The lift index of a loop class is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: combine `circleFundamentalGroupLiftEndpoint_spec` with the fact that the lifted
-- endpoint lies in the unit fiber of `Real.fourierChar`, hence is an integer.
theorem circleFundamentalGroupLiftIndex_spec (γ : Path (1 : Circle) 1) :
    ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ⟧) : ℤ) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  calc
    ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ⟧) : ℤ) : ℝ) =
        circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧) :=
      circleFundamentalGroupLiftIndex_eq_endpoint _
    _ =
        real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero γ) 1 :=
      circleFundamentalGroupLiftEndpoint_spec γ
