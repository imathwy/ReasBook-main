import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Metric Real Set

/-- Remark III.2-extra-3 (1): if a function is continuous on a closed disc and holomorphic on its
interior, then any upper bound for `‖f z‖` on the boundary circle also bounds `‖f z‖` on the whole
closed disc. -/
-- Proof sketch: package the interior holomorphy and boundary continuity as
-- `DiffContOnCl ℂ f (ball c r)` using `DiffContOnCl.mk_ball`, then apply
-- `Complex.norm_le_of_forall_mem_frontier_norm_le` to `ball c r` and rewrite its frontier and
-- closure as `sphere c r` and `closedBall c r` via `frontier_ball` and `closure_ball`.
theorem norm_le_on_closedBall_of_forall_mem_sphere_norm_le
    {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (closedBall c r)) (hhol : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ sphere c r, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall c r, ‖f z‖ ≤ M := by
  have hd : DiffContOnCl ℂ f (ball c r) := DiffContOnCl.mk_ball hhol hcont
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ ?_
  · intro w hw
    rw [frontier_ball c hr.ne'] at hw
    exact hM w hw
  · rw [closure_ball c hr.ne']
    exact hz

/-- Remark III.2-extra-3 (2): in the centered case, any constant that bounds `‖f z‖` on the
circle `|z| = r` also bounds `‖f z‖` on the whole closed disc `|z| ≤ r`, as in the `M(r)` term
appearing in Cauchy's inequalities. -/
-- Proof sketch: specialize `norm_le_on_closedBall_of_forall_mem_sphere_norm_le` to the center
-- `c = 0`.
theorem norm_le_on_closedBall_zero_of_forall_mem_sphere_norm_le
    {f : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (closedBall (0 : ℂ) r))
    (hhol : DifferentiableOn ℂ f (ball (0 : ℂ) r))
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ M :=
  norm_le_on_closedBall_of_forall_mem_sphere_norm_le hr hcont hhol hM
