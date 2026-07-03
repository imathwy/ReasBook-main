import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_16
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_44
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_41
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_26
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)

noncomputable section

section

variable {n p : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin p)

/- Algorithm 12.5 is `source-facing`: it gives the explicit dual projection-gradient recursion for
the polyhedral system `A x ≤ b`.

Domain sampling identifies the abstraction layers as follows.
- `source-facing`: the explicit DPG dual sequence `y^k` and the derived primal points `x^k`;
- `core/canonical`: the Chapter 12.1 admissible stepsize owner
  `DualBasedProximalGradientDualStepsizeParameter` specialized to `σ = 1`, together with the
  Chapter 12.2 trajectory owner `is_dual_proximal_gradient_primal_trajectory`;
- `bridge/view`: the projection-specific explicit formulas `Aᵀ y + d` and
  `y - (1 / L) A x + (1 / L) min {A x - L y, b}` realizing the Chapter 12.2 argmax/proximal
  steps for the quadratic projection model.

The primitive projection data are therefore the shared stepsize owner, the coordinatewise minimum
in `ℝ^p`, the explicit primal point, and the explicit dual update. The recursive iterate families
remain source-facing, while the canonical Chapter 12.2 owner is recovered by a bridge theorem. -/

/-- The admissible constant stepsize parameters for the polyhedral projection problem. This is the
Chapter 12.1 dual stepsize owner specialized to the projection objective, whose strong-convexity
modulus is `σ = 1`. -/
abbrev PolyhedralProjectionStepsizeParameter
    (A : Matrix (Fin p) (Fin n) ℝ) :=
  DualBasedProximalGradientDualStepsizeParameter
    (A.toEuclideanLin.toContinuousLinearMap) 1

-- Proof sketch: specialize the Chapter 12.1 lower-bound theorem at `σ = 1`, then simplify the
-- resulting scalar expression `‖A‖² / 1`.
/-- Every admissible polyhedral-projection stepsize parameter satisfies `‖A‖₂,₂² ≤ L`. -/
theorem polyhedral_projection_stepsize_parameter_lower_bound
    (A : Matrix (Fin p) (Fin n) ℝ) (L : PolyhedralProjectionStepsizeParameter A) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ (2 : ℕ) ≤ (L : ℝ) := by
  simpa [PolyhedralProjectionStepsizeParameter,
    dual_based_proximal_gradient_dual_lipschitz_constant_eq]
    using
      DualBasedProximalGradientDualStepsizeParameter.lower_bound L

/-- The coordinatewise minimum of two vectors in `ℝ^p`. -/
def euclidean_coordinatewise_min (x y : Ep) : Ep :=
  toLp 2 (fun i ↦ min (x i) (y i))

/-- Evaluating the coordinatewise minimum at `i` gives `min (x_i, y_i)`. -/
@[simp] theorem euclidean_coordinatewise_min_apply
    (x y : Ep) (i : Fin p) :
    euclidean_coordinatewise_min x y i = min (x i) (y i) :=
  rfl

/-- Helper for Algorithm 12.5: if `y ≤ b`, then the residual from clamping `s` above by `b`
has nonpositive product with the feasible displacement from the same clamp to `y`. -/
theorem sub_min_mul_nonpos_of_le_right
    (s y b : ℝ) (hy : y ≤ b) :
    (s - min s b) * (y - min s b) ≤ 0 := by
  by_cases hsb : s ≤ b
  · rw [min_eq_left hsb]
    simp
  · rw [min_eq_right (le_of_not_ge hsb)]
    exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (le_of_not_ge hsb))
      (sub_nonpos.mpr hy)

/-- The shared primal point `Aᵀ y + d` attached to the current dual iterate `y`. -/
def polyhedral_projection_primal_point
    (A : Matrix (Fin p) (Fin n) ℝ) (d : En) (y : Ep) : En :=
  A.transpose.toEuclideanLin y + d

/-- The shared explicit dual update from a primal point `x` and current dual point `y`:
`y - (1 / L) A x + (1 / L) min {A x - L y, b}`. -/
def polyhedral_projection_dual_update
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (L : PosReal) (x : En) (y : Ep) : Ep :=
  y - (1 / L : ℝ) • A.toEuclideanLin x +
    (1 / L : ℝ) • euclidean_coordinatewise_min (A.toEuclideanLin x - (L : ℝ) • y) b

/-- Algorithm 12.5: given `A`, `b`, `d`, an admissible constant parameter `L ≥ ‖A‖₂,₂²`, and an
initial dual point `y⁰ = y0`, the polyhedral projection DPG method generates the dual iterates
`y^k` by recursively applying the shared primal-point and dual-update formulas. -/
def polyhedral_projection_dpg_dual_iterates
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) : ℕ → Ep
  | 0 => y0
  | k + 1 =>
      let yk := polyhedral_projection_dpg_dual_iterates A b d L y0 k
      polyhedral_projection_dual_update A b L
        (polyhedral_projection_primal_point A d yk) yk

/-- The associated primal iterates `x^k = Aᵀ y^k + d` derived from the DPG dual recursion. -/
def polyhedral_projection_dpg_primal_iterates
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) : ℕ → En :=
  fun k ↦ polyhedral_projection_primal_point A d
    (polyhedral_projection_dpg_dual_iterates A b d L y0 k)

private def polyhedral_projection_quadratic_objective (d : En) : En → EReal :=
  fun x ↦ ((((1 / 2 : ℝ) * ‖x - d‖ ^ (2 : ℕ)) : ℝ) : EReal)

private def polyhedral_projection_upper_box_indicator (b : Ep) : Ep → EReal :=
  extendedIndicator {z : Ep | ∀ i : Fin p, z i ≤ b i}

section

variable (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
variable (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep)

local notation "y[" k "]" => polyhedral_projection_dpg_dual_iterates A b d L y0 k
local notation "x[" k "]" => polyhedral_projection_dpg_primal_iterates A b d L y0 k
local notation "ySeq" => polyhedral_projection_dpg_dual_iterates A b d L y0
local notation "xSeq" => polyhedral_projection_dpg_primal_iterates A b d L y0
local notation "IsPolyhedralProjectionDPGTrajectory" =>
  @is_dual_proximal_gradient_primal_trajectory En Ep _ _ _ _ _ _
    (polyhedral_projection_quadratic_objective d)
    (polyhedral_projection_upper_box_indicator b)
    A.toEuclideanLin (1 : PosReal) L y0

/-- The polyhedral projection DPG dual sequence starts from the prescribed initialization
`y⁰ = y0`. -/
theorem polyhedral_projection_dpg_dual_iterates_zero
    :
    y[0] = y0 :=
  rfl

-- Proof sketch: unfold `polyhedral_projection_dpg_dual_iterates` at `k + 1`; the recursive
-- clause applies the shared dual-update owner to the current iterate `y^k`.
/-- Each successor dual iterate is obtained by evaluating the shared dual update at the current
dual iterate and its associated primal point. -/
theorem polyhedral_projection_dpg_dual_iterates_succ
    (k : ℕ) :
    y[k + 1] =
      polyhedral_projection_dual_update A b L
        (polyhedral_projection_primal_point A d y[k])
        y[k] :=
  by
  -- Route correction: unfold the recursive definition directly instead of relying on a generated
  -- recursion equation that can drift under elaboration.
  rfl

-- Proof sketch: unfold `polyhedral_projection_dpg_primal_iterates`; by definition `x^k` is the
-- shared primal-point owner evaluated at the current dual iterate `y^k`.
/-- The primal iterates satisfy the textbook identity `x^k = Aᵀ y^k + d`. -/
theorem polyhedral_projection_dpg_primal_iterates_eq
    (k : ℕ) :
    x[k] = A.transpose.toEuclideanLin y[k] + d :=
  rfl

/-- Helper for Algorithm 12.5: the affine-minus-quadratic step-(a) objective is a constant minus
the squared distance to the explicit primal point `Aᵀ y + d`. -/
theorem polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq_real
    (y : Ep) (x' : En) :
    (inner ℝ x' (A.transpose.toEuclideanLin y) : ℝ) -
        (1 / 2 : ℝ) * ‖(x' - d : En)‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖(polyhedral_projection_primal_point A d y : En)‖ ^ (2 : ℕ) -
        (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) -
        (1 / 2 : ℝ) *
          ‖(x' - (polyhedral_projection_primal_point A d y : En) : En)‖ ^ (2 : ℕ) :=
  by
  let a : En := A.transpose.toEuclideanLin y
  have hxd : ‖(x' - d : En)‖ ^ (2 : ℕ) = ‖x'‖ ^ (2 : ℕ) - 2 * inner ℝ x' d + ‖d‖ ^ (2 : ℕ) := by
    simpa [real_inner_comm] using (norm_sub_sq_real x' d)
  have hxa :
      ‖(x' - (polyhedral_projection_primal_point A d y : En) : En)‖ ^ (2 : ℕ) =
        ‖x'‖ ^ (2 : ℕ) - 2 * inner ℝ x' (polyhedral_projection_primal_point A d y) +
          ‖(polyhedral_projection_primal_point A d y : En)‖ ^ (2 : ℕ) := by
    simpa [real_inner_comm] using (norm_sub_sq_real x' (polyhedral_projection_primal_point A d y))
  have hadd :
      inner ℝ x' (polyhedral_projection_primal_point A d y) =
        inner ℝ x' (A.transpose.toEuclideanLin y) + inner ℝ x' d := by
    -- Split the completed-square center into the affine term and the shift by `d`.
    simp [polyhedral_projection_primal_point, inner_add_right]
  nlinarith

/-- Helper for Algorithm 12.5: the affine-minus-quadratic step-(a) objective is a constant minus
the squared distance to the explicit primal point `Aᵀ y + d`. -/
theorem polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq
    (y : Ep) (x' : En) :
    (((inner ℝ x' (A.transpose.toEuclideanLin y) : ℝ) : EReal) -
      polyhedral_projection_quadratic_objective d x') =
      (((1 / 2 : ℝ) * ‖(polyhedral_projection_primal_point A d y : En)‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) *
            ‖x' - (polyhedral_projection_primal_point A d y : En)‖ ^ (2 : ℕ) : ℝ) :
        EReal) :=
  by
  -- Cast the real completed-square identity once after unfolding the quadratic objective.
  exact_mod_cast
    polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq_real
      (A := A) (d := d) y x'

/-- Helper for Algorithm 12.5: the explicit primal point `Aᵀ y + d` globally maximizes the
step-(a) affine-minus-quadratic owner objective. -/
theorem polyhedral_projection_primal_point_isMaxOn_owner
    (y : Ep) :
    IsMaxOn
      (fun x' : En ↦
        (((inner ℝ x' (A.toEuclideanLin.adjoint y) : ℝ) : EReal) -
          polyhedral_projection_quadratic_objective d x'))
      Set.univ
      (polyhedral_projection_primal_point A d y) :=
  -- TODO: rewrite `A.toEuclideanLin.adjoint` to `A.transpose.toEuclideanLin`, apply the
  -- completed-square identity at `x'` and at the center `polyhedral_projection_primal_point A d y`,
  -- and close the remaining comparison with `EReal.coe_le_coe_iff.mpr (sub_le_self _ hquad_nonneg)`.
  sorry

/-- The explicit primal point `Aᵀ y + d` is the Chapter 12.2 step-(a) argmax point for the
quadratic projection objective. -/
theorem polyhedral_projection_primal_point_mem_argmax
    (y : Ep) :
    polyhedral_projection_primal_point A d y ∈
      dual_proximal_gradient_primal_x_argmax
        (polyhedral_projection_quadratic_objective d) A.toEuclideanLin y :=
  -- TODO: unfold `dual_proximal_gradient_primal_x_argmax` and package
  -- `polyhedral_projection_primal_point_isMaxOn_owner`.
  sorry

/-- Helper for Algorithm 12.5: the upper box `{z | z_i ≤ b_i}` is convex. -/
theorem polyhedral_projection_upper_box_convex
    (b : Ep) :
    Convex ℝ {z : Ep | ∀ i : Fin p, z i ≤ b i} := by
  intro x hx y hy a b' ha hb hab i
  -- Check convexity coordinatewise, then collapse the scalar combination with `a + b' = 1`.
  calc
    (a • x + b' • y) i = a * x i + b' * y i := by simp
    _ ≤ a * b i + b' * b i := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = (a + b') * b i := by ring
    _ = b i := by rw [hab, one_mul]

/-- Helper for Algorithm 12.5: the coordinatewise minimum is the projection of `s` onto the upper
box `{z | z_i ≤ b_i}`. -/
theorem euclidean_coordinatewise_min_mem_projection_mapping_upper_box
    (s : Ep) :
    euclidean_coordinatewise_min s b ∈
      P[{z : Ep | ∀ i : Fin p, z i ≤ b i}] s :=
  by
  let u : Ep := euclidean_coordinatewise_min s b
  have hu_mem : u ∈ {z : Ep | ∀ i : Fin p, z i ≤ b i} := by
    intro i
    show u i ≤ b i
    simpa [u, euclidean_coordinatewise_min_apply] using (min_le_right (s i) (b i))
  refine
    (mem_projection_mapping_iff_inner_le_zero
      {z : Ep | ∀ i : Fin p, z i ≤ b i}
      (polyhedral_projection_upper_box_convex b) s hu_mem).2 ?_
  intro y hy
  rw [euclideanSpace_inner_eq_sum_mul]
  exact Finset.sum_nonpos fun i _ ↦ by
    simpa [u, euclidean_coordinatewise_min_apply] using
      sub_min_mul_nonpos_of_le_right (s i) (y i) (b i) (hy i)

/-- Helper for Algorithm 12.5: positive scaling leaves the upper-box indicator unchanged because
it is `0` on the box and `⊤` outside. -/
theorem smul_polyhedral_projection_upper_box_indicator
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (L : PolyhedralProjectionStepsizeParameter A) :
    ((((L : EReal) • polyhedral_projection_upper_box_indicator b) : Ep → EReal)) =
      polyhedral_projection_upper_box_indicator b := by
  funext z
  change ((L : EReal) * polyhedral_projection_upper_box_indicator b z) =
    polyhedral_projection_upper_box_indicator b z
  have hL_pos : (0 : ℝ) < ((L : PosReal) : ℝ) := by
    exact PosReal.coe_pos (L : PosReal)
  have hL_pos' : (0 : EReal) < (L : EReal) := by
    exact_mod_cast hL_pos
  by_cases hz : z ∈ {z : Ep | ∀ i : Fin p, z i ≤ b i}
  · have hz_zero : polyhedral_projection_upper_box_indicator b z = 0 := by
      simp [polyhedral_projection_upper_box_indicator, extendedIndicator, hz]
    rw [hz_zero]
    simp
  · have hz_top : polyhedral_projection_upper_box_indicator b z = ⊤ := by
      simp [polyhedral_projection_upper_box_indicator, extendedIndicator, hz]
    rw [hz_top]
    simp [EReal.mul_top_of_pos hL_pos']

/-- Helper for Algorithm 12.5: the clipped point `min {A x - L y, b}` is a proximal point of the
scaled upper-box indicator at `A x - L y`. -/
theorem polyhedral_projection_clipped_point_mem_scaled_indicator_prox
    (x : En) (y : Ep) :
    euclidean_coordinatewise_min (A.toEuclideanLin x - (L : ℝ) • y) b ∈
      prox (((L : EReal) • polyhedral_projection_upper_box_indicator b))
        (A.toEuclideanLin x - (L : ℝ) • y) :=
  -- TODO: rewrite the scaled upper-box indicator via
  -- `smul_polyhedral_projection_upper_box_indicator`, identify prox of the indicator with the
  -- projection mapping by `prox_extendedIndicator_eq_projection_mapping`, and finish with
  -- `euclidean_coordinatewise_min_mem_projection_mapping_upper_box`.
  sorry

/-- The explicit clipped dual update realizes the Chapter 12.2 step-(b) primal proximal update
for the indicator of the upper box `{z | z ≤ b}`. -/
theorem polyhedral_projection_dual_update_mem_y_step
    (x : En) (y : Ep) :
    polyhedral_projection_dual_update A b L x y ∈
      dual_proximal_gradient_primal_y_step
        (polyhedral_projection_upper_box_indicator b) A.toEuclideanLin x y L :=
  -- TODO: use `polyhedral_projection_clipped_point_mem_scaled_indicator_prox` as the proximal
  -- witness in the image-set definition of `dual_proximal_gradient_primal_y_step` and then unfold
  -- `polyhedral_projection_dual_update` to match the affine correction.
  sorry

-- Proof sketch: combine `polyhedral_projection_dpg_dual_iterates_succ` with
-- the explicit dual-update definition, then rewrite the primal point through
-- `polyhedral_projection_dpg_primal_iterates_eq`.
/-- The dual iterates satisfy the textbook general step
`y^(k+1) = y^k - (1 / L) A x^k + (1 / L) min {A x^k - L y^k, b}`. -/
theorem polyhedral_projection_dpg_dual_iterates_update
    (k : ℕ) :
    y[k + 1] =
      y[k] - (1 / L : ℝ) • A.toEuclideanLin x[k] +
        (1 / L : ℝ) •
          euclidean_coordinatewise_min
            (A.toEuclideanLin x[k] - (L : ℝ) • y[k])
            b :=
  by
  -- Expand the successor iterate and then rewrite the primal point as `x[k]`.
  rw [polyhedral_projection_dpg_dual_iterates_succ, polyhedral_projection_dual_update,
    polyhedral_projection_dpg_primal_iterates_eq]

/-- Each primal iterate `x^k` lies in the Chapter 12.2 primal argmax set determined by the
current dual iterate `y^k`. -/
theorem polyhedral_projection_dpg_primal_iterates_mem_argmax
    (k : ℕ) :
    polyhedral_projection_dpg_primal_iterates A b d L y0 k ∈
      dual_proximal_gradient_primal_x_argmax
        (polyhedral_projection_quadratic_objective d) A.toEuclideanLin
        (polyhedral_projection_dpg_dual_iterates A b d L y0 k) :=
  -- TODO: specialize `polyhedral_projection_primal_point_mem_argmax` at `y[k]` and unfold the
  -- source-facing primal iterate definition.
  sorry

/-- Each successor dual iterate belongs to the Chapter 12.2 primal proximal-update set based at
the current pair `(x^k, y^k)`. -/
theorem polyhedral_projection_dpg_dual_iterates_mem_y_step
    (k : ℕ) :
    polyhedral_projection_dpg_dual_iterates A b d L y0 (k + 1) ∈
      dual_proximal_gradient_primal_y_step
        (polyhedral_projection_upper_box_indicator b) A.toEuclideanLin
        (polyhedral_projection_dpg_primal_iterates A b d L y0 k)
        (polyhedral_projection_dpg_dual_iterates A b d L y0 k) L :=
  -- TODO: rewrite `y[k + 1]` with `polyhedral_projection_dpg_dual_iterates_update` and then
  -- reuse `polyhedral_projection_dual_update_mem_y_step` at `(x[k], y[k])`.
  sorry

/-- Helper for Algorithm 12.5: the explicit primal and dual iterate families satisfy the fully
expanded Chapter 12.2 trajectory predicate. -/
theorem polyhedral_projection_dpg_is_dual_proximal_gradient_primal_trajectory_explicit :
    @is_dual_proximal_gradient_primal_trajectory En Ep _ _ _ _ _ _
      (polyhedral_projection_quadratic_objective d)
      (polyhedral_projection_upper_box_indicator b)
      A.toEuclideanLin
      (1 : PosReal)
      L
      y0
      (polyhedral_projection_dpg_primal_iterates A b d L y0)
      (polyhedral_projection_dpg_dual_iterates A b d L y0) :=
  -- TODO: assemble the Chapter 12.2 trajectory owner from the initialization theorem and the two
  -- iterate-level membership bridges.
  sorry

/-- The explicit polyhedral projection recursion is a Chapter 12.2 dual proximal-gradient primal
trajectory for the quadratic objective and the upper-box indicator. -/
theorem polyhedral_projection_dpg_is_dual_proximal_gradient_primal_trajectory :
    IsPolyhedralProjectionDPGTrajectory xSeq ySeq :=
  by
  simpa using polyhedral_projection_dpg_is_dual_proximal_gradient_primal_trajectory_explicit

end

end
