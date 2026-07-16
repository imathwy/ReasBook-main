import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_11
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold
open scoped InnerProduct
open ContinuousLinearMap

universe u v

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 ADMM files together with the Chapter 6 soft-threshold owner.

This item is `source-facing`: Algorithm 15.12 gives explicit formulas for the linear solve
`x^(k+1)` and shifted soft-thresholding step `z^(k+1)`, but the ambient owner layer is already
present upstream.

- `core/canonical`: `IsADMMSumCompositionTrajectoryV2` from Algorithm 15.7 for the version-2
  trajectory owner;
- `core/canonical`: `admm_x_update_argmin` and `admm_z_update_argmin` from Algorithms 15.3 and
  15.6 for the per-step ADMM minimization owners;
- `bridge/view`: `ContinuousLinearMap.adjoint`, `ContinuousLinearMap.inverse`, and
  `mem_admm_x_update_argmin_linear_composite_iff`,
  `mem_admm_z_update_argmin_linear_composite_iff`, and
  `admm_multiplier_update_linear_composite_eq` from Algorithm 15.6;
- `bridge/view`: `admm_linear_composite_shifted_l1_regularizer` and
  `admm_linear_composite_shifted_l1_z_update` as the shared shifted `ℓ¹` owners for the
  linear-composite `z`-subproblem;
- `bridge/view`: `T_[·]`, `prox_euclidean_l1_eq_singleton_softThreshold`, and
  `proximal_mapping_scaling_translation` from Chapter 6 for the explicit soft-threshold formula;
- `source-facing`: the displayed resolvent and the recursive iterate sequences themselves.

Primitive data are therefore only the explicit formulas and iterate sequences. The `x`-solve lives
most canonically on the continuous operator owner `A : X →L[ℝ] E`; the canonical ADMM `arg min`
and multiplier clauses are derived API and should not be duplicated by a parallel owner.

Since the soft-thresholding formula is genuinely coordinatewise, the residual space is kept in the
canonical Euclidean finite-product model `EuclideanSpace ℝ ι`, specializing to the textbook
matrix-vector setting `ℝ^m` when `ι = Fin m`. -/

/-- The explicit Algorithm 15.12 specialization `w^k = x^k`, `y₂^k = 0` of the Chapter 15
version-2 `x`-solve realizes the canonical ADMM `x`-argmin step for the quadratic tether
`x ↦ (1 / 2) ‖x - x^k‖²`. -/
theorem admm_sum_composition_v2_x_update_mem_argmin_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    admm_sum_composition_v2_x_update ρ A zk y1k xk 0 ∈
      admm_x_update_argmin
        ρ
        (fun x : X ↦ ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)))
        A
        (-LinearMap.id)
        0
        zk
        y1k := by
  sorry

/-- The specialized Algorithm 15.12 `x`-solve is exactly the displayed linear-composite ADMM
minimizer with the quadratic proximal tether centered at `x^k`. -/
theorem admm_sum_composition_v2_x_update_isMinOn_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    IsMinOn
      (fun x : X ↦
        ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((ρ : ℝ) / 2) * ‖A x - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ) : ℝ) : EReal))
      Set.univ
      (admm_sum_composition_v2_x_update ρ A zk y1k xk 0) := by
  simpa using
    (mem_admm_x_update_argmin_linear_composite_iff.mp
      (admm_sum_composition_v2_x_update_mem_argmin_zero ρ A zk y1k xk))

end

section

variable {X : Type u} {ι : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-- The shifted `ℓ¹` regularizer centered at `b`, viewed as the canonical `EReal`-valued owner for
the linear-composite ADMM `z`-subproblem. -/
def admm_linear_composite_shifted_l1_regularizer (b : E) : E → EReal :=
  fun z ↦ ((‖z - b‖₁ : ℝ) : EReal)

/-- Evaluating the shifted `ℓ¹` regularizer at `z` gives the translated Euclidean `ℓ¹` norm
`‖z - b‖₁`. -/
@[simp] theorem admm_linear_composite_shifted_l1_regularizer_apply (b z : E) :
    admm_linear_composite_shifted_l1_regularizer b z = ((‖z - b‖₁ : ℝ) : EReal) :=
  rfl

/-- The shared shifted `ℓ¹` soft-threshold `z`-update for the linear-composite split
`A x - z = 0`:
`z^(k+1) = T_[1 / ρ] (A x^(k+1) + (1 / ρ) y^k - b) + b`. -/
def admm_linear_composite_shifted_l1_z_update
    (ρ : PosReal) (A : X →ₗ[ℝ] E) (b : E) (xNext : X) (yk : E) : E :=
  T_[1 / (ρ : ℝ)] (A xNext + (1 / (ρ : ℝ)) • yk - b) + b

-- Proof sketch: unfold `admm_linear_composite_shifted_l1_z_update`; the right-hand side is
-- exactly the shifted soft-thresholding formula displayed for `z^(k+1)` in Algorithms 15.11,
-- 15.12, and 15.13.
/-- Expanding `admm_linear_composite_shifted_l1_z_update` gives the shifted soft-thresholding
formula for `z^(k+1)`. -/
@[simp] theorem admm_linear_composite_shifted_l1_z_update_eq
    (ρ : PosReal) (A : X →ₗ[ℝ] E) (b : E) (xNext : X) (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk =
      T_[1 / (ρ : ℝ)] (A xNext + (1 / (ρ : ℝ)) • yk - b) + b :=
  rfl

/-- The explicit thresholded `z`-update in Algorithm 15.12 is the canonical proximal point of the
shifted `ℓ¹` regularizer `z ↦ ‖z - b‖₁` at the ADMM center
`A x^(k+1) + (1 / ρ) y₁^k`. -/
theorem admm_linear_composite_shifted_l1_z_update_mem_prox
    (ρ : PosReal)
    (A : X →ₗ[ℝ] E)
    (b : E)
    (xNext : X)
    (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        (A xNext + (1 / (ρ : ℝ)) • yk) := by
  let x : E := A xNext + (1 / (ρ : ℝ)) • yk
  let g : E → EReal := fun z ↦ (((1 / (ρ : ℝ)) * ‖z‖₁ : ℝ) : EReal)
  have hshift :
      ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b)) =
        fun z : E ↦ g (z - b) := by
    funext z
    simp [admm_linear_composite_shifted_l1_regularizer, g, Pi.smul_apply, smul_eq_mul,
      EReal.coe_mul]
  have htranslate :
      prox[fun z : E ↦ g (z - b)] x =
        (fun z ↦ z + b) '' prox[g] (x - b) := by
    simpa [g, x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (proximal_mapping_scaling_translation g 1 one_ne_zero (-b) x)
  have hprox :
      prox[g] (x - b) = {T_[1 / (ρ : ℝ)] (x - b)} := by
    simpa [g, x] using
      (prox_euclidean_l1_eq_singleton_softThreshold
        ((inv_pos.mpr ρ.2).le)
        (x - b))
  rw [hshift, htranslate, hprox]
  refine Set.mem_image_of_mem (fun z ↦ z + b) ?_
  simp [x]

/-- The explicit thresholded `z`-update from Algorithm 15.12 belongs to the canonical
linear-composite ADMM `z`-argmin set for the shifted `ℓ¹` block. -/
theorem admm_linear_composite_shifted_l1_z_update_mem_argmin
    (ρ : PosReal)
    (A : X →ₗ[ℝ] E)
    (b : E)
    (xNext : X)
    (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
      admm_z_update_argmin
        ρ
        (admm_linear_composite_shifted_l1_regularizer b)
        A
        (-LinearMap.id)
        0
        xNext
        yk := by
  rw [mem_admm_z_update_argmin_linear_composite_iff]
  exact admm_linear_composite_shifted_l1_z_update_mem_prox ρ A b xNext yk

end

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

private structure IterateState (X' E' : Type*) where
  x : X'
  z : E'
  y1 : E'

private def initialState (x0 : X) (z0 y10 : E) : IterateState X E :=
  { x := x0
    z := z0
    y1 := y10 }

private def stateUpdate
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (state : IterateState X E) : IterateState X E :=
  let xNext := admm_sum_composition_v2_x_update ρ A state.z state.y1 state.x 0
  let zNext := admm_linear_composite_shifted_l1_z_update ρ A b xNext state.y1
  { x := xNext
    z := zNext
    y1 := admm_multiplier_update ρ A (-LinearMap.id) 0 state.y1 xNext zNext }

private def iterateState
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → IterateState X E
  | 0 => initialState x0 z0 y10
  | k + 1 => stateUpdate ρ A b (iterateState ρ A b x0 z0 y10 k)

/-- Algorithm 15.12 `x`-iterate sequence for the linear-composite ADMM version-2 recursion. -/
def admm_linear_composite_v2_x
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → X :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).x

/-- Algorithm 15.12 `z`-iterate sequence for the linear-composite ADMM version-2 recursion. -/
def admm_linear_composite_v2_z
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → E :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).z

/-- Algorithm 15.12 multiplier sequence `y₁^k` for the linear-composite ADMM version-2
recursion. -/
def admm_linear_composite_v2_y1
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → E :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).y1

section

variable (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E)

local notation "x[" k "]" =>
  admm_linear_composite_v2_x ρ A b x0 z0 y10 k
local notation "z[" k "]" =>
  admm_linear_composite_v2_z ρ A b x0 z0 y10 k
local notation "y1[" k "]" =>
  admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k
local notation "f2" =>
  admm_linear_composite_shifted_l1_regularizer b

/-- The `x`-iterate sequence starts from the prescribed initial point `x⁰ = x0`. -/
theorem admm_linear_composite_v2_x_zero :
    x[0] = x0 := rfl

/-- The `z`-iterate sequence starts from the prescribed initial point `z⁰ = z0`. -/
theorem admm_linear_composite_v2_z_zero :
    z[0] = z0 := rfl

/-- The multiplier sequence starts from the prescribed initial point `y₁⁰ = y10`. -/
theorem admm_linear_composite_v2_y1_zero :
    y1[0] = y10 := rfl

/-- At every iteration `k`, the next `x`-iterate is given by the explicit linear solve from
Algorithm 15.12. -/
theorem admm_linear_composite_v2_x_succ (k : ℕ) :
    x[k + 1] = admm_sum_composition_v2_x_update ρ A z[k] y1[k] x[k] 0 := rfl

/-- At every iteration `k`, the next `z`-iterate is given by the shifted soft-thresholding formula
from Algorithm 15.12. -/
theorem admm_linear_composite_v2_z_succ (k : ℕ) :
    z[k + 1] = admm_linear_composite_shifted_l1_z_update ρ A b x[k + 1] y1[k] := rfl

/-- At every iteration `k`, the next multiplier iterate is the canonical ADMM affine update. -/
theorem admm_linear_composite_v2_y1_succ (k : ℕ) :
    y1[k + 1] = admm_multiplier_update ρ A (-LinearMap.id) 0 y1[k] x[k + 1] z[k + 1] := rfl

/-- At every iteration `k`, the `z`-iterate is the canonical proximal point of the shifted
`ℓ¹` block. -/
theorem admm_linear_composite_v2_z_succ_mem_prox
    (k : ℕ) :
    z[k + 1] ∈
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        (A x[k + 1] + (1 / (ρ : ℝ)) • y1[k]) := by
  sorry

/-- At every iteration `k`, the `z`-iterate belongs to the canonical linear-composite ADMM
`z`-argmin set for the shifted `ℓ¹` block. -/
theorem admm_linear_composite_v2_z_succ_mem_argmin
    (k : ℕ) :
    z[k + 1] ∈ admm_z_update_argmin ρ f2 A (-LinearMap.id) 0 x[k + 1] y1[k] := by
  sorry

/-- The explicit Algorithm 15.12 iterates are the canonical Chapter 15 ADMM-version-2 trajectory
specialized to the zero first block, with `w^k = x^k` and `y₂^k = 0`. This is a `bridge/view`
theorem from the explicit source-facing recursion to the chapter's canonical version-2 trajectory
owner. -/
theorem admm_linear_composite_v2_isADMMSumCompositionTrajectoryV2 :
    IsADMMSumCompositionTrajectoryV2
      ρ
      (fun _ : X ↦ (0 : EReal))
      f2
      A
      (admm_linear_composite_v2_x ρ A b x0 z0 y10)
      (admm_linear_composite_v2_x ρ A b x0 z0 y10)
      (fun _ : ℕ ↦ (0 : X))
      (admm_linear_composite_v2_z ρ A b x0 z0 y10)
      (admm_linear_composite_v2_y1 ρ A b x0 z0 y10)
      x0
      x0
      0
      z0
      y10 where
  x_zero := rfl
  w_zero := rfl
  y2_zero := rfl
  z_zero := rfl
  y1_zero := rfl
  x_step k := rfl
  z_step := admm_linear_composite_v2_z_succ_mem_prox ρ A b x0 z0 y10
  w_step k := by
    rw [prox_zero_eq_singleton]
    exact Set.mem_singleton (x[k + 1])
  y1_step k := by
    calc
      y1[k + 1] = admm_multiplier_update ρ A (-LinearMap.id) 0 y1[k] x[k + 1] z[k + 1] := rfl
      _ = y1[k] + (ρ : ℝ) • (A x[k + 1] - z[k + 1]) :=
        admm_multiplier_update_linear_composite_eq ρ A y1[k] x[k + 1] z[k + 1]
  y2_step k := by
    simp

/-- At every iteration `k`, the `x`-iterate is the canonical linear-composite ADMM minimizer with
the quadratic tether centered at `x^k`. -/
theorem admm_linear_composite_v2_x_succ_mem_argmin (k : ℕ) :
    x[k + 1] ∈
      admm_x_update_argmin
        ρ
        (fun xNext : X ↦ ((((1 / 2 : ℝ) * ‖xNext - x[k]‖ ^ (2 : ℕ) : ℝ) : EReal)))
        A
        (-LinearMap.id)
        0
        z[k]
        y1[k] :=
  admm_sum_composition_v2_x_update_mem_argmin_zero ρ A z[k] y1[k] x[k]

/-- At every iteration `k`, the `x`-iterate globally minimizes the displayed quadratic-tethered
linear-composite ADMM objective from Algorithm 15.12. -/
theorem admm_linear_composite_v2_x_succ_isMinOn (k : ℕ) :
    IsMinOn
      (fun xNext : X ↦
        ((((1 / 2 : ℝ) * ‖xNext - x[k]‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((ρ : ℝ) / 2) * ‖A xNext - z[k] + (1 / (ρ : ℝ)) • y1[k]‖ ^ (2 : ℕ) : ℝ) : EReal))
      Set.univ
      x[k + 1] := by
  sorry

/-- At every iteration `k`, the multiplier iterate satisfies the affine recursion
`y₁^(k+1) = y₁^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem admm_linear_composite_v2_y1_succ_eq (k : ℕ) :
    y1[k + 1] = y1[k] + (ρ : ℝ) • (A x[k + 1] - z[k + 1]) := by
  simpa using admm_multiplier_update_linear_composite_eq ρ A y1[k] x[k + 1] z[k + 1]

/-- Algorithm 15.12 starts from the prescribed initialization
`x⁰ = x0`, `z⁰ = z0`, and `y₁⁰ = y10`. -/
theorem admm_linear_composite_v2_zero :
    x[0] = x0 ∧ z[0] = z0 ∧ y1[0] = y10 := by
  exact ⟨rfl, rfl, rfl⟩

/-- At every iteration `k`, Algorithm 15.12 satisfies the canonical ADMM interpretation of the
explicit formulas: the `x`-step is the specialized linear-composite ADMM `arg min` with quadratic
tether, the `z`-step belongs to the shifted `ℓ¹` ADMM `arg min` set, and the multiplier step is
the canonical affine update. -/
theorem admm_linear_composite_v2_step (k : ℕ) :
    (x[k + 1] ∈
      admm_x_update_argmin
        ρ
        (fun xNext : X ↦ ((((1 / 2 : ℝ) * ‖xNext - x[k]‖ ^ (2 : ℕ) : ℝ) : EReal)))
        A
        (-LinearMap.id)
        0
        z[k]
        y1[k]) ∧
      (z[k + 1] ∈
        admm_z_update_argmin ρ f2 A (-LinearMap.id) 0 x[k + 1] y1[k]) ∧
        y1[k + 1] =
          admm_multiplier_update ρ A (-LinearMap.id) 0 y1[k] x[k + 1] z[k + 1] := by
  exact ⟨admm_linear_composite_v2_x_succ_mem_argmin ρ A b x0 z0 y10 k,
    admm_linear_composite_v2_z_succ_mem_argmin ρ A b x0 z0 y10 k,
    rfl⟩

end

end
