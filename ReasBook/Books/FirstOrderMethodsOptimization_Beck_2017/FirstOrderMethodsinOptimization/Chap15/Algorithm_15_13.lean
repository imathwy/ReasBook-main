import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold

universe u v

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- `source-facing`: the recursive iterate families for Algorithm 15.13.

Domain sampling against `Algorithm_15_5`, `Algorithm_15_10`, `Algorithm_15_12`, and
`Algorithm_15_14` shows the following owner split.

- `core/canonical`: `IsADLPMMTrajectory`, `ad_lpmm_alpha_parameter`, and
  `ad_lpmm_beta_parameter`;
- `bridge/view`: `admm_linear_composite_shifted_l1_z_update` for the shifted `ℓ¹` `z`-step and
  `admm_multiplier_update` for the affine dual step;
- `source-facing`: only the explicit recursive iterate families specialized to `h₁ = 0` and
  `h₂(z) = l1n[z - b]`, together with the positivity hypothesis
  `hL : 0 < adlpmm_linearization_bound (1 : PosReal) A` needed for the source step size
  `1 / L`.

The internal three-component recursion is therefore implementation scaffolding and stays private.
The public surface keeps only the iterate sequences and the source-facing step formulas, with the
shared chapter owners exposed as the canonical bridge theorems. -/

private def iterateState
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → X × E × E
  | 0 => (x0, z0, y0)
  | k + 1 =>
      let ⟨xk, zk, yk⟩ := iterateState A ρ hL b x0 z0 y0 k
      let xNext :=
        xk - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
          A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk)
      let zNext := admm_linear_composite_shifted_l1_z_update ρ A b xNext yk
      (xNext, zNext, admm_multiplier_update ρ A (-LinearMap.id) 0 yk xNext zNext)

/-- Algorithm 15.13: the explicit `x`-iterate sequence for the shifted `ℓ¹` residual
specialization of AD-LPMM. -/
def ad_lpmm_l1_residual_x
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → X :=
  fun k ↦
    let ⟨xk, _, _⟩ := iterateState A ρ hL b x0 z0 y0 k
    xk

/-- Algorithm 15.13: the explicit shifted-soft-threshold `z`-iterate sequence. -/
def ad_lpmm_l1_residual_z
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → E :=
  fun k ↦
    let ⟨_, zk, _⟩ := iterateState A ρ hL b x0 z0 y0 k
    zk

/-- Algorithm 15.13: the multiplier sequence for the shifted `ℓ¹` residual specialization. -/
def ad_lpmm_l1_residual_y
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → E :=
  fun k ↦
    let ⟨_, _, yk⟩ := iterateState A ρ hL b x0 z0 y0 k
    yk

section

/-- The Algorithm 15.13 `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_l1_residual_x_zero
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 0 = x0 :=
  rfl

/-- The Algorithm 15.13 `z`-sequence starts from `z^0 = z0`. -/
theorem ad_lpmm_l1_residual_z_zero
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 0 = z0 :=
  rfl

/-- The Algorithm 15.13 multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_l1_residual_y_zero
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 0 = y0 :=
  rfl

/-- At every iteration `k`, the next `x`-iterate is given by the displayed gradient step from
Algorithm 15.13. -/
theorem ad_lpmm_l1_residual_x_succ
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 (k + 1) =
      ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 k -
        (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
          A.adjoint
            (A (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 k) -
              ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 k +
              (1 / (ρ : ℝ)) • ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 k) := by
  rfl

/-- At every iteration `k`, the next `z`-iterate is the canonical shifted-soft-threshold update
from Chapter 15. -/
theorem ad_lpmm_l1_residual_z_succ
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 (k + 1) =
      admm_linear_composite_shifted_l1_z_update
        ρ
        A
        b
        (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 (k + 1))
        (ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 k) :=
  rfl

/-- Expanding the recursive `z`-step gives the displayed shifted soft-threshold formula from
Algorithm 15.13. -/
theorem ad_lpmm_l1_residual_z_succ_eq
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 (k + 1) =
      T_[1 / (ρ : ℝ)]
        (A (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 (k + 1)) - b +
          (1 / (ρ : ℝ)) • ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 k) + b := by
  rw [ad_lpmm_l1_residual_z_succ A ρ hL b x0 z0 y0 k]
  rw [admm_linear_composite_shifted_l1_z_update_eq]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- At every iteration `k`, the next multiplier iterate is the canonical ADMM affine update. -/
theorem ad_lpmm_l1_residual_y_succ
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 (k + 1) =
      admm_multiplier_update
        ρ
        A
        (-LinearMap.id)
        0
        (ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 k)
        (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 (k + 1))
        (ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 (k + 1)) :=
  rfl

/-- Expanding the recursive multiplier step gives the displayed affine update from
Algorithm 15.13. -/
theorem ad_lpmm_l1_residual_y_succ_eq
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 (k + 1) =
      ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0 k +
        (ρ : ℝ) •
          (A (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0 (k + 1)) -
            ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0 (k + 1)) := by
  rw [ad_lpmm_l1_residual_y_succ A ρ hL b x0 z0 y0 k,
    admm_multiplier_update_linear_composite_eq]

/-- The explicit Algorithm 15.13 iterates form the canonical linear-composite AD-LPMM trajectory
for `h₁ = 0` and `h₂(z) = l1n[z - b]`, under the source specialization `α = ρ L`
and `β = ρ`. -/
theorem ad_lpmm_l1_residual_trajectory
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun _ : X ↦ (0 : EReal))
      (admm_linear_composite_shifted_l1_regularizer b)
      (ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0)
      (ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0)
      (ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0)
      x0
      z0
      y0 where
  x_zero := ad_lpmm_l1_residual_x_zero A ρ hL b x0 z0 y0
  z_zero := ad_lpmm_l1_residual_z_zero A ρ hL b x0 z0 y0
  y_zero := ad_lpmm_l1_residual_y_zero A ρ hL b x0 z0 y0
  x_step k := by
    rw [mem_adlpmm_x_step_linear_composite_iff]
    have hzero :
        ((((1 / (ad_lpmm_alpha_parameter A ρ hL : PosReal) : PosReal) : EReal) •
          fun _ : X ↦ (0 : EReal)) : X → EReal) = 0 := by
      funext u
      simp
    rw [hzero, prox_zero_eq_singleton, Set.mem_singleton_iff]
    have hρ0 : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
    have hρα :
        (((ρ / (ad_lpmm_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) =
          (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) := by
      rw [PosReal.coe_div, ad_lpmm_alpha_parameter_coe]
      field_simp [hρ0]
    simpa [hρα] using ad_lpmm_l1_residual_x_succ A ρ hL b x0 z0 y0 k
  z_step k := by
    let x := ad_lpmm_l1_residual_x A ρ hL b x0 z0 y0
    let z := ad_lpmm_l1_residual_z A ρ hL b x0 z0 y0
    let y := ad_lpmm_l1_residual_y A ρ hL b x0 z0 y0
    let β : ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E) :=
      show ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E) from
        ad_lpmm_beta_parameter ρ
    rw [mem_adlpmm_z_step_linear_composite_iff]
    change admm_linear_composite_shifted_l1_z_update ρ A b (x (k + 1)) (y k) ∈
      prox[
        ((((1 / (β : PosReal) : PosReal) : EReal) •
          admm_linear_composite_shifted_l1_regularizer b))]
        (z k + (((ρ / (β : PosReal)) : PosReal) : ℝ) •
          (A (x (k + 1)) - z k + (1 / (ρ : ℝ)) • y k))
    have hρ0 : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
    have hβ :
        (((ρ / (β : PosReal)) : PosReal) : ℝ) = 1 := by
      simp [β, ad_lpmm_beta_parameter, PosReal.coe_div, hρ0]
    have hcenter :
        z k + (((ρ / (β : PosReal)) : PosReal) : ℝ) •
              (A (x (k + 1)) - z k + (1 / (ρ : ℝ)) • y k) =
          A (x (k + 1)) + (1 / (ρ : ℝ)) • y k := by
      rw [hβ]
      simp [sub_eq_add_neg]
      abel_nf
    rw [hcenter]
    simpa [x, y, β, ad_lpmm_beta_parameter] using
      admm_linear_composite_shifted_l1_z_update_mem_prox ρ A b (x (k + 1)) (y k)
  y_step := ad_lpmm_l1_residual_y_succ A ρ hL b x0 z0 y0

end

end

end
