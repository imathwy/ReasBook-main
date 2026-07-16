import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Definition_12_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_9
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace
open scoped SoftThreshold

universe u v

section

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- `lean_leansearch` is unavailable in this environment, so the owner/API choice was verified
against the local Chapter 15 AD-LPMM files (`Algorithm_15_5`, `Algorithm_15_8`, `Algorithm_15_9`)
and the Chapter 6 soft-threshold notation.

This item is `source-facing`: Algorithm 15.10 gives the concrete AD-LPMM specialization
`α = ρ L`, `β = ρ`, with `L = λ_max(Aᵀ A)`, together with explicit recursions for
`x^(k+1)`, `z^(k+1)`, and `y^(k+1)`. The public surface here therefore keeps:
- the exact Chapter 15 parameter choices `ad_lpmm_alpha_parameter` and
  `ad_lpmm_beta_parameter`;
- the explicit soft-thresholded `x`-update;
- the recursive iterate families `ad_lpmm_x`, `ad_lpmm_z`, and `ad_lpmm_y`;
- bridge theorems connecting those explicit recursions to the canonical linear-composite
  AD-LPMM owners from Algorithms 15.5, 15.8, and 15.9. -/

/-- Positivity of the exact Algorithm 15.10 choice `α = ρ L`. -/
theorem ad_lpmm_alpha_pos
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    0 < (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := sorry

/-- The exact Algorithm 15.10 choice `α = ρ L` is admissible for the generic AD-LPMM
`x`-linearization bound. -/
theorem ad_lpmm_alpha_admissible
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) :
    adlpmm_linearization_bound ρ A ≤
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := sorry

/-- The Algorithm 15.10 choice `α = ρ L` as the canonical Chapter 15 `x`-linearization
parameter. -/
def ad_lpmm_alpha_parameter
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ADLPMMLinearizationParameter ρ A :=
  ⟨⟨(ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A, ad_lpmm_alpha_pos A ρ hL⟩,
    ad_lpmm_alpha_admissible A ρ⟩

/-- Coercing the canonical Algorithm 15.10 `x`-linearization parameter to `ℝ` returns
`α = ρ L`. -/
@[simp] theorem ad_lpmm_alpha_parameter_coe
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) =
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A :=
  rfl

end

section

variable {Y : Type v}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The Algorithm 15.10 choice `β = ρ` as the canonical Chapter 15 `z`-linearization
parameter for the linear-composite specialization `B = -I`. -/
def ad_lpmm_beta_parameter
    (ρ : PosReal) :
    ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y) :=
  ⟨ρ, adlpmm_linearization_bound_neg_id_le ρ⟩

/-- Coercing the canonical Algorithm 15.10 `z`-linearization parameter to `PosReal` returns
`β = ρ`. -/
@[simp] theorem ad_lpmm_beta_parameter_coe
    (ρ : PosReal) :
    ((ad_lpmm_beta_parameter ρ :
        ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)) : PosReal) = ρ :=
  rfl

end

section

variable {ι : Type u} {Y : Type v}
variable [Fintype ι]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

local notation "X" => EuclideanSpace ℝ ι

/-- The explicit soft-thresholding `x`-update used by Algorithm 15.10. -/
def ad_lpmm_x_update
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (xk : X) (zk yk : Y) : X :=
  T_[((lam : ℝ) / (adlpmm_linearization_bound (1 : PosReal) A * (ρ : ℝ)))]
    (xk - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
      A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk))

end

section

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

local notation "X" => EuclideanSpace ℝ ι
local notation "Y" => EuclideanSpace ℝ κ

/-- The recursive internal Algorithm 15.10 state sequence. -/
private def iterateState
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → X × Y × Y
  | 0 => (x0, z0, y0)
  | k + 1 =>
      let ⟨xk, zk, yk⟩ := iterateState A ρ lam b x0 z0 y0 k
      let xNext := ad_lpmm_x_update A ρ lam xk zk yk
      let zNext := l1_regularized_least_squares_admm_v2_z_update A b ρ xNext yk
      (xNext, zNext, admm_multiplier_update ρ A (-LinearMap.id) 0 yk xNext zNext)

/-- The `x`-iterate sequence from Algorithm 15.10. -/
def ad_lpmm_x
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → X :=
  fun k ↦
    let ⟨xk, _, _⟩ := iterateState A ρ lam b x0 z0 y0 k
    xk

/-- The `z`-iterate sequence from Algorithm 15.10. -/
def ad_lpmm_z
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → Y :=
  fun k ↦
    let ⟨_, zk, _⟩ := iterateState A ρ lam b x0 z0 y0 k
    zk

/-- The multiplier sequence from Algorithm 15.10. -/
def ad_lpmm_y
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → Y :=
  fun k ↦
    let ⟨_, _, yk⟩ := iterateState A ρ lam b x0 z0 y0 k
    yk

section

/-- The Algorithm 15.10 `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_x_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_x A ρ lam b x0 z0 y0 0 = x0 :=
  rfl

/-- The Algorithm 15.10 `z`-sequence starts from `z^0 = z0`. -/
theorem ad_lpmm_z_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_z A ρ lam b x0 z0 y0 0 = z0 :=
  rfl

/-- The Algorithm 15.10 multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_y_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_y A ρ lam b x0 z0 y0 0 = y0 :=
  rfl

/-- The recursive `x`-iterate is obtained by applying the explicit soft-thresholding
one-step update to the previous state. -/
theorem ad_lpmm_x_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1) =
      ad_lpmm_x_update
        A
        ρ
        lam
        (ad_lpmm_x A ρ lam b x0 z0 y0 k)
        (ad_lpmm_z A ρ lam b x0 z0 y0 k)
        (ad_lpmm_y A ρ lam b x0 z0 y0 k) :=
  rfl

/-- Algorithm 15.10 (1): at every iteration `k`, the next `x`-iterate is the displayed
soft-thresholding update
`x^(k+1) = T_[λ / (L ρ)] (x^k - (1 / L) Aᵀ (A x^k - z^k + (1 / ρ) y^k))`. -/
theorem ad_lpmm_x_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1) =
      T_[((lam : ℝ) / (adlpmm_linearization_bound (1 : PosReal) A * (ρ : ℝ)))]
        (ad_lpmm_x A ρ lam b x0 z0 y0 k -
          (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
            A.adjoint
              (A (ad_lpmm_x A ρ lam b x0 z0 y0 k) -
                ad_lpmm_z A ρ lam b x0 z0 y0 k +
                (1 / (ρ : ℝ)) • ad_lpmm_y A ρ lam b x0 z0 y0 k)) := by
  simpa [ad_lpmm_x_update] using ad_lpmm_x_succ A ρ lam b x0 z0 y0 k

/-- The recursive `z`-iterate is obtained by applying the shared least-squares affine-average
update to the current `x^(k+1)` and `y^k`. -/
theorem ad_lpmm_z_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_z A ρ lam b x0 z0 y0 (k + 1) =
      l1_regularized_least_squares_admm_v2_z_update
        A
        b
        ρ
        (ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1))
        (ad_lpmm_y A ρ lam b x0 z0 y0 k) :=
  rfl

/-- Algorithm 15.10 (2): at every iteration `k`, the next `z`-iterate satisfies
`z^(k+1) = (ρ A x^(k+1) + y^k + b) / (ρ + 1)`. -/
theorem ad_lpmm_z_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_z A ρ lam b x0 z0 y0 (k + 1) =
      (1 / ((ρ : ℝ) + 1)) •
        ((ρ : ℝ) • A (ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1)) +
          ad_lpmm_y A ρ lam b x0 z0 y0 k + b) := by
  simpa using
    (ad_lpmm_z_succ A ρ lam b x0 z0 y0 k).trans
      (l1_regularized_least_squares_admm_v2_z_update_eq
        A
        b
        ρ
        (ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1))
        (ad_lpmm_y A ρ lam b x0 z0 y0 k))

/-- The recursive multiplier iterate is obtained by the canonical linear-composite ADMM
multiplier update specialized to `A x - z = 0`. -/
theorem ad_lpmm_y_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_y A ρ lam b x0 z0 y0 (k + 1) =
      admm_multiplier_update
        ρ
        A
        (-LinearMap.id)
        0
        (ad_lpmm_y A ρ lam b x0 z0 y0 k)
        (ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1))
        (ad_lpmm_z A ρ lam b x0 z0 y0 (k + 1)) :=
  rfl

/-- Algorithm 15.10 (3): at every iteration `k`, the multiplier update is
`y^(k+1) = y^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem ad_lpmm_y_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_y A ρ lam b x0 z0 y0 (k + 1) =
      ad_lpmm_y A ρ lam b x0 z0 y0 k +
        (ρ : ℝ) •
          (A (ad_lpmm_x A ρ lam b x0 z0 y0 (k + 1)) -
            ad_lpmm_z A ρ lam b x0 z0 y0 (k + 1)) := by
  rw [ad_lpmm_y_succ]
  simp [admm_multiplier_update, sub_eq_add_neg]

end

/-- The explicit Algorithm 15.10 `x`-update belongs to the corresponding linear-composite
AD-LPMM `x`-step with `α = ρ L`. -/
theorem ad_lpmm_x_update_mem_adlpmm_x_step
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : X) (zk yk : Y) :
    ad_lpmm_x_update A ρ lam xk zk yk ∈
      adlpmm_x_step
        (fun x : X ↦ ((((lam : ℝ) * ‖x‖₁ : ℝ)) : EReal))
        ρ
        (ad_lpmm_alpha_parameter A ρ hL : PosReal)
        A
        (-LinearMap.id)
        0
        xk
        zk
        yk := sorry

/-- The explicit least-squares affine-average update used in Algorithm 15.10 belongs to the
corresponding linear-composite AD-LPMM `z`-step with `β = ρ`. -/
theorem ad_lpmm_z_update_mem_adlpmm_z_step
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (b : Y) (xNext : X) (zk yk : Y) :
    l1_regularized_least_squares_admm_v2_z_update A b ρ xNext yk ∈
      adlpmm_z_step
        (denoising_data_fidelity b)
        ρ
        ρ
        A
        (-LinearMap.id)
        0
        xNext
        zk
        yk := sorry

/-- The explicit Algorithm 15.10 iterates form the canonical linear-composite AD-LPMM trajectory
with `α = ρ L` and `β = ρ`. -/
theorem ad_lpmm_trajectory
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun x : X ↦ ((((lam : ℝ) * ‖x‖₁ : ℝ)) : EReal))
      (denoising_data_fidelity b)
      (ad_lpmm_x A ρ lam b x0 z0 y0)
      (ad_lpmm_z A ρ lam b x0 z0 y0)
      (ad_lpmm_y A ρ lam b x0 z0 y0)
      x0
      z0
      y0 := sorry

end
