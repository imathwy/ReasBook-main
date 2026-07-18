import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Algorithm_15_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold

universe u v

section

variable {Y : Type u} {ι : Type v}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled directly from the
nearby Chapter 15 AD-LPMM basis-pursuit files together with the Chapter 2 indicator owner and the
Chapter 6 proximal/projection bridge.

This item is `source-facing`: Algorithm 15.14 keeps only the explicit `x`- and `y`-recursions
for the basis-pursuit specialization of AD-LPMM. The sampled declarations in this domain are:
- `adlpmm_linearization_bound` from Algorithm 15.5 for the canonical realization
  `L = λ_max(Aᵀ A) = ‖A‖²`;
- `IsADLPMMTrajectory` from Algorithm 15.5 and its linear-composite specialization API from
  Algorithm 15.8 as the chapter owner for the ambient AD-LPMM recursion;
- `adlpmm_x_step` from Algorithm 15.5 together with
  `mem_adlpmm_x_step_linear_composite_iff` from Algorithm 15.8 as the chapter owner of the
  linear-composite `x`-update set;
- `ad_lpmm_x_update` from Algorithm 15.10 as the chapter owner of the explicit soft-thresholded
  `x`-step, with basis pursuit obtained by the source specialization `λ = 1` and `z^k = b`;
- `admm_multiplier_update` and `admm_multiplier_update_linear_composite_eq` from Algorithms 15.2
  and 15.6 for the affine multiplier step specialized to `B = -I`, `c = 0`, and `z^(k+1) = b`;
- `extendedIndicator` from Definition 2.2 and `prox_extendedIndicator_eq_projection_mapping` from
  Definition 2.2 for the singleton indicator `h₂ = δ_{ {b} }` encoding the fixed-`z` branch.

The source-facing primitive public data are therefore just the recursive basis-pursuit iterate
families with initial values `x^0 = x0`, `y^0 = y0`; the fixed `z^k = b` branch is derived API,
best exposed as the canonical Chapter 15 trajectory bridge with `z = fun _ ↦ b` and
`h₂ = extendedIndicator {b}` rather than by a parallel local wrapper. The positivity hypothesis
`hL : 0 < adlpmm_linearization_bound (1 : PosReal) A` is needed only for that canonical
`IsADLPMMTrajectory` bridge and the inherited `x`-step owner, not for the recursion itself. -/

private def basisPursuitState
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) :
    ℕ → E × Y
  | 0 => (x0, y0)
  | k + 1 =>
      let statek := basisPursuitState ρ A b x0 y0 k
      let xNext := ad_lpmm_x_update A ρ (1 : NNReal) statek.1 b statek.2
      (xNext, admm_multiplier_update ρ A (-LinearMap.id) 0 statek.2 xNext b)

/-- Algorithm 15.14: the basis-pursuit `x`-iterates obtained by recursively applying the
soft-thresholded Chapter 15 `x`-update with `λ = 1` and `z^k = b`. -/
def ad_lpmm_basis_pursuit_x
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) :
    ℕ → E :=
  fun k ↦ (basisPursuitState ρ A b x0 y0 k).1

/-- Algorithm 15.14: the basis-pursuit multiplier iterates obtained by recursively applying the
canonical affine multiplier update with `z^k = b`. -/
def ad_lpmm_basis_pursuit_y
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) :
    ℕ → Y :=
  fun k ↦ (basisPursuitState ρ A b x0 y0 k).2

private theorem prox_extendedIndicator_singleton_eq
    (b center : Y) :
    prox[extendedIndicator ({b} : Set Y)] center = {b} := by
  have hb : b ∈ prox[extendedIndicator ({b} : Set Y)] center := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro z
    by_cases hz : z = b
    · simp [proximal_objective, extendedIndicator, hz]
    · have htop :
          proximal_objective (extendedIndicator ({b} : Set Y)) center z = ⊤ := by
        calc
          proximal_objective (extendedIndicator ({b} : Set Y)) center z =
              (⊤ : EReal) + (((((1 / 2 : ℝ) * ‖z - center‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
                simp [proximal_objective, extendedIndicator, hz]
          _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
      rw [htop]
      exact le_top
  ext z
  constructor
  · intro hz
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hz
    by_contra hzb
    have htop :
        proximal_objective (extendedIndicator ({b} : Set Y)) center z = ⊤ := by
      calc
        proximal_objective (extendedIndicator ({b} : Set Y)) center z =
            (⊤ : EReal) + (((((1 / 2 : ℝ) * ‖z - center‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
              simp [proximal_objective, extendedIndicator, hzb]
        _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    have hbfin :
        proximal_objective (extendedIndicator ({b} : Set Y)) center b =
          ((((1 / 2 : ℝ) * ‖b - center‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      simp [proximal_objective, extendedIndicator]
    have hle := hz b
    rw [htop, hbfin] at hle
    have hnot :
        ¬ ((⊤ : EReal) ≤ ((((1 / 2 : ℝ) * ‖b - center‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
      simpa [top_le_iff] using
        (EReal.coe_ne_top (((1 / 2 : ℝ) * ‖b - center‖ ^ (2 : ℕ))))
    exact (hnot hle).elim
  · intro hz
    simpa [Set.mem_singleton_iff.mp hz] using hb

private theorem smul_extendedIndicator_singleton
    (μ : PosReal) (b : Y) :
    ((((1 / μ : PosReal) : EReal) • extendedIndicator ({b} : Set Y)) : Y → EReal) =
      extendedIndicator ({b} : Set Y) := by
  funext z
  by_cases hz : z = b
  · simp [extendedIndicator, hz]
  · have hμinv : 0 < ((μ : ℝ)⁻¹) := inv_pos.mpr μ.2
    simp [extendedIndicator, hz, EReal.coe_mul_top_of_pos hμinv]

section

/-- The basis-pursuit `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_basis_pursuit_x_zero
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) :
    ad_lpmm_basis_pursuit_x ρ A b x0 y0 0 = x0 :=
  rfl

/-- The basis-pursuit multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_basis_pursuit_y_zero
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) :
    ad_lpmm_basis_pursuit_y ρ A b x0 y0 0 = y0 :=
  rfl

/-- At every iteration `k`, the next basis-pursuit `x`-iterate is the canonical Chapter 15
soft-thresholding update specialized to `λ = 1` and `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_x_succ
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A b x0 y0 (k + 1) =
      ad_lpmm_x_update
        A
        ρ
        (1 : NNReal)
        (ad_lpmm_basis_pursuit_x ρ A b x0 y0 k)
        b
        (ad_lpmm_basis_pursuit_y ρ A b x0 y0 k) :=
  rfl

/-- The next basis-pursuit `x`-iterate belongs to the canonical Chapter 15 linear-composite
AD-LPMM `x`-step set specialized to the `ℓ¹` term and the fixed value `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_x_succ_mem_adlpmm_x_step
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (h : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A b x0 y0 (k + 1) ∈
      adlpmm_x_step
        (fun x : E ↦ ((l1n[x] : ℝ) : EReal))
        ρ
        (ad_lpmm_alpha_parameter A ρ h : PosReal)
        A
        (-LinearMap.id)
        0
        (ad_lpmm_basis_pursuit_x ρ A b x0 y0 k)
        b
        (ad_lpmm_basis_pursuit_y ρ A b x0 y0 k) := by
  sorry

/-- Expanding the recursive basis-pursuit `x`-step gives the textbook soft-thresholding formula
from Algorithm 15.14. -/
theorem ad_lpmm_basis_pursuit_x_succ_eq
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A b x0 y0 (k + 1) =
      T_[((1 : ℝ) / (adlpmm_linearization_bound (1 : PosReal) A * (ρ : ℝ)))]
        (ad_lpmm_basis_pursuit_x ρ A b x0 y0 k -
          (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
            A.adjoint
              (A (ad_lpmm_basis_pursuit_x ρ A b x0 y0 k) - b +
                (1 / (ρ : ℝ)) • ad_lpmm_basis_pursuit_y ρ A b x0 y0 k)) := by
  simp [ad_lpmm_basis_pursuit_x_succ, ad_lpmm_x_update]

/-- At every iteration `k`, the next basis-pursuit multiplier iterate is the canonical affine
multiplier update specialized to `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_y_succ
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_y ρ A b x0 y0 (k + 1) =
      admm_multiplier_update
        ρ
        A
        (-LinearMap.id)
        0
        (ad_lpmm_basis_pursuit_y ρ A b x0 y0 k)
        (ad_lpmm_basis_pursuit_x ρ A b x0 y0 (k + 1))
        b :=
  rfl

/-- Expanding the recursive basis-pursuit multiplier step gives the textbook affine formula
`y^(k+1) = y^k + ρ (A x^(k+1) - b)`. -/
theorem ad_lpmm_basis_pursuit_y_succ_eq
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_y ρ A b x0 y0 (k + 1) =
      ad_lpmm_basis_pursuit_y ρ A b x0 y0 k +
        (ρ : ℝ) • (A (ad_lpmm_basis_pursuit_x ρ A b x0 y0 (k + 1)) - b) := by
  rw [ad_lpmm_basis_pursuit_y_succ, admm_multiplier_update_linear_composite_eq]

/-- The explicit Algorithm 15.14 basis-pursuit iterates form the canonical linear-composite
AD-LPMM trajectory with `h₁ x = l1n[x]`, `h₂ = δ_{ {b} }`, `α = ρ L`, and the fixed
`z^k = b`. -/
theorem ad_lpmm_basis_pursuit_trajectory
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (x0 : E) (y0 : Y) :
    IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun x : E ↦ ((l1n[x] : ℝ) : EReal))
      (extendedIndicator ({b} : Set Y))
      (ad_lpmm_basis_pursuit_x ρ A b x0 y0)
      (fun _ ↦ b)
      (ad_lpmm_basis_pursuit_y ρ A b x0 y0)
      x0
      b
      y0 where
  x_zero := ad_lpmm_basis_pursuit_x_zero ρ A b x0 y0
  z_zero := rfl
  y_zero := ad_lpmm_basis_pursuit_y_zero ρ A b x0 y0
  x_step k := ad_lpmm_basis_pursuit_x_succ_mem_adlpmm_x_step ρ A b hL x0 y0 k
  z_step k := by
    let x := ad_lpmm_basis_pursuit_x ρ A b x0 y0
    let y := ad_lpmm_basis_pursuit_y ρ A b x0 y0
    let β : ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y) :=
      show ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y) from
        ad_lpmm_beta_parameter ρ
    rw [mem_adlpmm_z_step_linear_composite_iff]
    change b ∈
      prox[((((1 / (β : PosReal) : PosReal) : EReal) • extendedIndicator ({b} : Set Y)))]
        (b + (((ρ / (β : PosReal)) : PosReal) : ℝ) •
          (A (x (k + 1)) - b + (1 / (ρ : ℝ)) • y k))
    have hβ :
        (((ρ / (β : PosReal)) : PosReal) : ℝ) = 1 := by
      have hρ0 : (ρ : ℝ) ≠ 0 := ρ.2.ne'
      simp [β, ad_lpmm_beta_parameter, PosReal.coe_div, hρ0]
    have hcenter :
        b + (((ρ / (β : PosReal)) : PosReal) : ℝ) •
              (A (x (k + 1)) - b + (1 / (ρ : ℝ)) • y k) =
          A (x (k + 1)) + (1 / (ρ : ℝ)) • y k := by
      rw [hβ]
      simp [sub_eq_add_neg]
      abel_nf
    rw [smul_extendedIndicator_singleton (β : PosReal) b, hcenter,
      prox_extendedIndicator_singleton_eq]
    simp
  y_step := ad_lpmm_basis_pursuit_y_succ ρ A b x0 y0

end

end
