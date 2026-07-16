import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable (n : ℕ)

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin (n - 1))

/- Algorithm 12.11 is `source-facing` in the subsection on one-dimensional total variation
denoising.

Domain sampling against the nearby project owners identifies:
- `one_dimensional_total_variation_dpg_primal_point` and
  `one_dimensional_total_variation_dpg_dual_update` from Algorithm 12.10 as the canonical owners
  of the shared step-(a) / step-(b) primitives for one-dimensional TV denoising;
- `fista_momentum_sequence` and `fista_momentum_update` from Algorithm 10.13 as the canonical
  Chapter 10 owners of the scalar recurrence `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`.

This separates the API into:
- `source-facing`: the named iterate families `u^k`, `y^k`, and `w^k`;
- `bridge/view`: the recursive iterate state, with the hidden bookkeeping convention `t_(-1) = 0`
  absorbed into the extrapolation coefficient derived from the canonical momentum owner.

The scalar sequence `t_k` itself is already owned upstream by `fista_momentum_sequence`, so this
file reuses that canonical owner directly on theorem surfaces instead of introducing a parallel
public momentum definition carrying the TV problem-data binders. Matching Algorithm 12.10, the
source-facing iterate owners keep the canonical signal-length parameter `n : ℕ` and the positive
regularization parameter `lam : PosReal`. -/

/- The FDPG acceleration scalars reuse the canonical Chapter 10 FISTA momentum owner. -/
recall fista_momentum_sequence
recall fista_momentum_sequence_zero
recall fista_momentum_sequence_succ

private structure OneDimensionalTotalVariationFDPGState (n : ℕ) where
  yCur : EuclideanSpace ℝ (Fin (n - 1))
  wCur : EuclideanSpace ℝ (Fin (n - 1))

local notation "State" => OneDimensionalTotalVariationFDPGState n

private def one_dimensional_total_variation_fdpg_initial_state (y0 : Em) : State :=
  { yCur := y0
    wCur := y0 }

private def one_dimensional_total_variation_fdpg_extrapolation_factor : ℕ → ℝ
  | 0 => 0
  | k + 1 => fista_momentum_sequence k / fista_momentum_sequence (k + 2)

private def one_dimensional_total_variation_fdpg_state_update
    (d : En) (lam : PosReal) (k : ℕ) (state : State) : State :=
  let u := one_dimensional_total_variation_dpg_primal_point n d state.wCur
  let yNext := one_dimensional_total_variation_dpg_dual_update n lam u state.wCur
  let coeff := one_dimensional_total_variation_fdpg_extrapolation_factor k
  { yCur := yNext
    wCur := yNext + coeff • (yNext - state.yCur) }

private def one_dimensional_total_variation_fdpg_state
    (d : En) (lam : PosReal) (y0 : Em) : ℕ → State
  | 0 => one_dimensional_total_variation_fdpg_initial_state n y0
  | k + 1 =>
      one_dimensional_total_variation_fdpg_state_update n d lam k
        (one_dimensional_total_variation_fdpg_state d lam y0 k)

/-- Algorithm 12.11: for the one-dimensional total variation denoising problem
`min_x { (1 / 2) ‖x - d‖_2^2 + λ ‖D x‖_1 }`, with signal length `n`, positive regularization
parameter `λ` encoded by `lam : PosReal`, and initialization `w⁰ = y⁰ = y0 ∈ ℝ^(n-1)`,
the iterate families below generate the FDPG recursion with
`u^k = Dᵀ w^k + d`,
`y^(k+1) = w^k - (1 / 4) D u^k + (1 / 4) T_[4 λ] (D u^k - 4 w^k)`,
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`,
and
`w^(k+1) = y^(k+1) + (t_(k-1) / t_(k+1)) (y^(k+1) - y^k)`,
implemented in Lean through the equivalent hidden initialization `t_(-1) = 0`. -/
def one_dimensional_total_variation_fdpg_y
    (d : En) (lam : PosReal) (y0 : Em) : ℕ → Em :=
  fun k ↦ (one_dimensional_total_variation_fdpg_state n d lam y0 k).yCur

/-- The one-dimensional TV FDPG extrapolated sequence `w^k`. -/
def one_dimensional_total_variation_fdpg_w
    (d : En) (lam : PosReal) (y0 : Em) : ℕ → Em :=
  fun k ↦ (one_dimensional_total_variation_fdpg_state n d lam y0 k).wCur

/-- The auxiliary primal sequence `u^k = Dᵀ w^k + d` derived from the one-dimensional TV FDPG
iterates. -/
def one_dimensional_total_variation_fdpg_u
    (d : En) (lam : PosReal) (y0 : Em) : ℕ → En :=
  fun k ↦
    one_dimensional_total_variation_dpg_primal_point n d
      (one_dimensional_total_variation_fdpg_w n d lam y0 k)

section

variable (d : En) (lam : PosReal) (y0 : Em)

local notation "y[" k "]" => one_dimensional_total_variation_fdpg_y n d lam y0 k
local notation "w[" k "]" => one_dimensional_total_variation_fdpg_w n d lam y0 k
local notation "t[" k "]" => fista_momentum_sequence k
local notation "u[" k "]" => one_dimensional_total_variation_fdpg_u n d lam y0 k

/-- The one-dimensional TV FDPG dual sequence starts from the prescribed initialization
`y⁰ = y0`. -/
theorem one_dimensional_total_variation_fdpg_y_zero :
    y[0] = y0 := rfl

/-- The one-dimensional TV FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
theorem one_dimensional_total_variation_fdpg_w_zero :
    w[0] = y0 := rfl

/-- At every iteration `k`, the auxiliary point satisfies the step-(a) formula
`u^k = Dᵀ w^k + d`. -/
theorem one_dimensional_total_variation_fdpg_u_eq
    (k : ℕ) :
    u[k] = Dᵀ[n] (w[k]) + d :=
  rfl

/-- At every iteration `k`, the next dual iterate is obtained from the shared one-dimensional TV
DPG dual-update owner evaluated at `u^k` and `w^k`. -/
theorem one_dimensional_total_variation_fdpg_y_succ
    (k : ℕ) :
    y[k + 1] = one_dimensional_total_variation_dpg_dual_update n lam u[k] w[k] :=
  rfl

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem one_dimensional_total_variation_fdpg_w_one :
    w[1] = y[1] := by
  simp only [one_dimensional_total_variation_fdpg_w, one_dimensional_total_variation_fdpg_y,
    one_dimensional_total_variation_fdpg_state, one_dimensional_total_variation_fdpg_state_update,
    one_dimensional_total_variation_fdpg_initial_state,
    one_dimensional_total_variation_fdpg_extrapolation_factor, zero_smul, add_zero]

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook recursion
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`, where `t_k` is the canonical Chapter
10 FISTA momentum sequence. -/
theorem one_dimensional_total_variation_fdpg_w_succ_succ
    (k : ℕ) :
    w[k + 2] =
      y[k + 2] +
        (t[k] / t[k + 2]) •
          (y[k + 2] - y[k + 1]) :=
  rfl

end

end
