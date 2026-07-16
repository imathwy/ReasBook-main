import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Definition_12_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Proposition_12_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open WithLp

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ
local notation "Pmn" => Matrix (Fin m) (Fin (n - 1)) ℝ
local notation "Qmn" => Matrix (Fin (m - 1)) (Fin n) ℝ
local notation "TVSpace" => WithLp 2 (Pmn × Qmn)

local instance : NormedAddCommGroup Mmn := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ Mmn := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ Mmn := Matrix.frobeniusInnerProductSpace

local instance : NormedAddCommGroup Pmn := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ Pmn := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ Pmn := Matrix.frobeniusInnerProductSpace

local instance : NormedAddCommGroup Qmn := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ Qmn := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ Qmn := Matrix.frobeniusInnerProductSpace

/-
This item is `source-facing`: the textbook gives an explicit accelerated dual recursion for the
two-dimensional anisotropic total-variation denoising model with `g = λ TV_l1`.

Domain sampling against the nearby Chapter 12 API identifies:
- `two_dimensional_total_variation_denoising_objective` from Definition 12.12 as the canonical
  owner of the two-dimensional TV denoising model and of its positive regularization parameter
  `lam : PosReal`;
- `fista_momentum_update` from Algorithm 10.13 as the canonical owner of the scalar recursion
  `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `A[m, n]` and `Aᵀ[m, n]` from Proposition 12.4 as the canonical owner notation for the
  two-dimensional TV operator and its adjoint, together with the Proposition 12.5 companion
  coordinate formula `two_dimensional_total_variation_difference_adjoint_toLp_apply`;
- `two_dimensional_total_variation_horizontal_difference` and
  `two_dimensional_total_variation_vertical_difference` from Proposition 12.4 as the canonical
  owners of the horizontal and vertical finite differences in step (b);
- the recursive-state pattern from Algorithms 12.6 and 12.11 as the right owner shape for the
  explicit FDPG iteration.

The source gives concrete matrix recursions for `u^k`, `p^(k+1)`, `q^(k+1)`, `t_(k+1)`,
`\tilde p^(k+1)`, and `\tilde q^(k+1)`. The public API therefore keeps the genuinely
source-facing matrix sequences visible, while the hidden state carrying the bookkeeping convention
`t_(-1) = 0` remains only an internal bridge to the Chapter 10 owner
`fista_momentum_sequence`. Matching Definition 12.12, the denoising parameter stays on the
chapter's positive owner `lam : PosReal` rather than a bare real scalar. -/

/-- The auxiliary primal image `u = Aᵀ z + d` used in step (a) of the two-dimensional anisotropic
TV FDPG method, where `z` is the canonical `L²` dual pair in
`WithLp 2 (ℝ^(m × (n - 1)) × ℝ^((m - 1) × n))`. Proposition 12.5 supplies the equivalent
zero-padded divergence formula for the owner-level adjoint term. -/
def two_dimensional_tv_l1_fdpg_primal_point
    (d : Mmn) (z : TVSpace) : Mmn :=
  Aᵀ[m, n] z + d

-- Proof sketch: unfold `two_dimensional_tv_l1_fdpg_primal_point`; matrix addition is pointwise,
-- so each entry is the canonical adjoint term `Aᵀ z` plus `d i j`.
/-- Evaluating the auxiliary primal image gives the step-(a) formula
`u = Aᵀ z + d` through the canonical adjoint owner notation from Proposition 12.4. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_primal_point_apply
    (d : Mmn) (z : TVSpace) (i : Fin m) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_primal_point d z i j =
      Aᵀ[m, n] z i j + d i j := rfl

-- Proof sketch: specialize `two_dimensional_tv_l1_fdpg_primal_point_apply` to the canonical
-- `L²` dual pair `toLp 2 (p, q)`.
/-- Evaluating the auxiliary primal image at the textbook dual pair `(p, q)` gives the step-(a)
formula `u = Aᵀ (p, q) + d`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_primal_point_toLp_apply
    (d : Mmn) (p : Pmn) (q : Qmn) (i : Fin m) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_primal_point d (toLp 2 (p, q)) i j =
      Aᵀ[m, n] (toLp 2 (p, q)) i j + d i j := rfl

/-- The step-(b) dual update on the canonical `L²` dual pair owner: starting from the current
extrapolated dual point `z = (p, q)`, subtract `(1 / 8) A u` and add the anisotropic proximal
point of the shifted dual residual `A u - 8 z`. The textbook `p`- and `q`-updates are recovered
as the `.fst` and `.snd` projections of this owner-level map, with the positive denoising
parameter carried canonically by `lam : PosReal`. -/
def two_dimensional_tv_l1_fdpg_dual_update
    (lam : PosReal) (u : Mmn) (z : TVSpace) : TVSpace :=
  let Au := A[m, n] u
  z - (1 / 8 : ℝ) • Au +
    (1 / 8 : ℝ) •
      two_dimensional_total_variation_anisotropic_prox_point
        ((8 : ℝ) * lam)
        (Au.fst - (8 : ℝ) • z.fst)
        (Au.snd - (8 : ℝ) • z.snd)

-- Proof sketch: unfold `two_dimensional_tv_l1_fdpg_dual_update`; the first coordinate is the
-- horizontal component of `A u` corrected by the anisotropic proximal owner from Proposition 12.4.
/-- Evaluating the first coordinate of the owner-level dual update gives the explicit step-(b)
formula for the horizontal block `p^(k+1)`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_dual_update_fst_apply
    (lam : PosReal) (u : Mmn) (z : TVSpace) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_tv_l1_fdpg_dual_update lam u z).fst i j =
      z.fst i j - (1 / 8 : ℝ) * two_dimensional_total_variation_horizontal_difference u i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] (two_dimensional_total_variation_horizontal_difference u i j -
            8 * z.fst i j) := by
  simp [two_dimensional_tv_l1_fdpg_dual_update]

-- Proof sketch: unfold `two_dimensional_tv_l1_fdpg_dual_update`; the second coordinate is the
-- vertical component of `A u` corrected by the anisotropic proximal owner from Proposition 12.4.
/-- Evaluating the second coordinate of the owner-level dual update gives the explicit step-(b)
formula for the vertical block `q^(k+1)`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_dual_update_snd_apply
    (lam : PosReal) (u : Mmn) (z : TVSpace) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_tv_l1_fdpg_dual_update lam u z).snd i j =
      z.snd i j - (1 / 8 : ℝ) * two_dimensional_total_variation_vertical_difference u i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] (two_dimensional_total_variation_vertical_difference u i j -
            8 * z.snd i j) := by
  simp [two_dimensional_tv_l1_fdpg_dual_update]

private structure TwoDimensionalTVL1FDPGState (m n : ℕ) where
  zCur : WithLp 2
    (Matrix (Fin m) (Fin (n - 1)) ℝ × Matrix (Fin (m - 1)) (Fin n) ℝ)
  zExtrap : WithLp 2
    (Matrix (Fin m) (Fin (n - 1)) ℝ × Matrix (Fin (m - 1)) (Fin n) ℝ)

local notation "State" => TwoDimensionalTVL1FDPGState m n

private def two_dimensional_tv_l1_fdpg_initial_state
    (p0 : Pmn) (q0 : Qmn) : State :=
  let z0 := toLp 2 (p0, q0)
  { zCur := z0
    zExtrap := z0 }

private def two_dimensional_tv_l1_fdpg_extrapolation_factor : ℕ → ℝ
  | 0 => 0
  | k + 1 => fista_momentum_sequence k / fista_momentum_sequence (k + 2)

private def two_dimensional_tv_l1_fdpg_state_update
    (d : Mmn) (lam : PosReal) (k : ℕ) (state : State) : State :=
  let u := two_dimensional_tv_l1_fdpg_primal_point d state.zExtrap
  let zNext := two_dimensional_tv_l1_fdpg_dual_update lam u state.zExtrap
  let coeff := two_dimensional_tv_l1_fdpg_extrapolation_factor k
  { zCur := zNext
    zExtrap := zNext + coeff • (zNext - state.zCur) }

/-- Algorithm 12.12: for the two-dimensional total-variation denoising problem
`min_x { (1 / 2) ‖x - d‖_F^2 + λ TV_l1(x) }`, given initial dual blocks
`\tilde p⁰ = p⁰ = p0 ∈ ℝ^(m × (n - 1))`,
`\tilde q⁰ = q⁰ = q0 ∈ ℝ^((m - 1) × n)`, positive regularization parameter `λ` encoded by
`lam : PosReal`, and `t₀ = 1`,
the iterate families below generate the FDPG recursion with step-(a) primal image
`u^k = Aᵀ (\tilde p^k, \tilde q^k) + d`, step-(b) horizontal and vertical thresholded updates,
and step-(d) extrapolated blocks `\tilde p^(k+1)` and `\tilde q^(k+1)`, while the scalar
recursion for `t_k` is reused directly from the Chapter 10 owner `fista_momentum_sequence`. -/
private def two_dimensional_tv_l1_fdpg_state
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → State
  | 0 => two_dimensional_tv_l1_fdpg_initial_state p0 q0
  | k + 1 =>
      two_dimensional_tv_l1_fdpg_state_update d lam k
        (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k)

/-- The canonical dual-pair sequence `z^k = (p^k, q^k)` in the `L²` product owner
`WithLp 2 (ℝ^(m × (n - 1)) × ℝ^((m - 1) × n))`. -/
def two_dimensional_tv_l1_fdpg_z
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → TVSpace :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k).zCur

/-- The canonical extrapolated dual-pair sequence
`\tilde z^k = (\tilde p^k, \tilde q^k)` in the `L²` product owner. -/
def two_dimensional_tv_l1_fdpg_zExtrap
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → TVSpace :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k).zExtrap

/-- The horizontal dual iterate sequence `p^k` extracted from the two-dimensional TV-L1 FDPG
state recursion. -/
def two_dimensional_tv_l1_fdpg_p
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → Pmn :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_z d lam p0 q0 k).fst

/-- The vertical dual iterate sequence `q^k` extracted from the two-dimensional TV-L1 FDPG state
recursion. -/
def two_dimensional_tv_l1_fdpg_q
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → Qmn :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_z d lam p0 q0 k).snd

/-- The extrapolated horizontal sequence `\tilde p^k` extracted from the two-dimensional TV-L1
FDPG state recursion. -/
def two_dimensional_tv_l1_fdpg_pExtrap
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → Pmn :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k).fst

/-- The extrapolated vertical sequence `\tilde q^k` extracted from the two-dimensional TV-L1 FDPG
state recursion. -/
def two_dimensional_tv_l1_fdpg_qExtrap
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → Qmn :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k).snd

/-- The auxiliary primal sequence `u^k = Aᵀ (\tilde p^k, \tilde q^k) + d` derived from the
two-dimensional TV-L1 FDPG iterates. -/
def two_dimensional_tv_l1_fdpg_u
    (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn) : ℕ → Mmn :=
  fun k ↦
    two_dimensional_tv_l1_fdpg_primal_point d
      (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k)

section

variable (d : Mmn) (lam : PosReal) (p0 : Pmn) (q0 : Qmn)

local notation "z[" k "]" => two_dimensional_tv_l1_fdpg_z d lam p0 q0 k
local notation "z̃[" k "]" => two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k
local notation "p[" k "]" => two_dimensional_tv_l1_fdpg_p d lam p0 q0 k
local notation "q[" k "]" => two_dimensional_tv_l1_fdpg_q d lam p0 q0 k
local notation "p̃[" k "]" => two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 k
local notation "q̃[" k "]" => two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 k
local notation "t[" k "]" => fista_momentum_sequence k
local notation "u[" k "]" => two_dimensional_tv_l1_fdpg_u d lam p0 q0 k

/-- The canonical dual-pair sequence starts from `z⁰ = (p0, q0)`. -/
theorem two_dimensional_tv_l1_fdpg_z_zero :
    z[0] = toLp 2 (p0, q0) := rfl

/-- The horizontal dual sequence starts at the prescribed initialization `p⁰ = p0`. -/
theorem two_dimensional_tv_l1_fdpg_p_zero :
    p[0] = p0 := by
  simpa [two_dimensional_tv_l1_fdpg_p] using
    congrArg (fun z ↦ z.fst) (two_dimensional_tv_l1_fdpg_z_zero d lam p0 q0)

/-- The vertical dual sequence starts at the prescribed initialization `q⁰ = q0`. -/
theorem two_dimensional_tv_l1_fdpg_q_zero :
    q[0] = q0 := by
  simpa [two_dimensional_tv_l1_fdpg_q] using
    congrArg (fun z ↦ z.snd) (two_dimensional_tv_l1_fdpg_z_zero d lam p0 q0)

/-- The canonical extrapolated dual-pair sequence starts from `\tilde z⁰ = (p0, q0)`. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_zero :
    z̃[0] = toLp 2 (p0, q0) := rfl

/-- The extrapolated horizontal sequence satisfies `\tilde p⁰ = p0`. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_zero :
    p̃[0] = p0 := by
  simpa [two_dimensional_tv_l1_fdpg_pExtrap] using
    congrArg (fun z ↦ z.fst) (two_dimensional_tv_l1_fdpg_zExtrap_zero d lam p0 q0)

/-- The extrapolated vertical sequence satisfies `\tilde q⁰ = q0`. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_zero :
    q̃[0] = q0 := by
  simpa [two_dimensional_tv_l1_fdpg_qExtrap] using
    congrArg (fun z ↦ z.snd) (two_dimensional_tv_l1_fdpg_zExtrap_zero d lam p0 q0)

/-- At every iteration `k`, the auxiliary image satisfies the step-(a) formula
`u^k = Aᵀ \tilde z^k + d` through the canonical adjoint owner. -/
theorem two_dimensional_tv_l1_fdpg_u_eq (k : ℕ) :
    u[k] = Aᵀ[m, n] z̃[k] + d := rfl

/-- Evaluating the auxiliary image at `(i, j)` gives the step-(a) matrix formula through the
canonical adjoint owner. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_u_apply
    (k : ℕ) (i : Fin m) (j : Fin n) :
    u[k] i j = Aᵀ[m, n] z̃[k] i j + d i j := rfl

/-- At every iteration `k`, the next dual pair is obtained from the owner-level step-(b) update
evaluated at `u^k` and `\tilde z^k`. -/
theorem two_dimensional_tv_l1_fdpg_z_update (k : ℕ) :
    z[k + 1] = two_dimensional_tv_l1_fdpg_dual_update lam u[k] z̃[k] := rfl

/-- At every iteration `k`, the next horizontal dual iterate is the first coordinate of the
canonical owner-level step-(b) dual update. -/
theorem two_dimensional_tv_l1_fdpg_p_update (k : ℕ) :
    p[k + 1] = (two_dimensional_tv_l1_fdpg_dual_update lam u[k] z̃[k]).fst := by
  simpa [two_dimensional_tv_l1_fdpg_p] using
    congrArg (fun z ↦ z.fst) (two_dimensional_tv_l1_fdpg_z_update d lam p0 q0 k)

/-- Evaluating the horizontal step-(b) recursion gives the source-facing update formula for the
entry `p_(i,j)^(k+1)` in terms of the Proposition 12.4 horizontal difference of `u^k`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_p_update_apply
    (k : ℕ) (i : Fin m) (j : Fin (n - 1)) :
    p[k + 1] i j =
      p̃[k] i j - (1 / 8 : ℝ) * two_dimensional_total_variation_horizontal_difference u[k] i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] (two_dimensional_total_variation_horizontal_difference u[k] i j -
            8 * p̃[k] i j) := by
  simpa using
    two_dimensional_tv_l1_fdpg_dual_update_fst_apply lam u[k] z̃[k] i j

/-- At every iteration `k`, the next vertical dual iterate is the second coordinate of the
canonical owner-level step-(b) dual update. -/
theorem two_dimensional_tv_l1_fdpg_q_update (k : ℕ) :
    q[k + 1] = (two_dimensional_tv_l1_fdpg_dual_update lam u[k] z̃[k]).snd := by
  simpa [two_dimensional_tv_l1_fdpg_q] using
    congrArg (fun z ↦ z.snd) (two_dimensional_tv_l1_fdpg_z_update d lam p0 q0 k)

/-- Evaluating the vertical step-(b) recursion gives the source-facing update formula for the
entry `q_(i,j)^(k+1)` in terms of the Proposition 12.4 vertical difference of `u^k`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_q_update_apply
    (k : ℕ) (i : Fin (m - 1)) (j : Fin n) :
    q[k + 1] i j =
      q̃[k] i j - (1 / 8 : ℝ) * two_dimensional_total_variation_vertical_difference u[k] i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] (two_dimensional_total_variation_vertical_difference u[k] i j -
            8 * q̃[k] i j) := by
  simpa using
    two_dimensional_tv_l1_fdpg_dual_update_snd_apply lam u[k] z̃[k] i j

/-- The first extrapolated dual pair satisfies `\tilde z¹ = z¹`. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_one :
    z̃[1] = z[1] := by
  simp [two_dimensional_tv_l1_fdpg_zExtrap, two_dimensional_tv_l1_fdpg_z,
    two_dimensional_tv_l1_fdpg_state, two_dimensional_tv_l1_fdpg_state_update,
    two_dimensional_tv_l1_fdpg_initial_state, two_dimensional_tv_l1_fdpg_extrapolation_factor]

/-- The first extrapolated horizontal iterate satisfies `\tilde p¹ = p¹`. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_one :
    p̃[1] = p[1] := by
  simpa [two_dimensional_tv_l1_fdpg_pExtrap, two_dimensional_tv_l1_fdpg_p] using
    congrArg (fun z ↦ z.fst) (two_dimensional_tv_l1_fdpg_zExtrap_one d lam p0 q0)

/-- The first extrapolated vertical iterate satisfies `\tilde q¹ = q¹`. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_one :
    q̃[1] = q[1] := by
  simpa [two_dimensional_tv_l1_fdpg_qExtrap, two_dimensional_tv_l1_fdpg_q] using
    congrArg (fun z ↦ z.snd) (two_dimensional_tv_l1_fdpg_zExtrap_one d lam p0 q0)

/-- For every `k`, the later extrapolated dual pairs satisfy the shifted step-(d) recursion
`\tilde z^(k+2) = z^(k+2) + (t_k / t_(k+2)) (z^(k+2) - z^(k+1))`. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_succ_succ (k : ℕ) :
    z̃[k + 2] = z[k + 2] + (t[k] / t[k + 2]) • (z[k + 2] - z[k + 1]) := by
  simp [two_dimensional_tv_l1_fdpg_zExtrap, two_dimensional_tv_l1_fdpg_z,
    two_dimensional_tv_l1_fdpg_state, two_dimensional_tv_l1_fdpg_state_update,
    two_dimensional_tv_l1_fdpg_extrapolation_factor]

/-- For every `k`, the later extrapolated horizontal iterates satisfy the shifted step-(d)
recursion
`\tilde p^(k+2) = p^(k+2) + (t_k / t_(k+2)) (p^(k+2) - p^(k+1))`,
where `t_k` is the canonical Chapter 10 FISTA momentum sequence. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_succ_succ (k : ℕ) :
    p̃[k + 2] = p[k + 2] + (t[k] / t[k + 2]) • (p[k + 2] - p[k + 1]) := by
  simpa [two_dimensional_tv_l1_fdpg_pExtrap, two_dimensional_tv_l1_fdpg_p] using
    congrArg (fun z ↦ z.fst) (two_dimensional_tv_l1_fdpg_zExtrap_succ_succ d lam p0 q0 k)

/-- For every `k`, the later extrapolated vertical iterates satisfy the shifted step-(d)
recursion
`\tilde q^(k+2) = q^(k+2) + (t_k / t_(k+2)) (q^(k+2) - q^(k+1))`,
where `t_k` is the canonical Chapter 10 FISTA momentum sequence. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_succ_succ (k : ℕ) :
    q̃[k + 2] = q[k + 2] + (t[k] / t[k + 2]) • (q[k + 2] - q[k + 1]) := by
  simpa [two_dimensional_tv_l1_fdpg_qExtrap, two_dimensional_tv_l1_fdpg_q] using
    congrArg (fun z ↦ z.snd) (two_dimensional_tv_l1_fdpg_zExtrap_succ_succ d lam p0 q0 k)

end

end
