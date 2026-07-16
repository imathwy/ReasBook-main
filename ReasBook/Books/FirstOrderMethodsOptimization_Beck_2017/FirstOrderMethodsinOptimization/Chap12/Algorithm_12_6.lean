import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open WithLp (toLp)
open Matrix

variable {n p : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin p)

/-- Helper for Algorithm 12.6: the admissible constant stepsize parameters specialized to the
polyhedral projection map `x ↦ A x`. -/
abbrev polyhedral_projection_fdpg_stepsize_parameter
    (A : Matrix (Fin p) (Fin n) ℝ) :=
  DualBasedProximalGradientDualStepsizeParameter
    (A.toEuclideanLin.toContinuousLinearMap) 1

/-- Helper for Algorithm 12.6: the coordinatewise minimum of two vectors in `ℝ^p`. -/
def polyhedral_projection_fdpg_coordinatewise_min (x y : Ep) : Ep :=
  toLp 2 (fun i ↦ min (x i) (y i))

/-- Helper for Algorithm 12.6: evaluating the coordinatewise minimum returns the scalar minimum in
that coordinate. -/
@[simp] theorem polyhedral_projection_fdpg_coordinatewise_min_apply
    (x y : Ep) (i : Fin p) :
    polyhedral_projection_fdpg_coordinatewise_min x y i = min (x i) (y i) :=
  rfl

/-- Helper for Algorithm 12.6: the primal point attached to a dual iterate is `Aᵀ y + d`. -/
def polyhedral_projection_fdpg_primal_point
    (A : Matrix (Fin p) (Fin n) ℝ) (d : En) (y : Ep) : En :=
  A.transpose.toEuclideanLin y + d

/-- Helper for Algorithm 12.6: the explicit dual update for the polyhedral projection model. -/
def polyhedral_projection_fdpg_dual_update
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (L : polyhedral_projection_fdpg_stepsize_parameter A) (x : En) (y : Ep) : Ep :=
  y - (1 / L : ℝ) • A.toEuclideanLin x +
    (1 / L : ℝ) •
      polyhedral_projection_fdpg_coordinatewise_min (A.toEuclideanLin x - (L : ℝ) • y) b

local notation "PolyhedralProjectionStepsizeParameter" =>
  polyhedral_projection_fdpg_stepsize_parameter
local notation "polyhedral_projection_primal_point" =>
  polyhedral_projection_fdpg_primal_point
local notation "polyhedral_projection_dual_update" =>
  polyhedral_projection_fdpg_dual_update

/- Algorithm 12.6 is `source-facing` in the subsection on orthogonal projection onto a polyhedral
set.

Domain sampling against nearby project owners identifies:
- `source-facing`: the named iterate families `u^k`, `y^k`, and `w^k`;
- `core/canonical`: `polyhedral_projection_primal_point`, `polyhedral_projection_dual_update`,
  `euclidean_coordinatewise_min`, and `PolyhedralProjectionStepsizeParameter` from Algorithm 12.5
  for the shared projection data, together with `fista_momentum_sequence` and
  `fista_momentum_update` from Algorithm 10.13 for the scalar recursion
  `t_(k+1) = (1 + √(1 + 4 t_k²)) / 2`;
- `bridge/view`: the private recursive state carrying only the hidden bookkeeping convention
  `t_(-1) = 0` needed to encode the extrapolation step.

This separates primitive data from derived API as follows: the only genuinely new public owners in
this file are the explicit iterate families `u^k`, `y^k`, and `w^k`, while the scalar sequence
`t_k` is already owned upstream by `fista_momentum_sequence` and should therefore be reused
directly on theorem surfaces rather than reintroduced through a parallel local definition carrying
the polyhedral problem-data binders. -/

/- The FDPG acceleration scalars use the canonical Chapter 10 FISTA momentum sequence. -/
recall fista_momentum_sequence

/- Its initialization and recursion are reused directly on the FDPG theorem surface. -/
recall fista_momentum_sequence_zero
recall fista_momentum_sequence_succ

private structure PolyhedralProjectionFDPGState (n p : ℕ) where
  yCur : EuclideanSpace ℝ (Fin p)
  wCur : EuclideanSpace ℝ (Fin p)
  tPrev : ℝ
  tCur : ℝ

local notation "State" => PolyhedralProjectionFDPGState n p

private def polyhedral_projection_fdpg_initial_state (y0 : Ep) : State :=
  { yCur := y0
    wCur := y0
    tPrev := 0
    tCur := 1 }

private def polyhedral_projection_fdpg_state_update
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (state : State) : State :=
  let u := polyhedral_projection_primal_point A d state.wCur
  let yNext := polyhedral_projection_dual_update A b L u state.wCur
  let tNext := fista_momentum_update state.tCur
  { yCur := yNext
    wCur := yNext + (state.tPrev / tNext) • (yNext - state.yCur)
    tPrev := state.tCur
    tCur := tNext }

/-- Algorithm 12.6: for the projection problem
`min_x {(1 / 2) ‖x - d‖^2 : A x ≤ b}`, given an admissible constant parameter `L ≥ ‖A‖₂,₂²`
and an initial point `y⁰ = w⁰ = y0`, the recursive families below generate the FDPG iterates
with step-(a) auxiliary point `u^k = Aᵀ w^k + d`, step-(b) update
`y^(k+1) = w^k - (1 / L) A u^k + (1 / L) min {A u^k - L w^k, b}`, step-(c) momentum recursion
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and step-(d) extrapolation
`w^(k+1) = y^(k+1) + (t_(k-1) / t_(k+1)) (y^(k+1) - y^k)`, whose public Lean surface is the
equivalent pair `w¹ = y¹` and
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
private def polyhedral_projection_fdpg_state
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    ℕ → State
  | 0 => polyhedral_projection_fdpg_initial_state y0
  | k + 1 =>
      polyhedral_projection_fdpg_state_update A b d L
        (polyhedral_projection_fdpg_state A b d L y0 k)

/-- The dual iterate sequence `y^k` generated by Algorithm 12.6. -/
def polyhedral_projection_fdpg_y
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    ℕ → Ep :=
  fun k ↦ (polyhedral_projection_fdpg_state A b d L y0 k).yCur

/-- The extrapolated sequence `w^k` generated by Algorithm 12.6. -/
def polyhedral_projection_fdpg_w
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    ℕ → Ep :=
  fun k ↦ (polyhedral_projection_fdpg_state A b d L y0 k).wCur

/-- The auxiliary primal sequence `u^k = Aᵀ w^k + d` derived from the FDPG iterates. -/
def polyhedral_projection_fdpg_u
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    ℕ → En :=
  fun k ↦ polyhedral_projection_primal_point A d (polyhedral_projection_fdpg_w A b d L y0 k)

section

variable (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
variable (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep)

local notation "state[" k "]" => polyhedral_projection_fdpg_state A b d L y0 k
local notation "y[" k "]" => polyhedral_projection_fdpg_y A b d L y0 k
local notation "w[" k "]" => polyhedral_projection_fdpg_w A b d L y0 k
local notation "t[" k "]" => fista_momentum_sequence k
local notation "u[" k "]" => polyhedral_projection_fdpg_u A b d L y0 k

private theorem polyhedral_projection_fdpg_state_tCur_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    (polyhedral_projection_fdpg_state A b d L y0 k).tCur = fista_momentum_sequence k := by
  induction k with
  | zero =>
      simp [polyhedral_projection_fdpg_state, polyhedral_projection_fdpg_initial_state,
        fista_momentum_sequence]
  | succ k hk =>
      rw [polyhedral_projection_fdpg_state, polyhedral_projection_fdpg_state_update,
        fista_momentum_sequence_succ, hk]

/-- Helper for Algorithm 12.6: after one hidden-state update, the stored previous momentum equals
the public FISTA scalar `t_k`. -/
private theorem polyhedral_projection_fdpg_state_tPrev_succ_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    (polyhedral_projection_fdpg_state A b d L y0 (k + 1)).tPrev = fista_momentum_sequence k := by
  -- Unfold one state update so the `tPrev` field becomes the previous state's `tCur`.
  simpa [polyhedral_projection_fdpg_state, polyhedral_projection_fdpg_state_update] using
    polyhedral_projection_fdpg_state_tCur_eq A b d L y0 k

/-- Helper for Algorithm 12.6: the current momentum stored in the hidden state at index `k + 1`
is the public FISTA scalar `t_(k+1)`. -/
private theorem polyhedral_projection_fdpg_state_tCur_succ_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    (polyhedral_projection_fdpg_state A b d L y0 (k + 1)).tCur =
      fista_momentum_sequence (k + 1) := by
  -- Specialize the general `tCur` identification at the successor index used in the main proof.
  simpa using polyhedral_projection_fdpg_state_tCur_eq A b d L y0 (k + 1)

/-- The FDPG dual sequence starts at the prescribed initial point `y⁰ = y0`. -/
theorem polyhedral_projection_fdpg_y_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    polyhedral_projection_fdpg_y A b d L y0 0 = y0 :=
  rfl

/-- The extrapolated FDPG sequence satisfies `w⁰ = y0`. -/
theorem polyhedral_projection_fdpg_w_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    polyhedral_projection_fdpg_w A b d L y0 0 = y0 :=
  rfl

/-- At every iteration `k`, the auxiliary point satisfies the textbook step-(a) formula
`u^k = Aᵀ w^k + d`. -/
theorem polyhedral_projection_fdpg_u_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    polyhedral_projection_fdpg_u A b d L y0 k =
      A.transpose.toEuclideanLin (polyhedral_projection_fdpg_w A b d L y0 k) + d :=
  rfl

/-- At every iteration `k`, the next dual iterate is obtained by the shared polyhedral-projection
dual-update owner applied to `u^k` and `w^k`. -/
theorem polyhedral_projection_fdpg_y_succ
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    polyhedral_projection_fdpg_y A b d L y0 (k + 1) =
      polyhedral_projection_dual_update A b L
        (polyhedral_projection_fdpg_u A b d L y0 k)
        (polyhedral_projection_fdpg_w A b d L y0 k) :=
  rfl

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem polyhedral_projection_fdpg_w_one
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) :
    polyhedral_projection_fdpg_w A b d L y0 1 =
      polyhedral_projection_fdpg_y A b d L y0 1 := by
  simp [polyhedral_projection_fdpg_w, polyhedral_projection_fdpg_y,
    polyhedral_projection_fdpg_state, polyhedral_projection_fdpg_state_update,
    polyhedral_projection_fdpg_initial_state]

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook step-(d)
recursion
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`, where `t_k` is the canonical Chapter
10 FISTA momentum sequence. -/
theorem polyhedral_projection_fdpg_w_succ_succ
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (d : En)
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : Ep) (k : ℕ) :
    polyhedral_projection_fdpg_w A b d L y0 (k + 2) =
      polyhedral_projection_fdpg_y A b d L y0 (k + 2) +
        (fista_momentum_sequence k / fista_momentum_sequence (k + 2)) •
          (polyhedral_projection_fdpg_y A b d L y0 (k + 2) -
            polyhedral_projection_fdpg_y A b d L y0 (k + 1)) := by
  -- Identify the hidden momentum fields at state `k + 1` with the public FISTA scalars.
  have htPrev :
      (polyhedral_projection_fdpg_state A b d L y0 (k + 1)).tPrev = fista_momentum_sequence k :=
    polyhedral_projection_fdpg_state_tPrev_succ_eq A b d L y0 k
  have htCur :
      (polyhedral_projection_fdpg_state A b d L y0 (k + 1)).tCur =
        fista_momentum_sequence (k + 1) :=
    polyhedral_projection_fdpg_state_tCur_succ_eq A b d L y0 k
  -- Rewrite `w[k + 2]` and `y[k + 2]` as the fields of the single hidden-state update at `k + 1`.
  change
    (polyhedral_projection_fdpg_state_update A b d L
        (polyhedral_projection_fdpg_state A b d L y0 (k + 1))).wCur =
      (polyhedral_projection_fdpg_state_update A b d L
          (polyhedral_projection_fdpg_state A b d L y0 (k + 1))).yCur +
        (fista_momentum_sequence k / fista_momentum_sequence (k + 2)) •
          ((polyhedral_projection_fdpg_state_update A b d L
              (polyhedral_projection_fdpg_state A b d L y0 (k + 1))).yCur -
            (polyhedral_projection_fdpg_state A b d L y0 (k + 1)).yCur)
  -- The update already has the textbook FDPG form once the hidden momentum fields are normalized.
  simp only [polyhedral_projection_fdpg_state_update, htPrev, htCur]
  -- Convert the remaining `fista_momentum_update (t[k + 1])` denominator into `t[k + 2]`.
  rw [← fista_momentum_sequence_succ (k + 1)]

end

end
