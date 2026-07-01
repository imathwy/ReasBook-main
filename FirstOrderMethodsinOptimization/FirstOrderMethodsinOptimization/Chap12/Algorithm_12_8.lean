import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsinOptimization.Chap12.Algorithm_12_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped BigOperators

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {p : ℕ}

/- Algorithm 12.8 is `source-facing` in the projection-onto-an-intersection subsection.

Domain sampling against nearby project owners identifies the owner layers as follows.
- `source-facing`: the named iterate families `u^k`, `y^k`, and `w^k`;
- `core/canonical`: `DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1`,
  `finite_intersection_projection_primal_point`, and
  `finite_intersection_projection_dual_update` from Algorithm 12.7 for the admissible parameter
  and the shared step-(a) / step-(b) primitives, together with `fista_momentum_sequence` and
  `fista_momentum_update` from Algorithm 10.13 for the scalar recurrence
  `t_(k+1) = (1 + √(1 + 4 t_k²)) / 2`;
- `bridge/view`: the private recursive state carrying only the hidden bookkeeping convention
  `t_(-1) = 0`.

The primitive data are therefore the nonempty closed convex family `C`, the admissible parameter
`L`, the point `d`, and the initialization `y0 : E^p`. The source item is an explicit recursive
algorithm with named sequences `u^k`, `y^k`, `w^k`, and `t_k`, so the public API keeps the
genuinely new iterate families `u^k`, `y^k`, and `w^k` visible. As in the nearby Chapter 12 FDPG
files, the scalar sequence `t_k` is only derived API, already owned upstream by
`fista_momentum_sequence`, so this file reuses that owner directly on theorem surfaces instead of
introducing a parallel public alias. -/

/- The finite-intersection FDPG acceleration scalars use the canonical Chapter 10 FISTA momentum
sequence. -/
recall fista_momentum_sequence

/- Its initialization and recursion are reused directly on the FDPG theorem surface. -/
recall fista_momentum_sequence_zero
recall fista_momentum_sequence_succ

private structure FiniteIntersectionFDPGState (E : Type u) (p : ℕ) where
  yCur : Fin p → E
  wCur : Fin p → E
  tPrev : ℝ
  tCur : ℝ

local notation "State" => FiniteIntersectionFDPGState E p

private def finite_intersection_fdpg_initial_state (y0 : Fin p → E) : State :=
  { yCur := y0
    wCur := y0
    tPrev := 0
    tCur := 1 }

section

variable (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
variable (d : E) (y0 : Fin p → E)

private def finite_intersection_fdpg_state_update
    (state : State) : State :=
  let yNext :=
    finite_intersection_projection_dual_update
      C hC_nonempty hC_closed hC_convex L
      (finite_intersection_projection_primal_point d state.wCur) state.wCur
  let tNext := fista_momentum_update state.tCur
  { yCur := yNext
    wCur := yNext + (state.tPrev / tNext) • (yNext - state.yCur)
    tPrev := state.tCur
    tCur := tNext }

private def finite_intersection_fdpg_state
    : ℕ → State
  | 0 => finite_intersection_fdpg_initial_state y0
  | k + 1 =>
      finite_intersection_fdpg_state_update C hC_nonempty hC_closed hC_convex L d
        (finite_intersection_fdpg_state k)

/-- Algorithm 12.8: for nonempty closed convex sets `C₁, …, C_p`, an admissible constant
parameter `L ≥ p`, a point `d ∈ E`, and an initialization `w⁰ = y⁰ = y0 ∈ E^p`, the iterate
families below generate the finite-intersection FDPG recursion with
`u^k = ∑ᵢ wᵢ^k + d`,
`yᵢ^(k+1) = wᵢ^k - (1 / L) u^k + (1 / L) P_{Cᵢ}(u^k - L wᵢ^k)`,
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`,
and
`w^(k+1) = y^(k+1) + (t_(k-1) / t_(k+1)) (y^(k+1) - y^k)`,
implemented in Lean through the equivalent hidden initialization `t_(-1) = 0`. -/
def finite_intersection_fdpg_y
    : ℕ → Fin p → E :=
  fun k ↦ (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k).yCur

/-- The finite-intersection FDPG extrapolated sequence `w^k ∈ E^p`. -/
def finite_intersection_fdpg_w
    : ℕ → Fin p → E :=
  fun k ↦ (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k).wCur

/-- The finite-intersection FDPG primal sequence `u^k = ∑ᵢ wᵢ^k + d`. -/
def finite_intersection_fdpg_u
    : ℕ → E :=
  fun k ↦ finite_intersection_projection_primal_point d
    (finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k)

end

section

variable (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
variable (d : E) (y0 : Fin p → E)

local notation "state[" k "]" =>
  finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k
local notation "y[" k "]" =>
  finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 k
local notation "w[" k "]" =>
  finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k
local notation "t[" k "]" => fista_momentum_sequence k
local notation "u[" k "]" =>
  finite_intersection_fdpg_u C hC_nonempty hC_closed hC_convex L d y0 k

private theorem finite_intersection_fdpg_state_tCur_eq (k : ℕ) :
    state[k].tCur = t[k] := by
  induction k with
  | zero =>
      simp [finite_intersection_fdpg_state, finite_intersection_fdpg_initial_state,
        fista_momentum_sequence]
  | succ k hk =>
      simp [finite_intersection_fdpg_state, finite_intersection_fdpg_state_update,
        fista_momentum_sequence_succ, hk]

private theorem finite_intersection_fdpg_state_tPrev_succ_eq (k : ℕ) :
    state[k + 1].tPrev = t[k] := by
  simp [finite_intersection_fdpg_state, finite_intersection_fdpg_state_update,
    finite_intersection_fdpg_state_tCur_eq]

/-- The finite-intersection FDPG sequence starts from `y⁰ = y0`. -/
@[simp] theorem finite_intersection_fdpg_y_zero :
    y[0] = y0 :=
  rfl

/-- The finite-intersection FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
@[simp] theorem finite_intersection_fdpg_w_zero :
    w[0] = y0 :=
  rfl

/-- Each finite-intersection FDPG primal iterate satisfies `u^k = ∑ᵢ wᵢ^k + d`. -/
theorem finite_intersection_fdpg_u_eq (k : ℕ) :
    u[k] = (∑ i, w[k] i) + d :=
  rfl

/-- Each successor iterate is obtained by applying the shared finite-intersection projection
update owner to `u^k` and `w^k`. -/
theorem finite_intersection_fdpg_y_succ (k : ℕ) :
    y[k + 1] =
      finite_intersection_projection_dual_update
        C hC_nonempty hC_closed hC_convex L u[k] w[k] :=
  rfl

/-- For each coordinate `i`, the successor iterate `yᵢ^(k+1)` is given by the textbook FDPG
projection formula based on `u^k` and `wᵢ^k`. -/
theorem finite_intersection_fdpg_y_succ_apply (k : ℕ) (i : Fin p) :
    y[k + 1] i =
      w[k] i - (1 / L : ℝ) • u[k] +
        (1 / L : ℝ) •
          Pp[C i, hC_nonempty i, hC_closed i, hC_convex i] (u[k] - (L : ℝ) • w[k] i) := by
  simpa using
    congrFun (finite_intersection_fdpg_y_succ C hC_nonempty hC_closed hC_convex L d y0 k) i

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem finite_intersection_fdpg_w_one :
    w[1] = y[1] := by
  simp [finite_intersection_fdpg_w, finite_intersection_fdpg_y, finite_intersection_fdpg_state,
    finite_intersection_fdpg_state_update, finite_intersection_fdpg_initial_state]

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook recursion
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`, where `t_k` is the canonical Chapter
10 FISTA momentum sequence. -/
theorem finite_intersection_fdpg_w_succ_succ (k : ℕ) :
    w[k + 2] =
      y[k + 2] + (t[k] / t[k + 2]) • (y[k + 2] - y[k + 1]) := by
  have htPrev : state[k + 1].tPrev = t[k] :=
    finite_intersection_fdpg_state_tPrev_succ_eq C hC_nonempty hC_closed hC_convex L d y0 k
  have htCur : state[k + 1].tCur = t[k + 1] :=
    finite_intersection_fdpg_state_tCur_eq C hC_nonempty hC_closed hC_convex L d y0 (k + 1)
  change
    (finite_intersection_fdpg_state_update
      C hC_nonempty hC_closed hC_convex L d state[k + 1]).wCur =
      (finite_intersection_fdpg_state_update
        C hC_nonempty hC_closed hC_convex L d state[k + 1]).yCur +
        (t[k] / t[k + 2]) •
          ((finite_intersection_fdpg_state_update
              C hC_nonempty hC_closed hC_convex L d
              state[k + 1]).yCur - state[k + 1].yCur)
  simp only [finite_intersection_fdpg_state_update, htPrev, htCur]
  rw [← fista_momentum_sequence_succ (k + 1)]

end

end
