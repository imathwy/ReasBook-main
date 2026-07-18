import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Proposition 10.58 is `source-facing` in the chapter's smoothing API.

Domain sampling:
- `T[...]` from Definition 10.9 is already the chapter owner for the prox-gradient map attached
  to a real-valued smooth term and an extended-real-valued regularizer;
- `fista_momentum_update` and `fista_momentum_sequence` from Algorithm 10.13 are the canonical
  Chapter 10 owners of the scalar FISTA momentum recursion;
- `FISTAState`, `fista_extrapolated_point`, and `fista_state_update` from Algorithm 10.6 are the
  canonical owners for accelerated states carrying the current momentum `t_k`;
- Proposition 10.56 already owns the regularity assumptions for the regularizer `g`.

Source/core/bridge triage:
- `source-facing`: the S-FISTA iterate and extrapolated-point sequences `s_fista_x` and
  `s_fista_y`;
- `core/canonical`: the Chapter 10 momentum owner `fista_momentum_sequence`;
- `bridge/view`: the private auxiliary state below, which stores the hidden boundary convention
  `t_(-1) = 0` needed to implement the textbook coefficient `((t_(k-1) - 1) / t_k)`.

Primitive data vs derived API:
- primitive data: the source-specific boundary convention `t_(-1) = 0`, the initial point
  `x^(-1) = x^0 = x0`, and the constant curvature parameter `L̃ = L_f + α / μ`;
- derived API: the public iterate and extrapolated-point sequences, together with direct reuse of
  the canonical Chapter 10 momentum sequence.

The only genuinely new source content is the boundary-explicit initialization used by S-FISTA.
Since the scalar momentum recursion is already owned upstream by `fista_momentum_sequence`, the
public API should expose the source-facing sequences directly and keep the boundary bookkeeping
internal instead of presenting a shifted public `FISTAState` owner. -/

-- Proof sketch: `Lf` is nonnegative, while `α` and `μ` are positive, so `α / μ > 0`; adding the
-- nonnegative term `Lf` keeps the total positive.
/-- The effective curvature parameter `L_f + α / μ` used by S-FISTA is positive. -/
theorem s_fista_curvature_bound_pos (Lf : NNReal) (α μ : PosReal) :
    0 < (Lf : ℝ) + (α : ℝ) / (μ : ℝ) := by
  -- The smoothing contribution is positive because both `α` and `μ` are positive.
  have hdiv : 0 < (α : ℝ) / (μ : ℝ) := by
    exact div_pos (PosReal.coe_pos α) (PosReal.coe_pos μ)
  -- Adding the nonnegative base curvature preserves strict positivity.
  exact add_pos_of_nonneg_of_pos (NNReal.coe_nonneg Lf) hdiv

/-- The S-FISTA curvature parameter `L̃ = L_f + α / μ`. -/
def s_fista_curvature_bound (Lf : NNReal) (α μ : PosReal) : PosReal :=
  ⟨(Lf : ℝ) + (α : ℝ) / (μ : ℝ), s_fista_curvature_bound_pos Lf α μ⟩

-- Proof sketch: unfold `s_fista_curvature_bound`; its real value is definitionally the sum
-- `(Lf : ℝ) + (α : ℝ) / (μ : ℝ)`.
/-- Coercing the S-FISTA curvature parameter to `ℝ` recovers the formula `L_f + α / μ`. -/
@[simp] theorem s_fista_curvature_bound_coe (Lf : NNReal) (α μ : PosReal) :
    ((s_fista_curvature_bound Lf α μ : PosReal) : ℝ) =
      (Lf : ℝ) + (α : ℝ) / (μ : ℝ) := by
  -- The packaged `PosReal` stores this real value by definition.
  rfl

private def s_fista_initial_aux_state (x0 : E) : FISTAState E :=
  { xPrev := x0
    xCur := x0
    tCur := 0 }

private def s_fista_aux_state_update
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (state : FISTAState E) :
    FISTAState E :=
  let y := fista_extrapolated_point state
  { xPrev := state.xCur
    xCur := T[s_fista_curvature_bound Lf α μ, (fun z ↦ f z + hμ z).toExtendedReal, g]
      (interior_effective_domain_point_of_real (fun z ↦ f z + hμ z) y)
    tCur := fista_momentum_update state.tCur }

private def s_fista_aux_state
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → FISTAState E
  | 0 => s_fista_initial_aux_state x0
  | k + 1 => s_fista_aux_state_update f hμ g Lf α μ (s_fista_aux_state f hμ g Lf α μ x0 k)

/-- Proposition 10.58: for a real-valued smooth term `f`, a smoothing `h_μ`, a proper closed
convex regularizer `g`, an initial point `x^0 = x0`, and the effective curvature parameter
`L̃ = L_f + α / μ`, the S-FISTA recursion is expressed through the chapter's canonical
`FISTAState E`. Its `k`-th state stores the boundary-explicit data
`(x^(k-1), x^k, t_(k-1))`, initialized by `x^(-1) = x^0 = x0` and `t_(-1) = 0`, and the update
uses the prox-gradient map for `f + h_μ` together with the standard FISTA extrapolation rule. -/
def s_fista
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → FISTAState E :=
  s_fista_aux_state f hμ g Lf α μ x0

/-- The S-FISTA primal iterates `x^k`. -/
def s_fista_x
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (s_fista f hμ g Lf α μ x0 k).xCur

/-- The S-FISTA extrapolated points `y^k`. The hidden boundary convention `t_(-1) = 0` remains
internal, while the public momentum sequence is reused directly from
`fista_momentum_sequence`. -/
def s_fista_y
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ fista_extrapolated_point (s_fista f hμ g Lf α μ x0 k)

section

variable (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable (Lf : NNReal) (α μ : PosReal) (x0 : E)

local notation "state[" k "]" => s_fista_aux_state f hμ g Lf α μ x0 k

private theorem s_fista_aux_state_tCur_succ (k : ℕ) :
    state[k + 1].tCur = fista_momentum_sequence k := by
  induction k with
  | zero =>
      simp [s_fista_aux_state, s_fista_initial_aux_state, s_fista_aux_state_update,
        fista_momentum_sequence]
  | succ k hk =>
      rw [s_fista_aux_state, s_fista_aux_state_update, hk, fista_momentum_sequence_succ]

-- Proof sketch: unfold `s_fista_x` at index `0`; the initial auxiliary state's `xCur` field is
-- `x0`.
/-- The S-FISTA primal sequence starts at the input point `x^0`. -/
@[simp] theorem s_fista_x_zero
    :
    s_fista_x f hμ g Lf α μ x0 0 = x0 :=
  rfl

-- Proof sketch: unfold `s_fista_y` at index `0`; the initial auxiliary state records
-- `x^(-1) = x^0 = x0` and `t_(-1) = 0`, so the extrapolation coefficient is `(-1) / 1` applied
-- to the zero vector.
/-- The S-FISTA extrapolated sequence starts from `y^0 = x^0`. -/
@[simp] theorem s_fista_y_zero
    :
    s_fista_y f hμ g Lf α μ x0 0 = x0 := by
  simp [s_fista_y, s_fista, s_fista_aux_state, s_fista_initial_aux_state,
    fista_extrapolated_point, fista_momentum_update]

-- Proof sketch: unfold `state[k + 1]`; the updated auxiliary state's `xCur` field is exactly the
-- smoothed prox-gradient point computed from `y^k`.
/-- At each iteration `k`, the next S-FISTA primal iterate is the proximal-gradient point for the
smoothed objective evaluated at `y^k`. -/
theorem s_fista_x_succ
    (k : ℕ) :
    s_fista_x f hμ g Lf α μ x0 (k + 1) =
      T[s_fista_curvature_bound Lf α μ, (fun y ↦ f y + hμ y).toExtendedReal, g]
        (interior_effective_domain_point_of_real (fun y ↦ f y + hμ y)
          (s_fista_y f hμ g Lf α μ x0 k)) :=
  rfl

-- Proof sketch: unfold `s_fista_y` at `k + 1`; the auxiliary state stores the previous momentum
-- `t_k`, which is canonically `fista_momentum_sequence k`, and one more update gives
-- `fista_momentum_sequence (k + 1)`.
/-- At each iteration `k`, the S-FISTA extrapolated point satisfies the update
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) (x^(k+1) - x^k)`. -/
theorem s_fista_y_succ
    (k : ℕ) :
    s_fista_y f hμ g Lf α μ x0 (k + 1) =
      s_fista_x f hμ g Lf α μ x0 (k + 1) +
        ((fista_momentum_sequence k - 1) /
            fista_momentum_sequence (k + 1)) •
          (s_fista_x f hμ g Lf α μ x0 (k + 1) - s_fista_x f hμ g Lf α μ x0 k) := by
  change fista_extrapolated_point state[k + 1] =
    s_fista_x f hμ g Lf α μ x0 (k + 1) +
      ((fista_momentum_sequence k - 1) /
          fista_momentum_sequence (k + 1)) •
        (s_fista_x f hμ g Lf α μ x0 (k + 1) - s_fista_x f hμ g Lf α μ x0 k)
  rw [fista_extrapolated_point_eq]
  have ht : state[k + 1].tCur = fista_momentum_sequence k :=
    s_fista_aux_state_tCur_succ f hμ g Lf α μ x0 k
  have htNext : fista_momentum_update state[k + 1].tCur = fista_momentum_sequence (k + 1) := by
    rw [ht, fista_momentum_sequence_succ]
  rw [htNext, ht]
  simp [s_fista_x, s_fista, s_fista_aux_state, s_fista_aux_state_update]

end

end
