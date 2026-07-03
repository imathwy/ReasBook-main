import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

/- Algorithm 10.13 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `prox_gradient_operator` with notation `T[...; ..., ...]` from Definition 10.9 is the chapter's
  canonical owner for the real-valued prox-gradient map `T_L`;
- `fista_momentum_update`, `FISTAState`, and `fista_extrapolated_point` are the intrinsic scalar
  and affine owners for the one-step FISTA momentum/extrapolation data, independent of the
  analytic prox-gradient assumptions;
- the chapter's accelerated-method pattern in Algorithm 10.6, Algorithm 10.14, and Algorithm
  10.59 is to expose named iterate families directly, together with atomic `zero`/`succ`
  projection lemmas;
- the source-facing recursive families `fista_constant_stepsize`, `fista_constant_stepsize_x`,
  `fista_constant_stepsize_y`, and `restarted_fista` are therefore the right public owners for the
  inner and restarted iterates.

Since the source item names the restart points `z^k` and the inner FISTA iterates `x^n`
explicitly, the faithful formalization keeps both layers visible through concrete recursive owners
instead of an existential “there exists a block output” wrapper. -/

/-- The standard FISTA momentum update `t ↦ (1 + √(1 + 4 t^2)) / 2`. -/
def fista_momentum_update (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * t ^ (2 : ℕ))) / 2

-- Proof sketch: this is immediate by unfolding the defining formula of
-- `fista_momentum_update`.
/-- Expanding `fista_momentum_update` yields the textbook formula
`(1 + √(1 + 4 t^2)) / 2`. -/
@[simp] theorem fista_momentum_update_eq (t : ℝ) :
    fista_momentum_update t =
      (1 + Real.sqrt (1 + 4 * t ^ (2 : ℕ))) / 2 := rfl

/-- The FISTA momentum update increases every input by at least `1 / 2`. -/
theorem add_one_half_le_fista_momentum_update (t : ℝ) :
    t + 1 / 2 ≤ fista_momentum_update t := by
  have hsqrt : 2 * t ≤ Real.sqrt (1 + 4 * t ^ (2 : ℕ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [fista_momentum_update_eq]
  linarith

/-- The canonical FISTA momentum sequence `t₀ = 1`,
`t_(n+1) = (1 + √(1 + 4 t_n^2)) / 2`. -/
def fista_momentum_sequence : ℕ → ℝ
  | 0 => 1
  | n + 1 => fista_momentum_update (fista_momentum_sequence n)

/-- The canonical FISTA momentum sequence starts at `t₀ = 1`. -/
@[simp] theorem fista_momentum_sequence_zero :
    fista_momentum_sequence 0 = 1 :=
  rfl

/-- The canonical FISTA momentum sequence satisfies the FISTA update rule. -/
theorem fista_momentum_sequence_succ (n : ℕ) :
    fista_momentum_sequence (n + 1) =
      fista_momentum_update (fista_momentum_sequence n) :=
  rfl

/-- The FISTA state consisting of the previous iterate, the current iterate, and the current
momentum parameter. -/
structure FISTAState (E : Type u) where
  xPrev : E
  xCur : E
  tCur : ℝ

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The extrapolated point associated to a FISTA state `(x^(n-1), x^n, t_n)`, namely
`x^n + ((t_n - 1) / t_(n+1)) (x^n - x^(n-1))`. -/
def fista_extrapolated_point (state : FISTAState E) : E :=
  let tNext := fista_momentum_update state.tCur
  state.xCur + ((state.tCur - 1) / tNext) • (state.xCur - state.xPrev)

-- Proof sketch: unfold `fista_extrapolated_point`; the right-hand side is exactly the defining
-- FISTA extrapolation formula built from `x^(n-1)`, `x^n`, and `t_n`.
/-- Expanding `fista_extrapolated_point` gives the textbook extrapolation formula
`x^n + ((t_n - 1) / t_(n+1)) (x^n - x^(n-1))`. -/
@[simp] theorem fista_extrapolated_point_eq (state : FISTAState E) :
    fista_extrapolated_point state =
      let tNext := fista_momentum_update state.tCur
      state.xCur + ((state.tCur - 1) / tNext) • (state.xCur - state.xPrev) := rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f : E → ℝ) (g : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/-- One constant-stepsize FISTA update: extrapolate from the current state using the standard
momentum coefficient and apply the prox-gradient map `T_(L_f)` at that extrapolated point. -/
def fista_constant_stepsize_state_update
    (Lf : PosReal) (state : FISTAState E) :
    FISTAState E :=
  let tNext := fista_momentum_update state.tCur
  let y := fista_extrapolated_point state
  { xPrev := state.xCur
    xCur := T[Lf; f, g] y
    tCur := tNext }

/-- The constant-stepsize FISTA state sequence started from `x^{-1} = z`,
`x^0 = T_(L_f)(z)`, and `t_0 = 1`. -/
def fista_constant_stepsize
    (Lf : PosReal) (z : E) :
    ℕ → FISTAState E
  | 0 =>
      { xPrev := z
        xCur := T[Lf; f, g] z
        tCur := 1 }
  | n + 1 => fista_constant_stepsize_state_update f g Lf (fista_constant_stepsize Lf z n)

/-- The constant-stepsize FISTA iterate family `x^n`. -/
def fista_constant_stepsize_x
    (Lf : PosReal) (z : E) (n : ℕ) : E :=
  (fista_constant_stepsize f g Lf z n).xCur

/-- The constant-stepsize FISTA extrapolated family `y^n`. -/
def fista_constant_stepsize_y
    (Lf : PosReal) (z : E) (n : ℕ) : E :=
  fista_extrapolated_point (fista_constant_stepsize f g Lf z n)

-- Proof sketch: unfold `fista_constant_stepsize` at `0`; the current iterate of the initial
-- state is definitionally `T_(L_f)(z)`.
/-- The constant-stepsize FISTA iterate family starts at `x^0 = T_(L_f)(z)`. -/
@[simp] theorem fista_constant_stepsize_x_zero
    (Lf : PosReal) (z : E) :
    fista_constant_stepsize_x f g Lf z 0 =
      T[Lf; f, g] z := rfl

-- Proof sketch: at the initialized state, `t_0 = 1`, so the extrapolation coefficient vanishes
-- and `y^0 = x^0`.
/-- The constant-stepsize FISTA extrapolated family starts from `y^0 = x^0 = T_(L_f)(z)`. -/
@[simp] theorem fista_constant_stepsize_y_zero
    (Lf : PosReal) (z : E) :
    fista_constant_stepsize_y f g Lf z 0 =
      T[Lf; f, g] z := by
  simp [fista_constant_stepsize_y, fista_constant_stepsize, fista_extrapolated_point,
    fista_momentum_update]

-- Proof sketch: unfold `fista_constant_stepsize` at `n + 1`; the updated state's current iterate
-- is definitionally the prox-gradient point `T_(L_f)(y^n)`.
/-- Each constant-stepsize FISTA successor iterate satisfies
`x^(n+1) = T_(L_f)(y^n)`. -/
theorem fista_constant_stepsize_x_succ
    (Lf : PosReal) (z : E) (n : ℕ) :
    fista_constant_stepsize_x f g Lf z (n + 1) =
      T[Lf; f, g] (fista_constant_stepsize_y f g Lf z n) :=
  rfl

/-- Helper for Algorithm 10.13: the momentum field stored in the constant-stepsize FISTA state
agrees with the canonical FISTA momentum sequence. -/
theorem fista_constant_stepsize_tCur_eq
    (Lf : PosReal) (z : E) (n : ℕ) :
    (fista_constant_stepsize f g Lf z n).tCur =
      fista_momentum_sequence n := by
  induction n with
  | zero =>
      -- The initialized state records the textbook starting momentum `t₀ = 1`.
      simp [fista_constant_stepsize, fista_momentum_sequence]
  | succ n hn =>
      -- One state update advances `tCur` by the same scalar recursion as
      -- `fista_momentum_sequence`.
      rw [fista_constant_stepsize, fista_constant_stepsize_state_update, hn,
        fista_momentum_sequence_succ]

-- Proof sketch: unfold `fista_constant_stepsize` at `n + 1`; the extrapolated point of the
-- updated state is definitionally the standard FISTA formula built from `x^(n+1)`, `x^n`, and
-- the canonical momentum values `fista_momentum_sequence (n + 1)` and
-- `fista_momentum_sequence (n + 2)`.
/-- The constant-stepsize FISTA extrapolated family satisfies
`y^(n+1) = x^(n+1) + ((t_(n+1) - 1) / t_(n+2)) (x^(n+1) - x^n)`, where `t_n` is the canonical
FISTA momentum sequence `fista_momentum_sequence`. -/
theorem fista_constant_stepsize_y_succ
    (Lf : PosReal) (z : E) (n : ℕ) :
    fista_constant_stepsize_y f g Lf z (n + 1) =
      fista_constant_stepsize_x f g Lf z (n + 1) +
        ((fista_momentum_sequence (n + 1) - 1) /
            fista_momentum_sequence (n + 2)) •
          (fista_constant_stepsize_x f g Lf z (n + 1) - fista_constant_stepsize_x f g Lf z n) :=
  by
  -- Unfold the extrapolated point once so the state fields can be rewritten to the canonical
  -- momentum sequence.
  rw [fista_constant_stepsize_y, fista_extrapolated_point_eq]
  have ht :
      (fista_constant_stepsize f g Lf z (n + 1)).tCur =
        fista_momentum_sequence (n + 1) :=
    fista_constant_stepsize_tCur_eq f g Lf z (n + 1)
  have htNext :
      fista_momentum_update ((fista_constant_stepsize f g Lf z (n + 1)).tCur) =
        fista_momentum_sequence (n + 2) := by
    -- The next stored momentum is one more step of the same canonical recursion.
    rw [ht, ← fista_momentum_sequence_succ (n + 1)]
  -- After the momentum terms are identified, the remaining fields are exactly the iterate family
  -- projections `x^(n+1)` and `x^n`.
  have hxPrev :
      (fista_constant_stepsize f g Lf z (n + 1)).xPrev =
        fista_constant_stepsize_x f g Lf z n := by
    rfl
  rw [htNext, ht]
  rw [hxPrev]
  simp [fista_constant_stepsize_x]

/-- Algorithm 10.13: given an input point `z^{-1}` and a positive integer restart length `N`,
the restarted FISTA sequence is defined by `z^0 = T_(L_f)(z^{-1})` and
`z^(k+1) = x^N`, where `x^N` is the `N`th constant-stepsize FISTA iterate started from `z^k`. -/
def restarted_fista
    (Lf : PosReal) (zMinusOne : E) (N : ℕ+) : ℕ → E
  | 0 => T[Lf; f, g] zMinusOne
  | k + 1 =>
      fista_constant_stepsize_x f g Lf (restarted_fista Lf zMinusOne N k) N

-- Proof sketch: unfold the recursive definition of `restarted_fista` at the base index `0`.
/-- The restarted FISTA sequence starts at `z^0 = T_(L_f)(z^{-1})`. -/
@[simp] theorem restarted_fista_zero
    (Lf : PosReal) (zMinusOne : E) (N : ℕ+) :
    restarted_fista f g Lf zMinusOne N 0 =
      T[Lf; f, g] zMinusOne := by
  simp [restarted_fista]

-- Proof sketch: unfold the recursive definition of `restarted_fista` at `k + 1`; the next outer
-- restart point is the `N`th inner iterate of the constant-stepsize FISTA family started from
-- `z^k`.
/-- Each restarted FISTA outer iterate `z^(k+1)` is the `N`th inner constant-stepsize FISTA
iterate started from the previous restart point `z^k`. -/
@[simp] theorem restarted_fista_succ
    (Lf : PosReal) (zMinusOne : E) (N : ℕ+) (k : ℕ) :
    restarted_fista f g Lf zMinusOne N (k + 1) =
      fista_constant_stepsize_x f g Lf (restarted_fista f g Lf zMinusOne N k) (N : ℕ) := by
  simp [restarted_fista]

variable {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

end
