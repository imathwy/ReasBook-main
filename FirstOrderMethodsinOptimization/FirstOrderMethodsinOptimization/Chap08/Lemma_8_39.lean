import FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_38
import FirstOrderMethodsinOptimization.Chap08.Definition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 8.39 is `source-facing`: its mathematical content is the descent estimate for the actual
incremental projected subgradient iterates `x^{k,i}` and `x^k`, not a surrogate wrapper around the
finite-sum problem. The existing owner abstractions already present in the project are the metric
projection `metricProjection`, the aggregate finite-sum objective `finite_sum_objective`, the
standing constrained problem class `IsConstrainedConvexProblem`, and the componentwise
assumption package `IncrementalProjectedSubgradientAssumptions`. The only genuinely new data are
the recursive inner and outer iterate sequences for the incremental method itself. -/

/-- The `Fin m` index canonically determined by a natural number `i < m`. -/
def fin_from_lt {m i : ℕ} (h : i < m) : Fin m :=
  ⟨i, h⟩

-- Proof sketch: unfold `fin_from_lt`; the underlying natural number of the resulting `Fin m`
-- index is definitionally `i`.
/-- The canonical `Fin` index built from `i < m` has underlying value `i`. -/
@[simp] theorem fin_from_lt_val {m i : ℕ} (h : i < m) :
    (fin_from_lt h : ℕ) = i := sorry

/-- The inner iterates `x^{k,i}` of the incremental projected subgradient method, obtained by
starting from the outer iterate `x^k = xk` and projecting after each of the first `i` component
subgradient steps at cycle `k`. -/
def incremental_projected_subgradient_inner_iterates {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (k : ℕ) (xk : C) : ℕ → C
  | 0 => xk
  | i + 1 =>
      let xki :=
        incremental_projected_subgradient_inner_iterates
          C hC_nonempty hC_closed hC_convex g t k xk i
      if hi : i < m then
        metricProjection C hC_nonempty hC_closed.isComplete hC_convex
          ((xki : E) - t k • g k xki (fin_from_lt hi))
      else
        xki

-- Proof sketch: unfold the recursive definition of
-- `incremental_projected_subgradient_inner_iterates` at `0`.
/-- The inner incremental projected-subgradient cycle starts from the prescribed outer iterate
`x^k`. -/
@[simp] theorem incremental_projected_subgradient_inner_iterates_zero
    {m : ℕ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → Fin m → E} {t : ℕ → ℝ} {k : ℕ} {xk : C} :
    incremental_projected_subgradient_inner_iterates
      C hC_nonempty hC_closed hC_convex g t k xk 0 = xk := sorry

-- Proof sketch: unfold the recursive definition at `i + 1`; the branch `hi : i < m` selects the
-- component index `⟨i, hi⟩`, so the next inner iterate is exactly one projected subgradient step
-- from `x^{k,i}` using the common stepsize `t_k`.
/-- When `i < m`, the next inner iterate is the metric projection of `x^{k,i} - t_k g^{k,i}` onto
`C`. -/
theorem incremental_projected_subgradient_inner_iterates_succ
    {m : ℕ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → Fin m → E} {t : ℕ → ℝ} {k i : ℕ} {xk : C}
    (hi : i < m) :
    incremental_projected_subgradient_inner_iterates
      C hC_nonempty hC_closed hC_convex g t k xk (i + 1) =
      metricProjection C hC_nonempty hC_closed.isComplete hC_convex
        (((incremental_projected_subgradient_inner_iterates
            C hC_nonempty hC_closed hC_convex g t k xk i : C) : E) -
          t k •
            g k
              (incremental_projected_subgradient_inner_iterates
                C hC_nonempty hC_closed hC_convex g t k xk i)
              (fin_from_lt hi)) := sorry

/-- The outer iterate sequence `x^k` of the incremental projected subgradient method, where
`x^{k+1}` is obtained by running one full inner cycle of `m` projected component-subgradient steps
starting from `x^k`. -/
def incremental_projected_subgradient_method {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C) : ℕ → C
  | 0 => x0
  | k + 1 =>
      let xk :=
        incremental_projected_subgradient_method
          C hC_nonempty hC_closed hC_convex g t x0 k
      incremental_projected_subgradient_inner_iterates
        C hC_nonempty hC_closed hC_convex g t k xk m

-- Proof sketch: unfold the recursive definition of
-- `incremental_projected_subgradient_method` at `0`.
/-- The incremental projected-subgradient method starts from the prescribed feasible initial
point. -/
@[simp] theorem incremental_projected_subgradient_method_zero
    {m : ℕ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → Fin m → E} {t : ℕ → ℝ} {x0 : C} :
    incremental_projected_subgradient_method
      C hC_nonempty hC_closed hC_convex g t x0 0 = x0 := sorry

-- Proof sketch: unfold the recursive definition of
-- `incremental_projected_subgradient_method` at `k + 1`; this identifies `x^{k+1}` with the end
-- point `x^{k,m}` of one full inner cycle starting from `x^k`.
/-- One outer step of the incremental projected subgradient method is the terminal inner iterate
after processing all `m` component functions once. -/
theorem incremental_projected_subgradient_method_succ
    {m : ℕ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → Fin m → E} {t : ℕ → ℝ} {x0 : C} (k : ℕ) :
    incremental_projected_subgradient_method
      C hC_nonempty hC_closed hC_convex g t x0 (k + 1) =
      incremental_projected_subgradient_inner_iterates
        C hC_nonempty hC_closed hC_convex g t k
        (incremental_projected_subgradient_method
          C hC_nonempty hC_closed hC_convex g t x0 k)
        m := sorry

section

variable {m : ℕ}
variable {fi : Fin m → E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem (finite_sum_objective fi) C XStar fOpt)
variable (h_incremental : IncrementalProjectedSubgradientAssumptions fi C)
variable (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex g t x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterates
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex g t k x[k] i

-- Proof sketch: apply the one-step projected subgradient inequality to each inner update
-- `x[k,i+1] = P_C (x[k,i] - t_k g^{k,i})`, sum over the `m` component steps, rewrite the summed
-- component objectives as the finite-sum objective, and bound the accumulated error terms with the
-- common subgradient norm constant `h_incremental.L` from Assumption 8.38.
/-- Lemma 8.39: under Assumptions 8.7 and 8.38, every outer step of the incremental projected
subgradient method satisfies the fundamental inequality
`‖x^{k+1} - xStar‖^2 ≤ ‖x^k - xStar‖^2 - 2 t_k (f(x^k) - fOpt) + t_k^2 m^2 L^2`
for each optimal point `xStar ∈ XStar`, where `f = ∑ i, f_i` and `L = h_incremental.L`. -/
theorem incremental_projected_subgradient_method_fundamental_inequality
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k, i] i) ∈ strongDualSubdifferential (fi i) (x[k, i] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
      ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
        2 * t k * (((finite_sum_objective fi) (x[k] : E)).toReal - fOpt) +
          (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := sorry

end

end
