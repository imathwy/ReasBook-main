import Mathlib
import FirstOrderMethodsinOptimization.Chap05.Definition_5_1
import FirstOrderMethodsinOptimization.Chap05.Lemma_5_7
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_2
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsinOptimization.Chap10.Assumption_10_31
import FirstOrderMethodsinOptimization.Chap10.Remark_10_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u}

/-- The initial FISTA state determined by the input point `x0`, with
`x^{-1} = x^0 = x0` and `t_0 = 1`. -/
def fista_initial_state (x0 : E) : FISTAState E :=
  { xPrev := x0
    xCur := x0
    tCur := 1 }

-- Proof sketch: unfold `fista_initial_state`; the current iterate field is definitionally the
-- initial point `x0`.
/-- The current iterate of the initial FISTA state is the input point `x0`. -/
@[simp] theorem fista_initial_state_xCur (x0 : E) :
    (fista_initial_state x0).xCur = x0 :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.6 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `T[...]` from Definition 10.9 and `fista_momentum_update`, `FISTAState`, and
  `fista_extrapolated_point` from Algorithm 10.13 are already the local owner abstractions for
  the prox-gradient map `T_L`, the momentum update, the triple `(x^{k-1}, x^k, t_k)`, and its
  derived extrapolated point `y^k`;
- `proximal_gradient_backtracking_trial_stepsize` and
  `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 already encode the geometric
  trial family `L_(k-1) η^i` used by B3;
- `proximal_gradient_backtracking_B2_accepts`,
  `proximal_gradient_backtracking_B2_previous_stepsize`, and
  `is_backtracking_procedure_B2_index` from Algorithm 10.3 are already the chapter owners for the
  quadratic upper-model acceptance test, the recursion for the previous accepted stepsize, and the
  minimal accepted trial index;
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 is already the chapter owner for
  the exact constant rule `L_k = L_f`.

The genuinely new content here is the variable-stepsize FISTA recursion, together with the B3
stepsize rule along the extrapolated sequence and the two admissible stepsize regimes. The public
API therefore reuses the existing owner abstractions and adds only the general state update and
the B3 rule itself, rather than introducing a second FISTA wrapper package or a parallel B3
acceptance layer. -/

/-- One FISTA update with curvature estimate `L_k`: extrapolate to `y^k`, apply the prox-gradient
map `T_(L_k)` there, and update the momentum parameter to `t_(k+1)`. -/
def fista_state_update
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (state : FISTAState E) :
    FISTAState E :=
  let tNext := fista_momentum_update state.tCur
  let y := fista_extrapolated_point state
  { xPrev := state.xCur
    xCur := T[L; f, g] y
    tCur := tNext }

-- Proof sketch: both definitions use the same extrapolated point `y` and the same momentum
-- update `tNext`; after unfolding, the two record expressions coincide field by field.
/-- When the curvature parameter is fixed to `L_f`, the general FISTA state update agrees with the
constant-stepsize FISTA update from Algorithm 10.13. -/
theorem fista_state_update_eq_constant_stepsize_state_update
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : PosReal) (state : FISTAState E) :
    fista_state_update f g Lf state =
      fista_constant_stepsize_state_update f g Lf state :=
  rfl

/-- Algorithm 10.6: for a real-valued smooth term `f`, a proper closed convex regularizer `g`,
an initial point `x^0 = x0`, and positive curvature estimates `L_k`, the FISTA recursion is the
state sequence whose `k`-th state stores `(x^(k-1), x^k, t_k)`, starts from
`(x^0, x^0, 1)`, and evolves by the extrapolation-plus-prox-gradient update with parameter
`L_k`. -/
def fista
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    ℕ → FISTAState E
  | 0 => fista_initial_state x0
  | k + 1 => fista_state_update f g (L k) (fista f g x0 L k)

/-- The FISTA iterate `x^k`, namely the current iterate field of the `k`-th FISTA state. -/
def fista_x
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : E :=
  (fista f g x0 L k).xCur

/-- The FISTA momentum parameter `t_k`, namely the momentum field of the `k`-th FISTA state. -/
def fista_t
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : ℝ :=
  (fista f g x0 L k).tCur

/-- The FISTA extrapolated point `y^k` obtained from the `k`-th FISTA state. -/
def fista_y
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : E :=
  fista_extrapolated_point (fista f g x0 L k)

-- Proof sketch: unfold `fista` at the base index `0`; the initial state's current iterate is
-- definitionally `x0`.
/-- FISTA starts from the initial iterate `x^0 = x0`. -/
@[simp] theorem fista_x_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_x f g x0 L 0 = x0 :=
  rfl

-- Proof sketch: unfold `fista` at the base index `0`; the initial state's momentum field is
-- definitionally `1`.
/-- The initial FISTA momentum parameter is `t_0 = 1`. -/
@[simp] theorem fista_t_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_t f g x0 L 0 = 1 :=
  rfl

-- Proof sketch: at the initial state one has `x^{-1} = x^0 = x0` and `t_0 = 1`, so the
-- extrapolation coefficient vanishes and the extrapolated point reduces to `x0`.
/-- The initial FISTA extrapolated point satisfies `y^0 = x^0 = x0`. -/
@[simp] theorem fista_y_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_y f g x0 L 0 = x0 := by
  -- Unfold the initial state and reduce the extrapolation coefficient to zero.
  simp [fista_y, fista, fista_initial_state, fista_extrapolated_point, fista_momentum_update]

-- Proof sketch: unfold `fista` at `k + 1`; by definition, the current iterate field of the
-- updated state is the prox-gradient point `T_(L_k)(y^k)`.
/-- Each FISTA successor iterate satisfies
`x^(k+1) = T_(L_k)(y^k)`. -/
theorem fista_x_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_x f g x0 L (k + 1) =
      T[L k; f, g] (fista_y f g x0 L k) :=
  rfl

-- Proof sketch: unfold `fista` at `k + 1`; the updated state's momentum field is
-- `fista_momentum_update t_k` by definition.
/-- The FISTA momentum sequence satisfies
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem fista_t_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_t f g x0 L (k + 1) =
      fista_momentum_update (fista_t f g x0 L k) :=
  rfl

-- Proof sketch: unfold `fista` at `k + 1`; the extrapolated point of the updated state is
-- definitionally the standard FISTA formula built from `x^(k+1)`, `x^k`, `t_(k+1)`, and
-- `t_(k+2)`.
/-- The FISTA extrapolated sequence satisfies
`y^(k+1) = x^(k+1) + ((t_(k+1) - 1) / t_(k+2)) (x^(k+1) - x^k)`. -/
theorem fista_y_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_y f g x0 L (k + 1) =
      fista_x f g x0 L (k + 1) +
        ((fista_t f g x0 L (k + 1) - 1) / fista_t f g x0 L (k + 2)) •
          (fista_x f g x0 L (k + 1) - fista_x f g x0 L k) := by
  rw [show fista_t f g x0 L (k + 2) = fista_momentum_update (fista_t f g x0 L (k + 1)) by
    simpa [Nat.add_assoc] using fista_t_succ f g x0 L (k + 1)]
  rfl

/-- The canonical B2 upper-model acceptance predicate for `f.toEReal` at the bridge point
`interior_effective_domain_point_of_real f y` is exactly the displayed FISTA upper-model
inequality `(10.39)` at `y`. -/
theorem proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal) (y : E) :
    proximal_gradient_backtracking_B2_accepts
      f.toEReal g L (interior_effective_domain_point_of_real f y) ↔
  let xNext := T[L; f, g] y
  f xNext ≤
    f y +
      inner ℝ (∇ f y) (xNext - y) +
      ((L : ℝ) / 2) * ‖xNext - y‖ ^ (2 : ℕ) := by
  -- Unfold the B2 predicate and isolate the final `EReal`-to-`ℝ` coercion bridge.
  simp only [proximal_gradient_backtracking_B2_accepts, prox_gradient_operator_apply,
    Function.toEReal, interior_effective_domain_point_of_real]
  constructor
  · intro h
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [add_assoc] using h
  · intro h
    exact EReal.coe_le_coe_iff.mpr <| by
      simpa [add_assoc] using h

/-- A stepsize schedule uses backtracking procedure B3 along a point sequence `y` when, at every
iteration `k`, the accepted curvature estimate `L_k` is the first accepted geometric trial based
on `s` at `k = 0` and on `L_(k-1)` at later steps, evaluated at the point `y^k`. -/
def uses_backtracking_procedure_B3_rule
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (y : ℕ → E) (L : ℕ → PosReal) (s : PosReal)
    (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    is_backtracking_procedure_B2_index
      f.toEReal g
      (proximal_gradient_backtracking_B2_previous_stepsize s L k) η
      (interior_effective_domain_point_of_real f (y k)) i ∧
    L k =
      proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i

-- Proof sketch: specialize `uses_backtracking_procedure_B3_rule` at the iteration `k`; the chosen
-- index `i` is accepted by `is_backtracking_procedure_B2_index_accepts` for the canonical
-- Chapter 10 B2 owner applied to `f.toEReal` at `interior_effective_domain_point_of_real f (y k)`.
-- The bridge theorem
-- `proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model` then rewrites this canonical
-- acceptance predicate as the displayed FISTA upper-model inequality.
/-- Under backtracking procedure B3, the chosen stepsize `L_k` satisfies the displayed
quadratic upper-model inequality `(10.39)` at the point `y^k`. -/
theorem uses_backtracking_procedure_B3_rule_accepts
    {f : E → ℝ} {g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] {y : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_backtracking_procedure_B3_rule f g y L s η)
    (k : ℕ) :
    let xNext := T[L k; f, g] (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  -- Extract the accepted B2 trial produced by the B3 rule at step `k`.
  rcases hrule k with ⟨i, hi, hLk⟩
  have haccepts :
      proximal_gradient_backtracking_B2_accepts
        f.toEReal g
        (proximal_gradient_backtracking_trial_stepsize
          (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i)
        (interior_effective_domain_point_of_real f (y k)) :=
    is_backtracking_procedure_B2_index_accepts hi
  -- Rewrite the accepted B2 predicate into the displayed FISTA upper-model inequality.
  simpa [hLk] using
    (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model
      (f := f)
      (g := g)
      (L := proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i)
      (y := y k)).mp haccepts

/-- The constant/B3 stepsize rule in the fast proximal-gradient analysis: either every
`L_k = L_f`, giving `α = 1`, or the schedule is produced by backtracking procedure B3 along the
point sequence `y`, with `α = max {η, s / L_f}`. The B3 branch records `0 < L_f` explicitly so
the quotient `s / L_f` remains faithful to the textbook constant rather than Lean's
division-by-zero convention. -/
def fast_proximal_gradient_sublinear_rate_stepsize_rule
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (y : ℕ → E) (L : ℕ → PosReal) (α : ℝ) : Prop :=
  (α = 1 ∧ uses_proximal_gradient_Lf_stepsize_rule Lf L) ∨
    ∃ _hLf : 0 < (Lf : ℝ), ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ)) ∧
        uses_backtracking_procedure_B3_rule f g y L s η

-- Proof sketch: in the constant branch, `L_0 = L_f` and `L_0` is positive because it is a
-- `PosReal`. In the B3 branch, the required positivity witness is stored explicitly in the rule.
/-- The shared fast proximal-gradient stepsize rule forces the smoothness constant `L_f` to be
positive. -/
theorem fast_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {y : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf y L α) :
    0 < (Lf : ℝ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨hLf, _, _, _, _⟩
  · exact uses_proximal_gradient_Lf_stepsize_rule_lf_pos hLf_rule
  · exact hLf

-- Proof sketch: in the constant-rule case, use the global `L_f`-smoothness inequality at `y^k`
-- and specialize `uses_proximal_gradient_Lf_stepsize_rule Lf L` at `k`. In the
-- backtracking case, the conclusion is exactly
-- `uses_backtracking_procedure_B3_rule_accepts hrule k`.
/-- If the curvature estimates are chosen either by the constant rule `L_k = L_f` or by
backtracking procedure B3 encoded by
`fast_proximal_gradient_sublinear_rate_stepsize_rule`, then the quadratic upper-model inequality
`(10.39)` holds at every point `y^k`. -/
theorem fast_proximal_gradient_sublinear_rate_stepsize_rule_accepts
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    {α : ℝ}
    {y : ℕ → E} {L : ℕ → PosReal}
    (hrule : fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf y L α)
    (k : ℕ) :
    let xNext := T[L k; f, g] (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  rcases hrule with ⟨_, hLconst⟩ | ⟨_, s, η, _, hB3⟩
  · -- In the constant branch, the global `L_f`-smoothness bound applies on `Set.univ`.
    let xNext := T[L k; f, g] (y k)
    have hy_mem : y k ∈ Set.univ := by
      simp
    have hxNext_mem : xNext ∈ Set.univ := by
      simp [xNext]
    -- Specialize the descent lemma to the pair `(y^k, T_(L_k)(y^k))`.
    simpa [xNext, hLconst k, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        (L := Lf)
        (D := Set.univ)
        (f := f)
        convex_univ
        hf_smooth
        hy_mem
        hxNext_mem)
  · -- In the backtracking branch, B3 acceptance is exactly the required inequality.
    exact uses_backtracking_procedure_B3_rule_accepts hB3 k

variable {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

namespace IsFastProximalGradientProblem

/-- Bridge/view layer: Assumption 10.31 canonically supplies the `g`-regularity data required by
the shared constant/B3 sublinear-rate stepsize owner from Algorithm 10.6. -/
abbrev SublinearRateStepsizeRule
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (y : ℕ → E) (L : ℕ → PosReal) (α : ℝ) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf y L α

/-- The canonical fast-problem bridge owner `SublinearRateStepsizeRule` already includes
positivity of the smoothness constant `L_f`. -/
theorem sublinearRateStepsizeRule_lf_pos
    {hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf}
    {y : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule y L α) :
    0 < (Lf : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [SublinearRateStepsizeRule] using
    fast_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos f g Lf hrule

/-- Under Assumption 10.31, the owner-level fast stepsize bridge supplies the FISTA upper-model
inequality `(10.39)` at every point `y^k`. -/
theorem sublinearRateStepsizeRule_accepts
    {hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf}
    {α : ℝ} {y : ℕ → E} {L : ℕ → PosReal}
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (k : ℕ) :
    letI : IsProperExtendedRealFunction g := hproblem.g_proper
    letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
    letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
    let xNext := T[L k; f, g] (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [SublinearRateStepsizeRule] using
    fast_proximal_gradient_sublinear_rate_stepsize_rule_accepts f g Lf hproblem.f_smooth hrule k

end IsFastProximalGradientProblem

end
