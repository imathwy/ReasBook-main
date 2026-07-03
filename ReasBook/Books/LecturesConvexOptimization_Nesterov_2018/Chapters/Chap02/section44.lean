

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_44 (from Chap02) -/
noncomputable section

universe u

open scoped StrongConvexSmooth

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

/- Definition 2.44 lies in the domain of smooth inequality-constrained minimization on a real
Hilbert space.

Sampled owner-style declarations:
* `LagrangianProblem E m` in `Chap01/Definition_1_10_2`, which already owns the primitive
  objective-and-constraint data `f₀, fᵢ`;
* `FunctionalConstraintsMinimizationProblem E m` in `Chap01/Definition_1_1_3`, which owns the
  feasible-set predicate and `IsMinOn` surface for finite scalar constraints on an ambient set;
* `𝓢[μ, L]¹¹`, `IsStrongConvexSmoothObjective μ L`, and `mem_S11_iff` in `Definition_2_17`,
  which own the source-facing and canonical regularity interfaces for `f₀` and each `fᵢ`.

Best owner abstraction:
* the primitive objective-and-constraint owner is `LagrangianProblem E m`;
* the feasible-set/optimality bridge is `FunctionalConstraintsMinimizationProblem E m`.

Primitive data:
* the ambient set `Q ⊆ E` together with its nonemptiness, closedness, and convexity;
* the inherited `LagrangianProblem E m` data `objective` and `constraints`;
* the regularity fields `objective_mem` and `constraints_mem`, stated in the chapter notation
  `𝓢[μ, L]¹¹`.

Derived API:
* the canonical parent projection `problem.toLagrangianProblem`;
* the owner feasible-set bridge `problem.toFunctionalConstraintsMinimizationProblem`;
* the feasible-set rewrite `problem.mem_feasibleSet_iff`.

Source/core/bridge triage:
* source-facing: `SmoothFunctionalConstraintsMinimizationProblem`;
* core/canonical: `LagrangianProblem E m` and `FunctionalConstraintsMinimizationProblem E m`;
* bridge/view: `toFunctionalConstraintsMinimizationProblem`.

Accordingly this file keeps only the ambient-set and regularity data specific to Definition 2.44
and reuses the Chapter 1 Lagrangian owner for the primitive functional data. The textbook
`ℝⁿ` presentation is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/

/-- Definition 2.44: a smooth convex constrained minimization problem with parameters `μ` and `L`
consists of a nonempty simple closed convex set `Q ⊆ E`, an objective `f₀ : E → ℝ`, and
constraint functions `fᵢ : E → ℝ` for `i = 1, …, m`, where every component belongs to
`𝓢[μ, L]¹¹`; the associated problem is to minimize `f₀` over points `x ∈ Q` satisfying
`fᵢ(x) ≤ 0` for all constraints. The textbook `ℝⁿ` case is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
structure SmoothFunctionalConstraintsMinimizationProblem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (μ L : ℝ)
    extends LagrangianProblem E m where
  /-- The ambient closed convex set `Q ⊆ E` on which the constrained problem is posed. -/
  ambientSet : Set E
  /-- The ambient set `Q` is nonempty. -/
  ambient_nonempty : ambientSet.Nonempty
  /-- The ambient set `Q` is closed. -/
  ambient_closed : IsClosed ambientSet
  /-- The ambient set `Q` is convex. -/
  ambient_convex : Convex ℝ ambientSet
  /-- The objective belongs to the smooth strongly convex class `𝓢[μ, L]¹¹`. -/
  objective_mem : objective ∈ 𝓢[μ, L]¹¹
  /-- Every constraint component belongs to the same smooth strongly convex class `𝓢[μ, L]¹¹`. -/
  constraints_mem : ∀ i : Fin m, constraints i ∈ 𝓢[μ, L]¹¹

/-- A smooth constrained minimization problem can be used as its ambient objective function. -/
instance : CoeFun (SmoothFunctionalConstraintsMinimizationProblem E m μ L) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

namespace SmoothFunctionalConstraintsMinimizationProblem

@[simp] theorem coe_apply
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (x : E) :
    problem x = problem.objective x :=
  rfl

/- The Chapter 1 owner abstraction attached to the ambient functional-constraint data, with all
constraint senses equal to `≤`. -/
def toFunctionalConstraintsMinimizationProblem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) :
    FunctionalConstraintsMinimizationProblem E m where
  basicFeasibleSet := problem.ambientSet
  objective := fun x ↦ problem.objective x
  constraints := fun i x ↦ problem.constraints i x
  senses := fun _ ↦ .le

/-- The owner bridge has only inequality constraints. -/
@[simp] theorem toFunctionalConstraintsMinimizationProblem_hasLeConstraints
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) :
    problem.toFunctionalConstraintsMinimizationProblem.HasLeConstraints :=
  fun _ ↦ rfl

/-- Membership in the owner feasible set is exactly satisfaction of the inequality constraints on
the ambient set `Q`. -/
@[simp]
theorem mem_feasibleSet_iff
    {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}
    {x : problem.ambientSet} :
    x ∈ problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↔
      ∀ i : Fin m, problem.constraints i x ≤ 0 := by
  simpa [toFunctionalConstraintsMinimizationProblem] using
    (problem.toFunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff
      problem.toFunctionalConstraintsMinimizationProblem_hasLeConstraints)

/- A global minimizer of Definition 2.44 is expressed directly by the Chapter 1 owner predicate
`IsMinOn
    problem.toFunctionalConstraintsMinimizationProblem.objective
    problem.toFunctionalConstraintsMinimizationProblem.feasibleSet
    xStar`
for `xStar : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet`.

No additional wrapper declaration is needed here. -/

end SmoothFunctionalConstraintsMinimizationProblem

/-! ### Theorem_2_44 (from Chap02) -/
open scoped Gradient MaxTypeStep

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {μ : ℝ} {L : NNRealˣ}

/- Primary domain: constant-step minimax gradient trajectories for smooth minimax problems on a
closed convex feasible set in a proper real inner-product space.

Owner declarations sampled for this refinement:
* `SmoothMinimaxProblem` in `Definition_2_38`, which owns the feasible set, component family, and
  affine max-type approximation;
* `constantStepMinimaxGradientMethod` and
  `constantStepMinimaxGradientMethod_succ` in `Algorithm_2_8`, which own the source-facing
  recursive Algorithm 2.8 trajectory and its textbook recurrence
  `xₖ₊₁ = xₖ - h • g_f(xₖ; L)`;
* `SmoothMinimaxProblem.objective_lower_bound_of_isMinOn_regularizedAffineApproximation` in
  `Theorem_2_42`, which gives the owner one-step lower bound from an exact minimizer of the
  regularized affine model;
* `maxTypeGradientMapping`, `maxTypeGradientMapping_isMinOn`, and `maxTypeReducedGradient` in
  `Remark_2_41_1`, which supply the canonical chosen exact step and reduced-gradient residual.

Best owner abstraction:
* the smooth minimax owner `problem : SmoothMinimaxProblem E ι μ (L : ℝ)` together with the
  source-facing recursive trajectory
  `constantStepMinimaxGradientMethod problem.feasibleSet ... problem.components L x0 h hh`;
* its companion exact-step minimizer predicate and reduced-gradient field from `Remark_2_41_1`.

Primitive data:
* the owner problem `problem`;
* the positive inverse-stepsize parameter `L`;
* one minimizer `xStar` of `problem` on `problem.feasibleSet`;
* the feasible initial point `x0`;
* the positive step size `h`;
* the admissible feasibility bound `h ≤ 1 / L`.

Derived API:
* the recursive trajectory generated by
  `constantStepMinimaxGradientMethod problem.feasibleSet problem.feasible_closed
    problem.feasible_convex problem.components L x0 h hh`;
* the exact-step point `x_f(xBar; L)` and residual field `g_f(xBar; L)`;
* the source-facing recurrence theorems
  `constantStepMinimaxGradientMethod_zero` and `constantStepMinimaxGradientMethod_succ`;
* the geometric squared-distance estimate of Theorem 2.44.

Source/core/bridge triage:
* source-facing: Theorem 2.44 as the linear-convergence statement for the recursive
  constant-step minimax trajectory;
* core/canonical: `SmoothMinimaxProblem`, `constantStepMinimaxGradientMethod`, and the owner
  exact-step predicate above;
* bridge/view: using `Remark_2_41_1` to recognize the abstract exact residual field as the
  textbook reduced gradient when a chosen exact step is needed, together with the recurrence
  theorems exported by `Algorithm_2_8`.

This refinement removes the previous local `gradientMappingRelaxedStep` /
`gradientMappingRelaxedMethod` duplicate API over single-objective constrained problems. Theorem
2.44 now lives directly over the smooth minimax owner and the chapter’s source-facing recursive
Algorithm 2.8 trajectory in the same proper inner-product-space / finite-index ambient layer
already used by those owner declarations. -/

namespace SmoothMinimaxProblem

section

variable (problem : SmoothMinimaxProblem E ι μ (L : ℝ))

local notation "Q" => problem.feasibleSet
local instance : Fact (Set.Nonempty Q) := ⟨problem.feasible_nonempty⟩
local instance : Fact (IsClosed Q) := ⟨problem.feasible_closed⟩
local instance : Fact (Convex ℝ Q) := ⟨problem.feasible_convex⟩

private theorem constantStepMinimaxGradient_sqdist_step_le
    [Nontrivial E]
    {xStar : E} (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn problem Q xStar)
    {h : NNRealˣ} (hh : (h : ℝ) ≤ 1 / (L : ℝ))
    (xBar : Q) :
    let g := g_f[Q | problem.components; L] ((xBar : E))
    ‖((xBar : E) - (h : ℝ) • g - xStar)‖ ^ (2 : ℕ) ≤
      (1 - μ * (h : ℝ)) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) := by
  let xPlus := x_f[Q | problem.components; L] ((xBar : E))
  let g := g_f[Q | problem.components; L] ((xBar : E))
  have hxPlus_data := maxTypeGradientMapping_mem_and_isMinOn_ofFact
    Q problem.components (xBar : E) L
  have hxPlus_mem : xPlus ∈ Q := by simpa [xPlus] using hxPlus_data.1
  have hxPlus :
      IsMinOn
        (quadraticallyRegularizedObjective (problem.affineApproximation (xBar : E)) L (xBar : E))
        Q
        xPlus := by
    simpa [xPlus] using hxPlus_data.2
  have hbound :=
    objective_lower_bound_of_isMinOn_regularizedAffineApproximation
      problem
      (xBar : E)
      le_rfl
      hxStar_mem
      hxPlus_mem
      hxPlus
  have hobj : problem xStar ≤ problem xPlus := (isMinOn_iff.mp hxStar) xPlus hxPlus_mem
  have hinner :
      (1 / (2 * (L : ℝ))) * ‖g‖ ^ (2 : ℕ) +
          (μ / 2) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) ≤
        inner ℝ g ((xBar : E) - xStar) := by
    have hbound' :
        problem xStar ≥
          problem xPlus +
            inner ℝ g (xStar - xBar) +
            (1 / (2 * (L : ℝ))) * ‖g‖ ^ (2 : ℕ) +
            (μ / 2) * ‖xStar - (xBar : E)‖ ^ (2 : ℕ) := by
      simpa [g, xPlus, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbound
    have hinner_neg :
        inner ℝ g (xStar - (xBar : E)) +
            (1 / (2 * (L : ℝ))) * ‖g‖ ^ (2 : ℕ) +
            (μ / 2) * ‖xStar - (xBar : E)‖ ^ (2 : ℕ) ≤ 0 := by
      have hmain :
          inner ℝ g (xStar - (xBar : E)) +
              (1 / (2 * (L : ℝ))) * ‖g‖ ^ (2 : ℕ) +
              (μ / 2) * ‖xStar - (xBar : E)‖ ^ (2 : ℕ) ≤
            problem xStar - problem xPlus := by
        nlinarith [hbound']
      have hdiff : problem xStar - problem xPlus ≤ 0 := by
        nlinarith [hobj]
      exact le_trans hmain hdiff
    have hflip : inner ℝ g (xStar - (xBar : E)) = -inner ℝ g ((xBar : E) - xStar) := by
      rw [show xStar - (xBar : E) = -((xBar : E) - xStar) by abel, inner_neg_right]
    have hsq : ‖xStar - (xBar : E)‖ ^ (2 : ℕ) = ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    have hinner_neg' :
        -inner ℝ g ((xBar : E) - xStar) +
            (1 / (2 * (L : ℝ))) * ‖g‖ ^ (2 : ℕ) +
            (μ / 2) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [hflip, hsq] using hinner_neg
    nlinarith [hinner_neg']
  have hh_nonneg : 0 ≤ (h : ℝ) := by positivity
  have hh_sq :
      (h : ℝ) ^ (2 : ℕ) ≤ (h : ℝ) / (L : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hh hh_nonneg
    simpa [pow_two, div_eq_mul_inv, mul_assoc] using hmul
  have hgrad_nonpos :
      ((h : ℝ) ^ (2 : ℕ) - (h : ℝ) / (L : ℝ)) * ‖g‖ ^ (2 : ℕ) ≤ 0 := by
    have hcoeff : (h : ℝ) ^ (2 : ℕ) - (h : ℝ) / (L : ℝ) ≤ 0 := sub_nonpos.mpr hh_sq
    nlinarith
  have hexpand :
      ‖((xBar : E) - (h : ℝ) • g - xStar)‖ ^ (2 : ℕ) =
        ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) -
          2 * (h : ℝ) * inner ℝ g ((xBar : E) - xStar) +
          (h : ℝ) ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
    calc
      ‖((xBar : E) - (h : ℝ) • g - xStar)‖ ^ (2 : ℕ)
          = ‖(((xBar : E) - xStar) - (h : ℝ) • g)‖ ^ (2 : ℕ) := by
              congr 1
              abel_nf
      _ = ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) -
            2 * inner ℝ ((xBar : E) - xStar) ((h : ℝ) • g) +
            ‖(h : ℝ) • g‖ ^ (2 : ℕ) := by
            simpa using norm_sub_sq_real (((xBar : E) - xStar)) ((h : ℝ) • g)
      _ = ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) -
            2 * (h : ℝ) * inner ℝ g ((xBar : E) - xStar) +
            (h : ℝ) ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, real_inner_comm]
            simp [norm_smul, Real.norm_of_nonneg hh_nonneg, sq]
            ring
  have hscaled :
      (h : ℝ) / (L : ℝ) * ‖g‖ ^ (2 : ℕ) + μ * (h : ℝ) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) ≤
        2 * (h : ℝ) * inner ℝ g ((xBar : E) - xStar) := by
    have hscaled' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * (h : ℝ))
    ring_nf at hscaled' ⊢
    exact hscaled'
  calc
    ‖((xBar : E) - (h : ℝ) • g - xStar)‖ ^ (2 : ℕ)
        = ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) -
            2 * (h : ℝ) * inner ℝ g ((xBar : E) - xStar) +
            (h : ℝ) ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := hexpand
    _ ≤ ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) -
          ((h : ℝ) / (L : ℝ) * ‖g‖ ^ (2 : ℕ) +
            μ * (h : ℝ) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ)) +
          (h : ℝ) ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
            nlinarith [hscaled]
    _ = (1 - μ * (h : ℝ)) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) +
          ((h : ℝ) ^ (2 : ℕ) - (h : ℝ) / (L : ℝ)) * ‖g‖ ^ (2 : ℕ) := by
            ring
    _ ≤ (1 - μ * (h : ℝ)) * ‖((xBar : E) - xStar)‖ ^ (2 : ℕ) := by
            nlinarith [hgrad_nonpos]

private theorem constantStepMinimaxGradientSequence_sqdist_le_geometric_nontrivial
    [Nontrivial E]
    {xStar : E} (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn problem Q xStar)
    {x0 : Q} {h : NNRealˣ}
    (hh : (h : ℝ) ≤ 1 / (L : ℝ))
    (k : ℕ) :
    let x :=
      constantStepMinimaxGradientMethod
        Q
        problem.feasible_closed
        problem.feasible_convex
        problem.components
        L
        x0
        h
        hh
    ‖((x k : E) - xStar)‖ ^ (2 : ℕ) ≤
      (1 - μ * (h : ℝ)) ^ k * ‖((x0 : E) - xStar)‖ ^ (2 : ℕ) := by
  let x :=
    constantStepMinimaxGradientMethod
      Q
      problem.feasible_closed
      problem.feasible_convex
      problem.components
      L
      x0
      h
      hh
  let r : ℕ → ℝ := fun j ↦ ‖((x j : E) - xStar)‖ ^ (2 : ℕ)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hμL : μ ≤ (L : ℝ) := (mem_S11_iff.mp (problem.components_mem i0)).mu_le_L
  have hq₁ : μ * (h : ℝ) ≤ 1 := by
    have hLh : (L : ℝ) * (h : ℝ) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (L : ℝ))
      simpa [div_eq_inv_mul, mul_assoc] using hmul
    have hμh : μ * (h : ℝ) ≤ (L : ℝ) * (h : ℝ) := by
      exact mul_le_mul_of_nonneg_right hμL (by positivity)
    exact le_trans hμh hLh
  have hstep : ∀ j : ℕ, r (j + 1) ≤ (1 - μ * (h : ℝ)) * r j := by
    intro j
    dsimp [r]
    simpa [x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      problem.constantStepMinimaxGradient_sqdist_step_le
        hxStar_mem
        hxStar
        hh
        (x j)
  have hgeom :
      HasGeometricRateOfConvergence r (μ * (h : ℝ)) (r 0) := by
    refine HasGeometricRateOfConvergence.of_step_bound hq₁ le_rfl hstep
  simpa [r, x, mul_comm, mul_left_comm, mul_assoc] using hgeom k

/-- Theorem 2.44: for the recursive Algorithm 2.8 trajectory of a smooth minimax problem, the
squared distance to any feasible minimizer `xStar` decays geometrically as
`‖x_k - xStar‖² ≤ (1 - μ h)^k ‖x₀ - xStar‖²` whenever `h ≤ 1 / L`, with the primitive positive
step size owned canonically as `h : NNRealˣ`. Feasibility is encoded by the subtype-valued
trajectory `constantStepMinimaxGradientMethod ... : ℕ → problem.feasibleSet`, while the target
minimizer keeps the canonical constrained-minimization data
`xStar ∈ problem.feasibleSet` and `IsMinOn problem problem.feasibleSet xStar`. -/
-- Proof sketch: fix `k` and let
-- `xPlus = x_f[Q | problem.components; L](x k)`. Apply
-- `objective_lower_bound_of_isMinOn_regularizedAffineApproximation` to `x = xStar`,
-- `xBar = x k`, `hx = hxStar_mem`, and the owner exact-step theorem for `xPlus`. Since `xStar`
-- minimizes `problem` on `Q`, the objective terms collapse to the lower bound
-- `⟪g_f(x k; L), x k - xStar⟫ ≥ (1 / (2 * L)) ‖g_f(x k; L)‖² +
--   (μ / 2) ‖x k - xStar‖²`.
-- Expand
-- `‖x (k + 1) - xStar‖² = ‖x k - xStar - h • g_f[Q | problem.components; L](x k)‖²` using
-- `constantStepMinimaxGradientMethod_succ`, insert the inner-product bound, and use `h ≤ 1 / L`
-- to make the remaining
-- gradient-norm contribution
-- nonpositive. Iterating the one-step contraction gives the stated geometric estimate.
theorem constantStepMinimaxGradientSequence_sqdist_le_geometric
    {xStar : E} (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn problem Q xStar)
    {x0 : Q} {h : NNRealˣ}
    (hh : (h : ℝ) ≤ 1 / (L : ℝ))
    (k : ℕ) :
    let x :=
      constantStepMinimaxGradientMethod
        Q
        problem.feasible_closed
        problem.feasible_convex
        problem.components
        L
        x0
        h
        hh
    ‖((x k : E) - xStar)‖ ^ (2 : ℕ) ≤
      (1 - μ * (h : ℝ)) ^ k * ‖((x0 : E) - xStar)‖ ^ (2 : ℕ) := by
  let x :=
    constantStepMinimaxGradientMethod
      Q
      problem.feasible_closed
      problem.feasible_convex
      problem.components
      L
      x0
      h
      hh
  by_cases hE : Subsingleton E
  · have hxk : (x k : E) = xStar := hE.elim _ _
    have hx0' : (x0 : E) = xStar := hE.elim _ _
    simp [x, hxk, hx0']
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    simpa [x] using
      problem.constantStepMinimaxGradientSequence_sqdist_le_geometric_nontrivial
        hxStar_mem
        hxStar
        hh
        k

end

end SmoothMinimaxProblem
