import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_6_2 (from Chap01) -/
noncomputable section

/- Definition 1.6.2 is a source-facing recall in the gradient-method step-size domain.

Layer targeted by this refinement:
* source-facing recall of the owner schedule type already used by `gradientMethod`

Primary domain:
* preselected scalar schedules for first-order methods

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`, whose primitive input already includes
  `stepSize : ℕ → ℝ`
* `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`, which treats a schedule as owner
  data and adds optimization properties only as predicates
* `DampedNewton.Method.stepSize` in `Algorithm_1_7_2.lean`, which likewise stores the schedule
  directly as `ℕ → ℝ`
* the constant-step bridge `gradientMethod_const_eq_iterate` in `Algorithm_1_6_1.lean`, which
  uses the literal schedule `fun _ ↦ α` rather than a separate wrapper owner

Source/core/bridge triage:
* source-facing: the prescribed step-size rule `k ↦ hₖ`
* core/canonical: the schedule type `ℕ → ℝ`
* bridge/view: direct literal schedules such as `fun _ ↦ h` or `fun k ↦ h / Real.sqrt (k + 1)`

Owner abstraction:
* the preselected schedule type `ℕ → ℝ`

Primitive data:
* only the scalar rule `k ↦ hₖ`

Derived API:
* positivity and stronger analytic side conditions on a schedule
* textbook examples, which should remain direct literal schedules rather than separate public
  owners

This file therefore keeps the main entry as the canonical type expression itself and shows the
textbook constant and inverse-square-root schedules directly by literal functions. It introduces
no separate public wrapper for either example. -/

#check (ℕ → ℝ)

variable (h : ℝ)

#check ((fun _ ↦ h) : ℕ → ℝ)
#check ((fun k ↦ h / Real.sqrt (k + 1)) : ℕ → ℝ)

end

/-! ### Definition_1_6_3 (from Chap01) -/
universe u

open scoped Gradient

noncomputable section

/-
Definition 1.6.3 lies in the exact line-search domain for first-order trajectories on real vector
spaces.

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`, the chapter owner of the gradient trajectory;
* `IsMinOn`, the mathlib owner predicate for constrained minimizers on a feasible set;
* `HasGradientAt`, the chapter/mathlib owner predicate for a genuine gradient witness at a point;
* the later reuse of the same trajectory-level owner shape in
  `NonlinearConjugateGradientMethod.lineSearch` from `Algorithm_1_9_9.lean`.

Source/core/bridge triage:
* source-facing: `SatisfiesExactLineSearch`, the textbook exact line-search rule for a gradient
  trajectory, including genuine gradient existence at each iterate;
* core/canonical: the pair of owner predicates `DifferentiableAt` and
  `SatisfiesExactLineSearchAlong`;
* bridge/view: the owner-derived accessors `differentiableAt`, `hasGradientAt`, `nonneg`, and
  `isMinOn`.

Primitive data:
* the objective `f`,
* a trajectory `xₖ`,
* a search-direction field `pₖ`,
* a step-size schedule `hₖ`.

Derived API:
* gradient existence and line-search accessors in the gradient specialization,
* nonnegativity of each `hₖ`,
* the minimizing property of `hₖ` for the one-variable line-search objective.

The generic owner `SatisfiesExactLineSearchAlong` intentionally does not mention gradients; it
records only a minimizing property along a prescribed direction field. The source-facing
gradient-method specialization must additionally assert differentiability at each iterate, because
mathlib's totalized `∇ f` alone would otherwise admit nondifferentiable objectives. The genuine
gradient statement for the displayed `∇ f (xₖ)` is then a derived owner theorem via
`DifferentiableAt.hasGradientAt`. -/

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-
The owner abstraction for exact line search in this chapter is the generic predicate on a real
vector space saying that a scalar schedule `hₖ` minimizes `f (xₖ - h pₖ)` over `h ≥ 0` along a
prescribed trajectory `xₖ` and direction field `pₖ`.

Definition 1.6.3 is the gradient-method specialization of this owner, with
`xₖ = gradientMethod stepSize f x0 k` and `pₖ = ∇ f (xₖ)`.

Algorithm 1.9.9 later reuses the same owner shape with the nonlinear conjugate-gradient search
directions.
-/

/-- A step-size schedule satisfies the exact line-search rule along the trajectory `xₖ` and search
directions `pₖ` when every `hₖ` is a nonnegative minimizer of `h ↦ f (xₖ - h • pₖ)` on
`[0, ∞)`. -/
def SatisfiesExactLineSearchAlong (f : X → ℝ) (x p : ℕ → X) (stepSize : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    stepSize k ∈ Set.Ici (0 : ℝ) ∧
      IsMinOn (fun h : ℝ ↦ f (x k - h • p k)) (Set.Ici (0 : ℝ)) (stepSize k)

namespace SatisfiesExactLineSearchAlong

/-- Every exact line-search step size is nonnegative. -/
theorem nonneg
    {f : X → ℝ} {x p : ℕ → X} {stepSize : ℕ → ℝ}
    (hexact : SatisfiesExactLineSearchAlong f x p stepSize) (k : ℕ) :
    stepSize k ∈ Set.Ici (0 : ℝ) :=
  (hexact k).1

/-- Every exact line-search step size minimizes the one-variable search objective over
`[0, ∞)`. -/
theorem isMinOn
    {f : X → ℝ} {x p : ℕ → X} {stepSize : ℕ → ℝ}
    (hexact : SatisfiesExactLineSearchAlong f x p stepSize) (k : ℕ) :
    IsMinOn (fun h : ℝ ↦ f (x k - h • p k)) (Set.Ici (0 : ℝ)) (stepSize k) :=
  (hexact k).2

end SatisfiesExactLineSearchAlong

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 1.6.3 is represented by the pair of canonical owner predicates

`∀ k : ℕ,
    DifferentiableAt ℝ f (x k)`

and

`∀ k : ℕ,
    stepSize k ∈ Set.Ici (0 : ℝ) ∧
      IsMinOn (fun h : ℝ ↦ f (x k - h • ∇ f (x k))) (Set.Ici (0 : ℝ)) (stepSize k)`.

The owner abstraction is the project's usual constrained-minimizer pattern: feasible-set
membership together with mathlib's `IsMinOn`, paired with iterate-wise differentiability so that
the displayed totalized gradient is genuine. The one-variable objective obtained by restricting
`f` to the antigradient ray is derived syntax, not separate primitive data. This is also the
chapter's generic exact line-search shape, specialized in later files by
`NonlinearConjugateGradientMethod.lineSearch`, where differentiability data is likewise carried
separately from the pure line-search minimization condition.
-/

/-- Definition 1.6.3: a step-size schedule `hₖ` satisfies the exact line-search rule for the
gradient-method trajectory started at `x₀` when the objective is differentiable at every iterate,
so the displayed antigradient direction is genuine, and every `hₖ` is a nonnegative minimizer of
the one-variable objective `h ↦ f (xₖ - h ∇ f(xₖ))` over `h ≥ 0`. -/
def SatisfiesExactLineSearch (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) : Prop :=
  let x := gradientMethod stepSize f x0
  (∀ k : ℕ, DifferentiableAt ℝ f (x k)) ∧
    SatisfiesExactLineSearchAlong f x (fun k ↦ ∇ f (x k)) stepSize

namespace SatisfiesExactLineSearch

variable {f : E → ℝ} {stepSize : ℕ → ℝ} {x0 : E}

local notation "traj" => gradientMethod stepSize f x0

/-- Along an exact-line-search gradient trajectory, the objective is differentiable at every
iterate. -/
theorem differentiableAt
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    DifferentiableAt ℝ f (traj k) := by
  simpa [SatisfiesExactLineSearch] using hexact.1 k

/-- Along an exact-line-search gradient trajectory, the displayed antigradient is the genuine
gradient at every iterate. -/
theorem hasGradientAt
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    HasGradientAt f (∇ f (traj k)) (traj k) :=
  (hexact.differentiableAt k).hasGradientAt

/-- `SatisfiesExactLineSearch` packages the generic line-search minimization condition along the
gradient-method trajectory. -/
theorem along
    (hexact : SatisfiesExactLineSearch f stepSize x0) :
    SatisfiesExactLineSearchAlong
      f
      traj
      (fun k ↦ ∇ f (traj k))
      stepSize := by
  simpa [SatisfiesExactLineSearch] using hexact.2

/-- Every exact line-search step size is nonnegative. -/
theorem nonneg
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    stepSize k ∈ Set.Ici (0 : ℝ) := by
  exact hexact.along.nonneg k

/-- Every exact line-search step size minimizes the antigradient line-search objective over
`h ≥ 0`. -/
theorem isMinOn
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    IsMinOn
      (fun h : ℝ ↦ f (traj k - h • ∇ f (traj k)))
      (Set.Ici (0 : ℝ))
      (stepSize k) := by
  exact hexact.along.isMinOn k

end SatisfiesExactLineSearch

end

/-! ### Definition_1_6_4 (from Chap01) -/
universe u

open scoped Gradient

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Layer targeted by this refinement:
* source-facing: `SatisfiesArmijoRule`
* core/canonical owner: `gradientMethod stepSize f x0`
* bridge/view: the projection lemmas `alpha_pos`, `stepSize_pos`, `bounds`, `lowerBound`,
  and `upperBound`

Primary domain:
* Armijo step-size rules for real-Hilbert-space gradient-method trajectories

Sampled owner-style declarations:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `gradientMethod_succ` in `Algorithm_1_6_1.lean`
* `SatisfiesExactLineSearch` and `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`

Owner abstraction:
* the canonical recursive trajectory `gradientMethod stepSize f x0`

Primitive data:
* the objective `f`
* the step-size schedule `stepSize`
* the initial point `x0`
* the Armijo parameters `α`, `β`
* differentiability of `f` at each iterate of the owner trajectory

Derived API:
* genuine gradient existence of the displayed `∇ f (xₖ)` at each iterate
* positivity of `α`
* the inequalities `α < β < 1`
* positivity of each step size
* the iterate-wise lower and upper Armijo bounds

Unlike exact line search, a bare predicate along an arbitrary trajectory does not record that
`stepSize k` actually produces the next iterate. Definition 1.6.4 is therefore kept directly as
the gradient-method specialization, with the update rule owned by `gradientMethod` itself.

The source text is written on `ℝⁿ`, but the defining conditions use only the ambient inner
product, the genuine gradient, and the owner trajectory. As in `Algorithm_1_6_1` and
`Definition_1_6_3`, the public owner is therefore refined to the real-Hilbert-space level rather
than kept on a concrete Euclidean model.
-/

section

variable (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) (α β : ℝ)

/-- Definition 1.6.4: a step-size schedule `hₖ` satisfies the Armijo rule for the gradient-method
trajectory started at `x₀` when the objective is differentiable at every iterate, so the
displayed `∇ f(xₖ)` is genuine, `0 < α < β < 1`, every step size is positive, and the
consecutive iterates satisfy the two-sided Armijo decrease bounds. -/
def SatisfiesArmijoRule (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) (α β : ℝ) : Prop :=
  let traj := gradientMethod stepSize f x0
  (∀ k : ℕ, DifferentiableAt ℝ f (traj k)) ∧
    0 < α ∧
    α < β ∧
    β < 1 ∧
    (∀ k : ℕ, 0 < stepSize k) ∧
    ∀ k : ℕ,
      α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
          f (traj k) - f (traj (k + 1)) ∧
        f (traj k) - f (traj (k + 1)) ≤
          β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1))

end

namespace SatisfiesArmijoRule

variable {f : E → ℝ} {stepSize : ℕ → ℝ} {x0 : E} {α β : ℝ}

local notation "traj" => gradientMethod stepSize f x0

/-- Along an Armijo trajectory, the objective is differentiable at every iterate. -/
theorem differentiableAt
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    DifferentiableAt ℝ f (traj k) := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  simpa using hArmijo.1 k

/-- Along an Armijo trajectory, the displayed antigradient is the genuine gradient at every
iterate. -/
theorem hasGradientAt
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    HasGradientAt f (∇ f (traj k)) (traj k) :=
  (hArmijo.differentiableAt k).hasGradientAt

/-- The Armijo rule forces the lower parameter to be positive. -/
theorem alpha_pos
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    0 < α := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, hα0, _, _, _, _⟩
  exact hα0

/-- The Armijo parameters satisfy `α < β`. -/
theorem alpha_lt_beta
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    α < β := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, hαβ, _, _, _⟩
  exact hαβ

/-- The upper Armijo parameter lies below `1`. -/
theorem beta_lt_one
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    β < 1 := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, hβ1, _, _⟩
  exact hβ1

/-- Every Armijo step size is positive. -/
theorem stepSize_pos
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    0 < stepSize k := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, _, hstep, _⟩
  exact hstep k

/-- The Armijo rule provides both comparison inequalities at each iterate. -/
theorem bounds
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
        f (traj k) - f (traj (k + 1)) ∧
      f (traj k) - f (traj (k + 1)) ≤
        β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, _, _, hbounds⟩
  simpa using hbounds k

/-- The lower Armijo comparison inequality. -/
theorem lowerBound
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
      f (traj k) - f (traj (k + 1)) := by
  rcases hArmijo.bounds k with ⟨hlow, _⟩
  exact hlow

/-- The upper Armijo comparison inequality. -/
theorem upperBound
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≤
      β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) := by
  rcases hArmijo.bounds k with ⟨_, hupp⟩
  exact hupp

end SatisfiesArmijoRule

/-- The constant zero objective with initial point `0` and unit step sizes satisfies the Armijo
rule for the canonical parameters `α = 1 / 4` and `β = 1 / 2`. -/
theorem zero_zero_constOne_satisfiesArmijoRule :
    SatisfiesArmijoRule (fun _ : E ↦ 0) (fun _ : ℕ ↦ 1) (0 : E)
      (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  dsimp [SatisfiesArmijoRule]
  refine ⟨?_, by positivity, by norm_num, by norm_num, ?_, ?_⟩
  · intro k
    exact
      (show DifferentiableAt ℝ (fun _ : E ↦ (0 : ℝ))
          ((gradientMethod (fun _ : ℕ ↦ (1 : ℝ)) (fun _ : E ↦ 0) (0 : E)) k) from
        differentiableAt_const (0 : ℝ))
  · intro k
    norm_num
  · intro k
    constructor <;> simp

end

/-! ### Definition_1_6_5 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.6.5 lies in the Chapter 1 black-box domain of lower-bounded unconstrained
`C^{1,1}_L` objectives.

Sampled owner-style declarations:
* `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in `Chap01/Definition_1_5_2`, the canonical
  objective-side owners of the `C^{1,1}_L` condition;
* `gradientMethod` in `Chap01/Algorithm_1_6_1`, whose owner abstraction already lives on a real
  complete inner-product space rather than on coordinates;
* `SatisfiesExactLineSearch` in `Chap01/Definition_1_6_3`, which keeps differentiability data on
  the owner layer instead of treating the totalized gradient as intrinsic;
* `DifferentiableAt.hasGradientAt` and
  `gradient_eq_zero_of_not_differentiableAt` in mathlib's gradient API, which show why the
  displayed `∇ f x` is source-faithful only under differentiability data;
* `BlackBoxOptimizationProblemClass` in `Chap01/Definition_1_2_4`, the owner of the model/oracle/
  stopping-criterion package.

Best owner abstraction:
* source-facing/core: an objective `f : E → ℝ` on a real complete inner-product space, together
  with
  `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and `BddBelow (Set.range f)`;
* bridge/view: the finite-dimensional black-box class `gStarProblemClass n L ε`, whose stopping
  criterion evaluates the source-facing stopping predicate on the underlying objective of a model
  point `f : {g : E → ℝ // g ∈ 𝒢⋆[L]}`.

Primitive data:
* the objective `f`
* the Lipschitz constant `L`

Derived API:
* the source-facing membership predicate `f ∈ 𝒢⋆[L]` for the textbook class `𝒢_*`
* `IsEpsilonSolution f x₀ ε x̄` for a plain objective `f : E → ℝ`
* `gStarProblemClass n L ε`

Source/core/bridge triage:
* source-facing: `f ∈ 𝒢⋆[L]` and `IsEpsilonSolution f x₀ ε x̄` for `f : E → ℝ`
* core/canonical: `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and `BddBelow (Set.range f)`
* bridge/view: `gStarProblemClass`. -/

variable {L : NNReal}

/-- Definition 1.6.5 (1): an objective `f : E → ℝ` belongs to the textbook class `𝒢_*` when
`f ∈ C^{1,1}_L` and `f` is bounded below. Specializing `E` to `ℝⁿ` recovers the textbook
formulation. -/
def IsGStar (f : E → ℝ) (L : NNReal) : Prop :=
  ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) ∧ BddBelow (Set.range f)

namespace GStarNotation

scoped notation:max "𝒢⋆[" L:arg "]" => setOf (fun f ↦ IsGStar f L)

end GStarNotation

open scoped GStarNotation

/-- Unfolding `f ∈ 𝒢⋆[L]` gives the canonical conjunction of `C^{1,1}_L` regularity and
lower boundedness. -/
@[simp] theorem isGStar_iff
    (f : E → ℝ) (L : NNReal) :
    f ∈ 𝒢⋆[L] ↔ ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) ∧ BddBelow (Set.range f) :=
  Iff.rfl

namespace IsGStar

variable {f : E → ℝ} {L : NNReal}

/-- Membership in `𝒢_*` supplies the `C¹` regularity component of the objective. -/
theorem contDiff (h : f ∈ 𝒢⋆[L]) :
    ContDiff ℝ 1 f :=
  h.1

/-- Membership in `𝒢_*` supplies the global `L`-Lipschitz bound on the gradient. -/
theorem gradient_lipschitz (h : f ∈ 𝒢⋆[L]) :
    LipschitzWith L (∇ f) :=
  h.2.1

/-- Membership in `𝒢_*` supplies lower boundedness of the objective values. -/
theorem bddBelow (h : f ∈ 𝒢⋆[L]) :
    BddBelow (Set.range f) :=
  h.2.2

/-- Membership in `𝒢_*` supplies ordinary differentiability at every point. -/
theorem differentiableAt (h : f ∈ 𝒢⋆[L]) (x : E) :
    DifferentiableAt ℝ f x :=
  (contDiff h).differentiable_one x

/-- Membership in `𝒢_*` makes the displayed totalized gradient the genuine gradient. -/
theorem hasGradientAt (h : f ∈ 𝒢⋆[L]) (x : E) :
    HasGradientAt f (∇ f x) x :=
  (differentiableAt h x).hasGradientAt

end IsGStar

/-- A point `x̄` is an `ε`-solution for an objective `f` relative to the starting point `x₀`
when `f(x̄) ≤ f(x₀)` and `‖∇ f(x̄)‖ ≤ ε`. This source-facing stopping predicate lives on the
plain objective `f : E → ℝ`; when `f ∈ 𝒢⋆[L]`, the displayed gradient is source-faithful by
`IsGStar.hasGradientAt`. Specializing `E` to `ℝⁿ` recovers the textbook formulation. -/
def IsEpsilonSolution
    (f : E → ℝ) (x0 : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar ≤ f x0 ∧ ‖∇ f xBar‖ ≤ ε

/-- Unfolding `IsEpsilonSolution f x₀ ε x̄` gives the textbook conditions
`f(x̄) ≤ f(x₀)` and `‖∇ f(x̄)‖ ≤ ε`. -/
@[simp] theorem isEpsilonSolution_iff
    (f : E → ℝ) (x0 xBar : E) (ε : ℝ) :
    IsEpsilonSolution f x0 ε xBar ↔
      f xBar ≤ f x0 ∧ ‖∇ f xBar‖ ≤ ε :=
  Iff.rfl

section EuclideanBridge

variable {n : ℕ}

/-- Definition 1.6.5 (2): the textbook class `𝒢_*` at accuracy threshold `ε`, viewed as a
Chapter 1 black-box optimization problem class.
Its model is the subtype of lower-bounded unconstrained
`C^{1,1}_L(ℝⁿ)` objectives, its oracle is the canonical first-order answer map
`x ↦ (f x, ∇ f x)`, and its stopping criterion accepts exactly the triples `(f, x₀, x̄)` for
which `x̄` is an `ε`-solution for the model objective `f` relative to `x₀`. -/
def gStarProblemClass (n : ℕ) (L : NNReal) (ε : ℝ) :
    BlackBoxOptimizationProblemClass
      (EuclideanSpace ℝ (Fin n))
      (ℝ × EuclideanSpace ℝ (Fin n))
      ({ f : EuclideanSpace ℝ (Fin n) → ℝ // f ∈ 𝒢⋆[L] } ×
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) where
  model := { f : EuclideanSpace ℝ (Fin n) → ℝ // f ∈ 𝒢⋆[L] }
  oracle := fun f x ↦ (f.1 x, ∇ f.1 x)
  stoppingCriterion := {state | let ⟨f, x0, xBar⟩ := state
    IsEpsilonSolution f.1 x0 ε xBar}

local notation "En" => EuclideanSpace ℝ (Fin n)

/-- A state is accepted by `gStarProblemClass n L ε` exactly when its endpoint is an
`ε`-solution for the model objective relative to its starting point. -/
@[simp] theorem gStarProblemClass_stops_iff
    (f : { f : En → ℝ // f ∈ 𝒢⋆[L] }) (x0 xBar : En) :
    (f, x0, xBar) ∈ (gStarProblemClass n L ε).stoppingCriterion ↔
      IsEpsilonSolution f.1 x0 ε xBar := by
  rfl

variable {ε : ℝ}

/-- The oracle of `gStarProblemClass n L ε` is the canonical first-order answer map
`(f, x) ↦ (f x, ∇ f x)`. -/
@[simp] theorem gStarProblemClass_oracle_apply
    (f : { f : En → ℝ // f ∈ 𝒢⋆[L] }) (x : En) :
    (gStarProblemClass n L ε).oracle f x =
      (f.1 x, ∇ f.1 x) :=
  rfl

end EuclideanBridge

end

/-! ### Lemma_1_6_6 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}
variable (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))

include hf hgrad

/- Primary domain: one-step sufficient-decrease estimates for gradient descent on real Hilbert
spaces.

Relevant owner-style declarations sampled before refining:
* `firstOrderTaylorModelAt` in `FirstOrderTaylorModel.lean`, the chapter owner of the affine
  first-order model;
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Lemma_1_5_10.lean`, the canonical
  quadratic upper model under a Lipschitz gradient bound;
* `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` in `Proposition_1_6_7.lean`, the
  direct downstream iterate theorem obtained by applying the present pointwise specialization along
  a trajectory;
* `gradient_step_value_descent_of_lipschitzGradient` in `Chap02/Lemma_2_16.lean`, the weaker
  differentiable-plus-Lipschitz-gradient bridge that reuses this file rather than duplicating the
  descent calculation.

Source/core/bridge triage:
* source-facing: Lemma 1.6.6's explicit gradient-step estimate at a point `x`;
* core/canonical: `taylor_upper_bound_of_contDiffOne_withLipschitzGradient`;
* bridge/view: the evaluation formula `firstOrderTaylorModelAt_apply`.

Primitive data:
* the base point `x`;
* the trial stepsize `h`.

Derived API:
* the value-decrease bound at the antigradient trial point `x - h • ∇ f x`.

The owner quadratic model is
`taylor_upper_bound_of_contDiffOne_withLipschitzGradient` from Lemma 1.5.10.
Lemma 1.6.6 is its antigradient-step specialization, so we keep only that textbook statement as
public API and let downstream uses specialize it directly. The theorem itself is stated on the
same canonical real inner-product-space owner layer as Lemma 1.5.10; specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formulation. -/

-- Proof sketch: apply
-- `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` with
-- `y = x - h • ∇ f x`, then simplify the linear term and the squared norm of the step vector.
/-- Lemma 1.6.6: specializing the owner quadratic upper bound at the trial point
`x - h • ∇ f x` gives the standard gradient-step estimate
`f (x - h ∇ f x) ≤ f x - h (1 - L h / 2) ‖∇ f(x)‖²`. -/
theorem gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
    (x : E) (h : ℝ) :
    f (x - h • ∇ f x) ≤
      f x - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  -- Rewrite the affine Taylor model at the antigradient trial point into the textbook linear term.
  have hmodel :
      firstOrderTaylorModelAt f x (x - h • ∇ f x) =
        f x - h * ‖∇ f x‖ ^ (2 : ℕ) := by
    simp [sub_eq_add_neg, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two]
  -- Rewrite the squared displacement so the quadratic remainder is measured by `‖∇ f x‖²`.
  have hsq :
      ‖(x - h • ∇ f x) - x‖ ^ (2 : ℕ) = h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    simp [sub_eq_add_neg, norm_smul, mul_pow, sq_abs]
  -- Specialize the quadratic upper model from Lemma 1.5.10 and simplify the resulting scalar factor.
  calc
    f (x - h • ∇ f x) ≤
        firstOrderTaylorModelAt f x (x - h • ∇ f x) +
          ((L : ℝ) / 2) * ‖(x - h • ∇ f x) - x‖ ^ (2 : ℕ) :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf hgrad x (x - h • ∇ f x)
    _ = f x - h * ‖∇ f x‖ ^ (2 : ℕ) +
          ((L : ℝ) / 2) * (h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ)) := by
      rw [hmodel, hsq]
    _ = f x - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      ring

omit hf hgrad

end

/-! ### Proposition_1_6_7 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain:
* sufficient-decrease estimates for real-Hilbert-space gradient-method trajectories

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` in `Lemma_1_6_6.lean`
* `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`, the generic line-search owner
  used directly at theorem level once `ContDiff ℝ 1 f` already supplies the gradient witness
* `SatisfiesArmijoRule` in `Definition_1_6_4.lean`, whose lower Armijo bound and parameter
  inequalities are the primitive components consumed here after removing its redundant
  `HasGradientAt` field at theorem level

Source/core/bridge triage:
* source-facing: Proposition 1.6.7's explicit sufficient-decrease inequalities for the
  constant step `h`, its specialization `h = 2 α / L`, exact line search, and Armijo
  backtracking
* core/canonical owner: the trajectory `gradientMethod stepSize f x0` together with the
  one-step estimate
  `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`
* bridge/view: the `∃ ω > 0` corollaries in the exact descent-hypothesis shape used by
  `Theorem_1_6_8`

Primitive data:
* the objective `f`, the initial point `x0`, and the step-size data of the chosen rule
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`
* the rule parameters `α`, `β` only when the step rule requires them
* the backtracking exponents `m_k` in the Armijo case

Derived API:
* the explicit `h = 2 α / L` normalization of the constant-step bound
* the exact-line-search and Armijo-backtracking decrease bounds
* the companion `∃ ω > 0` corollaries with the exact downstream orientation

The arbitrary-point constant-step estimate is already owned upstream by
`gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`. This file keeps only the
source-facing iterate form that Proposition 1.6.7 states, together with the `∃ ω > 0` bridge
corollaries used later in the chapter. The `h = 2 α / L` formula is kept as a direct
specialization of the owner constant-step estimate, not as an equality-based wrapper around an
arbitrary schedule. The exact-line-search proposition uses the generic owner
`SatisfiesExactLineSearchAlong` directly, since `ContDiff ℝ 1 f` already implies the gradient
existence field bundled in `SatisfiesExactLineSearch`. Likewise, the Armijo propositions consume
only the primitive lower-bound and parameter data extracted from `SatisfiesArmijoRule`; the only
extra source-facing data kept here is the minimality of the accepted exponent `m_k`, expressed by
rejection of every smaller trial. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `ℝⁿ` formulation. -/

section GradientMethod

variable {L : NNReal} {f : E → ℝ} {x0 : E}

/- The companion corollaries below are stated directly in the sufficient-decrease shape consumed
by `Theorem_1_6_8`, rather than through a parallel local wrapper predicate. -/

section ConstantStepSize

variable (h : ℝ)

local notation "traj" => gradientMethod (fun _ ↦ h) f x0

-- Proof sketch: apply the owner one-step estimate
-- `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` at `x = traj k`, rewrite
-- `traj (k + 1)` using `gradientMethod_succ`, and use that `traj` is already the constant-step
-- trajectory.
/-- Proposition 1.6.7 (1): if a gradient method for a `C_L^{1,1}(ℝⁿ)` objective uses the constant
step size `h`, then
`f(x_k) - f(x_(k+1)) ≥ h (1 - L h / 2) ‖∇ f(x_k)‖²` for every `k`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Rewrite the textbook iterate update into the pointwise owner descent lemma.
  have hstep :
      f (traj (k + 1)) ≤
        f (traj k) - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    simpa [gradientMethod_succ] using
      gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient hf hgrad (traj k) h
  -- Rearranging the one-step estimate gives the displayed sufficient decrease bound.
  linarith

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` and choose
-- `ω = (L : ℝ) * h * (1 - ((L : ℝ) * h) / 2)`. The step-size range `0 < h < 2 / L` makes this
-- choice positive.
/-- Companion corollary: any constant-step gradient method with `0 < h < 2 / L` satisfies the
chapter's `∃ ω > 0` sufficient-decrease form. -/
theorem gradientMethod_exists_sufficientDecrease_of_constant_stepsize
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hh0 : 0 < h)
    (hh1 : h < 2 / (L : ℝ)) :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- The admissible step-size range forces `L > 0`, so the standard coefficient is positive.
  refine ⟨(L : ℝ) * h * (1 - ((L : ℝ) * h) / 2), ?_, ?_⟩
  · have hLne : (L : ℝ) ≠ 0 := by
      intro hL
      simp [hL] at hh1
      linarith
    have hLpos : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hLne)
    have hhL : h * (L : ℝ) < 2 := by
      exact (lt_div_iff₀ hLpos).mp hh1
    have hcoeff : 0 < 1 - ((L : ℝ) * h) / 2 := by
      nlinarith
    exact mul_pos (mul_pos hLpos hh0) hcoeff
  · intro k
    -- Match the bridge coefficient `(ω / L)` with the owner constant-step estimate.
    have hLne : (L : ℝ) ≠ 0 := by
      intro hL
      simp [hL] at hh1
      linarith
    have hω :
        (((L : ℝ) * h * (1 - ((L : ℝ) * h) / 2)) / (L : ℝ)) =
          h * (1 - ((L : ℝ) * h) / 2) := by
      field_simp [hLne]
    simpa [hω] using
      gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
        (h := h) hf hgrad k

end ConstantStepSize

section ConstantStepSizeSpecialization

variable {α : ℝ}

local notation "traj" => gradientMethod (fun _ ↦ (2 * α) / (L : ℝ)) f x0

-- Proof sketch: specialize
-- `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` at `h = (2 * α) / L` and simplify
-- the coefficient.
/-- Proposition 1.6.7 (1), specialized: if the constant step size is `h = 2 α / L`, then
`f(x_k) - f(x_(k+1)) ≥ ((2 / L) * α * (1 - α)) ‖∇ f(x_k)‖²` for every `k`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize_eq_two_mul_div
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (((2 : ℝ) / (L : ℝ)) * α * (1 - α)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Specialize the constant-step estimate to `h = 2 α / L`.
  have hconst :=
    gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
      (x0 := x0) (h := (2 * α) / (L : ℝ)) hf hgrad k
  -- Normalize the coefficient exactly into the source-facing textbook form.
  by_cases hL : (L : ℝ) = 0
  · simp [hL] at hconst ⊢
  · have hcoeff :
        ((2 * α) / (L : ℝ)) * (1 - ((L : ℝ) * ((2 * α) / (L : ℝ))) / 2) =
          (((2 : ℝ) / (L : ℝ)) * α * (1 - α)) := by
      field_simp [hL]
    simpa [hcoeff] using hconst

end ConstantStepSizeSpecialization

section ExactLineSearch

variable {stepSize : ℕ → ℝ}

local notation "traj" => gradientMethod stepSize f x0
local notation "grad" => (∇ f) ∘ traj

-- Proof sketch: use that `stepSize k` minimizes the line-search objective over `h ≥ 0`, compare
-- the accepted value with the trial step `h = 1 / L`, and then specialize
-- `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` at the point `traj k`.
/-- Proposition 1.6.7 (2): if the step sizes satisfy the exact line-search minimization condition
along `-∇ f(x_k)`, then each gradient-method step decreases the objective by at least
`(2L)⁻¹ ‖∇ f(x_k)‖²`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hexact : SatisfiesExactLineSearchAlong f traj grad stepSize)
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (1 / (2 * (L : ℝ))) * ‖grad k‖ ^ (2 : ℕ) := by
  -- Compare the accepted step with the trial step `1 / L` using the exact line-search owner.
  have hLnonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast L.2
  have htrial_mem : (1 / (L : ℝ)) ∈ Set.Ici (0 : ℝ) := by
    rw [Set.mem_Ici]
    exact one_div_nonneg.mpr hLnonneg
  have hmin := hexact.isMinOn k
  rw [isMinOn_iff] at hmin
  have hcmp :
      f (traj (k + 1)) ≤ f (traj k - (1 / (L : ℝ)) • grad k) := by
    simpa [gradientMethod_succ] using hmin (1 / (L : ℝ)) htrial_mem
  by_cases hL : (L : ℝ) = 0
  · -- When `L = 0`, the target coefficient is zero, so monotonicity from the trial step `0` is enough.
    have hzero_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp
    have hcmp0 : f (traj (k + 1)) ≤ f (traj k) := by
      simpa [gradientMethod_succ] using hmin 0 hzero_mem
    have hdrop_nonneg : 0 ≤ f (traj k) - f (traj (k + 1)) := by
      linarith
    simpa [hL] using hdrop_nonneg
  · -- For `L ≠ 0`, import the descent-lemma estimate at the trial step `1 / L`.
    have hcoeff :
        (1 / (2 * (L : ℝ))) * ‖grad k‖ ^ (2 : ℕ) =
          (1 / (L : ℝ)) * (‖grad k‖ ^ (2 : ℕ) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) := by
      field_simp [hL]
      ring
    have hstep :
        f (traj k - (1 / (L : ℝ)) • grad k) ≤
          f (traj k) - (1 / (L : ℝ)) *
            (‖grad k‖ ^ (2 : ℕ) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hf hgrad (traj k) (1 / (L : ℝ))
    linarith

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch` and choose
-- `ω = 1 / 2`.
/-- Companion corollary to Proposition 1.6.7 (2): exact line search also yields the source-style
`∃ ω > 0` sufficient-decrease formulation. -/
theorem gradientMethod_exists_sufficientDecrease_of_exactLineSearch
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hexact : SatisfiesExactLineSearchAlong f traj grad stepSize)
    :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖grad k‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- The exact-line-search coefficient is obtained by the fixed choice `ω = 1 / 2`.
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro k
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch
      (hf := hf) (hgrad := hgrad) hexact k

end ExactLineSearch

section ArmijoBacktracking

variable {α β : ℝ} (armijoIndex : ℕ → ℕ)

local notation "stepSize" => fun k ↦ β ^ armijoIndex k
local notation "traj" => gradientMethod stepSize f x0
local notation "grad" => (∇ f) ∘ traj

/-
Primitive source-facing data beyond the owner `SatisfiesArmijoRule`:
* the theorem-local rejection of every smaller geometric trial exponent

Derived from the owner:
* genuine gradient existence along `traj`
* positivity and ordering of the Armijo parameters
* the accepted lower Armijo inequality at the chosen exponent

At theorem level, `ContDiff ℝ 1 f` already supplies the gradient witness along `traj`, so the
propositions below use the canonical owner `SatisfiesArmijoRule` for the accepted-step data. The
source-facing minimality condition from Proposition 1.6.7 (3) remains theorem-local, rather than
being exported as a second public raw-gradient owner.
-/

/-- Helper for Proposition 1.6.7: if the gradient at iterate `k` is nonzero, then the accepted
Armijo step is bounded below by `((2 / L) * (1 - β))`. -/
lemma armijo_stepsize_lower_bound_of_nonzero_gradient
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (k : ℕ)
    (hgradk : grad k ≠ 0) :
    (((2 : ℝ) / (L : ℝ)) * (1 - β)) ≤ stepSize k := by
  by_cases hL : (L : ℝ) = 0
  · -- In the degenerate `L = 0` branch the lower bound is simply `0 ≤ stepSize k`.
    simp [hL, le_of_lt (hArmijo.stepSize_pos k)]
  · -- Route correction: use the owner upper Armijo bound plus Lemma 1.6.6 at the accepted step.
    have hstep :
        f (traj (k + 1)) ≤
          f (traj k) - (stepSize k * (1 - ((L : ℝ) * stepSize k) / 2)) * ‖grad k‖ ^ (2 : ℕ) := by
      simpa [gradientMethod_succ] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hf hgrad (traj k) (stepSize k)
    have hdrop :
        (stepSize k * (1 - ((L : ℝ) * stepSize k) / 2)) * ‖grad k‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)) := by
      linarith
    have hupp :
        f (traj k) - f (traj (k + 1)) ≤ β * (stepSize k * ‖grad k‖ ^ (2 : ℕ)) := by
      simpa [gradientMethod_succ, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two,
        mul_assoc, mul_left_comm, mul_comm] using hArmijo.upperBound k
    have hnormsq_pos : 0 < ‖grad k‖ ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hgradk)
    have hcoeff : stepSize k * (1 - ((L : ℝ) * stepSize k) / 2) ≤ β * stepSize k := by
      nlinarith
    have hLpos : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL)
    have hmul : (2 : ℝ) * (1 - β) ≤ (L : ℝ) * stepSize k := by
      have hstep_pos : 0 < stepSize k := hArmijo.stepSize_pos k
      nlinarith
    have hdiv : ((2 : ℝ) * (1 - β)) / (L : ℝ) ≤ stepSize k := by
      exact (div_le_iff₀ hLpos).mpr (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

-- Proof sketch: the descent lemma shows that every trial step
-- `h ≤ 2 * (1 - α) / L` satisfies the Armijo acceptance inequality. If the accepted exponent
-- `armijoIndex k` were too large, the previous geometric trial would still be acceptable,
-- contradicting the theorem-local rejection hypothesis `hminimal`. Hence
-- `β * (2 * (1 - α) / L) ≤ stepSize k`. Combine this lower bound with the accepted Armijo
-- inequality, then use `β * (1 - α) ≥ 1 - β`, which follows from `α < β`.
/-- Proposition 1.6.7 (3): fix `0 < α < β < 1`. Suppose
`h_k = β^(armijoIndex k)` and `armijoIndex k` is the smallest nonnegative exponent whose trial
point satisfies the Armijo acceptance inequality along `-∇ f(x_k)`. Equivalently, the trajectory
is `gradientMethod (fun k ↦ β ^ armijoIndex k) f x0`, the accepted-step data is the owner
`SatisfiesArmijoRule f (fun k ↦ β ^ armijoIndex k) x0 α β`, and `hminimal` records rejection of
smaller exponents.
Then every gradient-method step decreases the objective by at least
`((2 / L) * α * (1 - β)) ‖∇ f(x_k)‖²`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (hminimal :
      ∀ ⦃k j : ℕ⦄, j < armijoIndex k →
        f (traj k - β ^ j • grad k) >
          f (traj k) - α * β ^ j * ‖grad k‖ ^ (2 : ℕ))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) * ‖grad k‖ ^ (2 : ℕ) := by
  -- The owner-based proof route does not need the explicit rejection hypothesis, but we keep it
  -- present because it is part of the textbook Armijo statement recorded in this theorem.
  let _ := hminimal
  by_cases hgradk : grad k = 0
  · -- If the gradient vanishes, the next iterate is unchanged and the desired lower bound is `0`.
    have hgradk' : ∇ f (traj k) = 0 := hgradk
    simp [gradientMethod_succ, hgradk']
  · -- The lower Armijo inequality becomes quantitative once the step-size lower bound is inserted.
    have hstep_lower :=
      armijo_stepsize_lower_bound_of_nonzero_gradient
        (armijoIndex := armijoIndex) (hf := hf) (hgrad := hgrad) hArmijo k hgradk
    have hlow :
        (α * stepSize k) * ‖grad k‖ ^ (2 : ℕ) ≤ f (traj k) - f (traj (k + 1)) := by
      simpa [gradientMethod_succ, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two,
        mul_assoc, mul_left_comm, mul_comm] using hArmijo.lowerBound k
    have hαnonneg : 0 ≤ α := le_of_lt hArmijo.alpha_pos
    have hnormsq_nonneg : 0 ≤ ‖grad k‖ ^ (2 : ℕ) := by
      positivity
    have htarget :
        (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) * ‖grad k‖ ^ (2 : ℕ) ≤
          (α * stepSize k) * ‖grad k‖ ^ (2 : ℕ) := by
      have hcoeff : α * (((2 : ℝ) / (L : ℝ)) * (1 - β)) ≤ α * stepSize k := by
        exact mul_le_mul_of_nonneg_left hstep_lower hαnonneg
      have hmul := mul_le_mul_of_nonneg_right hcoeff hnormsq_nonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans htarget hlow

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking` and choose
-- `ω = 2 * α * (1 - β)`.
/-- Companion corollary to Proposition 1.6.7 (3): the Armijo backtracking rule also yields the
source-style `∃ ω > 0` sufficient-decrease formulation. -/
theorem gradientMethod_exists_sufficientDecrease_of_armijo_backtracking
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (hminimal :
      ∀ ⦃k j : ℕ⦄, j < armijoIndex k →
        f (traj k - β ^ j • grad k) >
          f (traj k) - α * β ^ j * ‖grad k‖ ^ (2 : ℕ))
    :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖grad k‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- Choose the textbook Armijo coefficient `ω = 2 α (1 - β)`.
  refine ⟨2 * α * (1 - β), ?_, ?_⟩
  · have hαpos : 0 < α := hArmijo.alpha_pos
    have hβlt : β < 1 := hArmijo.beta_lt_one
    nlinarith
  · intro k
    have hcoeff :
        ((2 * α * (1 - β)) / (L : ℝ)) =
          (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) := by
      by_cases hL : (L : ℝ) = 0
      · simp [hL]
      · field_simp [hL]
    simpa [hcoeff] using
      gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking
        (armijoIndex := armijoIndex) (hf := hf) (hgrad := hgrad) hArmijo hminimal k

end ArmijoBacktracking

end GradientMethod

end

/-! ### Theorem_1_6_8 (from Chap01) -/
open scoped BigOperators Gradient MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}

variable {L ω fStar : ℝ}

/- Primary domain:
* sufficient-decrease consequences for real-Hilbert-space gradient-method trajectories

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `IsGStar` in `Definition_1_6_5.lean`, whose lower-boundedness component is the canonical owner
  `BddBelow (Set.range f)`
* the sufficient-decrease bridge theorems in `Proposition_1_6_7.lean`
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23.lean`

Source/core/bridge triage:
* source-facing: Theorem 1.6.8's telescoping inequality, vanishing-gradient conclusion, and
  `g_N^*` estimate under the chapter's sufficient-decrease hypothesis
* core/canonical owner: the recursive trajectory `gradientMethod stepSize f x0` and the
  finite-window minimum `minGradientNormAlongIterates`
* bridge/view: Proposition 1.6.7's constant-step, exact-line-search, and Armijo corollaries that
  produce the sufficient-decrease hypothesis used here; the source prose names the owner finite
  minimum `minGradientNormAlongIterates f (gradientMethod stepSize f x0) 0 N (Nat.zero_le N)` by
  the textbook symbol `g_N^*`

Primitive data:
* the objective `f`, step schedule `stepSize`, and initial point `x0`
* the real sufficient-decrease scale `L`
* the sufficient-decrease hypothesis `hdesc`
* the exact optimal value parameter `fStar` together with the canonical owner hypothesis
  `IsGLB (Set.range f) fStar` for the source-facing quantitative bounds
* an arbitrary lower-bound witness `fLower ∈ lowerBounds (Set.range f)` for the companion
  lower-bound-only estimates
* the lower-boundedness owner `BddBelow (Set.range f)` when only existence of a bound is needed

Derived API:
* the telescoping estimate
* convergence of the gradients to `0`
* the source-facing `g_N^*` square-root bound for the owner window minimum
  `g[f; gradientMethod stepSize f x0; 0, N | Nat.zero_le N]`
* lower-bound-only companion estimates obtained by replacing the exact `fStar` owner hypothesis by
  an arbitrary witness `fLower ∈ lowerBounds (Set.range f)`

This file stays at the sufficient-decrease layer. The smoothness and step-rule assumptions that
produce `hdesc` are already owned upstream by `Proposition_1_6_7`; after choosing such a bridge,
this file only uses the resulting real coefficient `L` appearing in `(ω / L)`. The ambient space
is refined to the same real-Hilbert-space owner level as `gradientMethod` and
`minGradientNormAlongIterates`, since no theorem here uses coordinates or finite-dimensional
Euclidean structure. The textbook scalar `f^*` is exposed through the exact-infimum owner
`IsGLB (Set.range f) fStar`; the weaker arbitrary-lower-bound form is kept only as companion API
through `lowerBounds (Set.range f)`. -/

section SufficientDecrease

variable (stepSize : ℕ → ℝ) (x0 : E)

local notation "traj" => gradientMethod stepSize f x0
variable
  (hdesc :
    ∀ k : ℕ,
      (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)))

-- Proof sketch: sum the assumed descent inequalities over `k = 0, …, N` and telescope the left
-- side to obtain the first inequality; the second follows from the lower-bound hypothesis
-- applied to the iterate `traj (N + 1)`.
/-- Companion form of Theorem 1.6.8: any chosen lower bound
`fLower ∈ lowerBounds (Set.range f)` yields the same telescoping estimate with `fLower` in place
of the exact optimal value `f^*`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
    {fLower : ℝ}
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfLower : fLower ∈ lowerBounds (Set.range f))
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fLower := by
  constructor
  · -- Summing the sufficient-decrease bounds produces the telescoping estimate.
    have hsum :
        ∑ k ∈ Finset.range (N + 1), (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) := by
      exact Finset.sum_le_sum fun k hk ↦ hdesc k
    have htel :
        ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) =
          f (traj 0) - f (traj (N + 1)) := by
      simpa using (Finset.sum_range_sub' (fun k ↦ f (traj k)) (N + 1))
    calc
      (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) =
          ∑ k ∈ Finset.range (N + 1), (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) := hsum
      _ = f (traj 0) - f (traj (N + 1)) := htel
      _ = f x0 - f (traj (N + 1)) := by simp
  · -- The terminal iterate still lies above any lower bound of `f`.
    have hterminal : fLower ≤ f (traj (N + 1)) := hfLower ⟨traj (N + 1), rfl⟩
    simpa using sub_le_sub_left hterminal (f x0)

/-- Helper for Theorem 1.6.8: the exact-infimum telescoping estimate follows by applying the
lower-bound companion theorem to the canonical lower-bound witness supplied by
`hfStar : IsGLB (Set.range f) fStar`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le_of_isGLB
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfStar : IsGLB (Set.range f) fStar)
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fStar := by
  -- Specialize the lower-bound telescope to the exact infimum witness `hfStar.1`.
  simpa using
    squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
      hfStar.1 N

/-- Theorem 1.6.8: for the gradient-method trajectory `gradientMethod stepSize f x0`, any
uniform descent bound of the form `(ω / L) ‖∇ f(xₖ)‖² ≤ f(xₖ) - f(xₖ₊₁)` yields the telescoping
estimate `(ω / L) ∑_{k=0}^N ‖∇ f(xₖ)‖² ≤ f(x₀) - f(x_{N+1}) ≤ f(x₀) - f^*`, where `fStar` is
the exact infimum value of `f`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le
    (hfStar : IsGLB (Set.range f) fStar)
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fStar := by
  -- Route correction: the exact adapter is now proved in
  -- `squared_gradient_norm_sum_le_and_value_gap_le_of_isGLB`, but this generated target header
  -- still omits the sufficient-decrease hypothesis, so no proof term can reference it here.
  -- TODO: repair the statement pipeline so this theorem carries `hdesc` and can close by
  -- `simpa using squared_gradient_norm_sum_le_and_value_gap_le_of_isGLB ... hdesc hfStar N`.
  sorry

end SufficientDecrease

section PositiveSufficientDecrease

variable (stepSize : ℕ → ℝ) (x0 : E)

local notation "traj" => gradientMethod stepSize f x0
variable (hL : 0 < L) (hω : 0 < ω)
variable
  (hdesc :
    ∀ k : ℕ,
      (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)))

local notation "g⋆[" N "]" => minGradientNormAlongIterates f traj 0 N (Nat.zero_le N)

-- Proof sketch: use `BddBelow (Set.range f)` to choose some lower bound value, apply the previous
-- theorem to obtain a uniform bound on the partial sums of `∑ ‖∇ f(xₖ)‖²`, and conclude that
-- this nonnegative series is summable. Hence `‖∇ f(xₖ)‖ → 0`, so the gradient vectors themselves
-- converge to `0`.
/-- Under the positive sufficient-decrease hypothesis of Theorem 1.6.8 and the canonical
lower-boundedness assumption `BddBelow (Set.range f)`, the gradients along
`gradientMethod stepSize f x0` converge to zero. -/
theorem tendsto_gradient_zero
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hbelow : BddBelow (Set.range f)) :
    Filter.Tendsto (fun k : ℕ ↦ ∇ f (traj k)) Filter.atTop (nhds 0) := by
  rcases hbelow with ⟨fLower, hfLower⟩
  let a : ℕ → ℝ := fun k ↦ (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ)
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    positivity
  have hsum_range_le : ∀ n : ℕ, ∑ i ∈ Finset.range n, a i ≤ f x0 - fLower := by
    intro n
    cases n with
    | zero =>
        simpa [a] using sub_nonneg.mpr (hfLower ⟨x0, by simp⟩)
    | succ N =>
        -- The telescoping theorem gives a uniform bound on every partial sum.
        have hpartial :
            (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
              f x0 - fLower :=
          (squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
            (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
            hfLower N).1.trans
            (squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
              (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
              hfLower N).2
        simpa [a, Finset.mul_sum] using hpartial
  have hsummable_a : Summable a := summable_of_sum_range_le ha_nonneg hsum_range_le
  have hsummable_sq : Summable (fun k : ℕ ↦ ‖∇ f (traj k)‖ ^ (2 : ℕ)) := by
    -- Remove the positive constant factor from the summable sequence.
    exact
      (summable_mul_left_iff (show ω / L ≠ 0 by exact div_ne_zero (ne_of_gt hω) (ne_of_gt hL))).1
        hsummable_a
  have hsq_zero :
      Filter.Tendsto (fun k : ℕ ↦ ‖∇ f (traj k)‖ ^ (2 : ℕ)) Filter.atTop (nhds 0) :=
    hsummable_sq.tendsto_atTop_zero
  have hnorm_zero :
      Filter.Tendsto (fun k : ℕ ↦ ‖∇ f (traj k)‖) Filter.atTop (nhds 0) := by
    -- Taking square roots converts convergence of squared norms into convergence of norms.
    have hsqrt_zero :
        Filter.Tendsto (fun k : ℕ ↦ Real.sqrt (‖∇ f (traj k)‖ ^ (2 : ℕ)))
          Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq_zero
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt_zero
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_zero

/-- Helper for Theorem 1.6.8: the finite-window minimum of gradient norms is nonnegative because
it is attained by some iterate in the window. -/
lemma minGradientNormAlongIterates_nonneg
    (N : ℕ) :
    0 ≤ g⋆[N] := by
  -- The owner minimum equals a norm at some iterate, so nonnegativity is immediate.
  rcases minGradientNormAlongIterates.exists_eq f traj (Nat.zero_le N) with
    ⟨i, -, -, hEq⟩
  rw [hEq]
  exact norm_nonneg _

/-- Helper for Theorem 1.6.8: the square of the window minimum `g⋆[N]` is bounded by the average
of the squared gradient norms over the same window. -/
lemma minGradientNormAlongIterates_sq_mul_le_sum_sq
    (N : ℕ) :
    ((N + 1 : ℝ) * g⋆[N] ^ (2 : ℕ)) ≤
      ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  have hmin_nonneg : 0 ≤ g⋆[N] :=
    minGradientNormAlongIterates_nonneg (stepSize := stepSize) (x0 := x0) (f := f) N
  have hpointwise :
      ∀ k ∈ Finset.range (N + 1), g⋆[N] ^ (2 : ℕ) ≤ ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hle :
        g⋆[N] ≤ ‖∇ f (traj k)‖ :=
      minGradientNormAlongIterates.le f traj (Nat.zero_le N) (Nat.zero_le k) hkN
    exact (sq_le_sq₀ hmin_nonneg (norm_nonneg _)).2 hle
  -- Sum the pointwise squared bounds over the whole window.
  have hsum :
      ∑ k ∈ Finset.range (N + 1), g⋆[N] ^ (2 : ℕ) ≤
        ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum hpointwise
  simpa using hsum

-- Proof sketch: the minimum of `N + 1` nonnegative numbers has square at most the average of
-- their squares, and the latter is bounded by Theorem 1.6.8 after rearranging the coefficient
-- `(ω / L)`.
/-- Companion form of the Chapter 1 estimate for the owner window minimum
`g⋆[N]`, representing the textbook quantity `g_N^*`: any chosen lower bound
`fLower ∈ lowerBounds (Set.range f)` gives the same square-root bound with `fLower` in place of
the exact optimum value `f^*`. -/
theorem minGradientNormAlongIterates_le_sqrt_of_lower_bound
    {fLower : ℝ}
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfLower : fLower ∈ lowerBounds (Set.range f))
    (N : ℕ) :
    g⋆[N] ≤
      Real.sqrt ((L * (f x0 - fLower)) / (ω * (N + 1 : ℝ))) := by
  have hgap_nonneg : 0 ≤ f x0 - fLower := by
    exact sub_nonneg.mpr (hfLower ⟨x0, by simp⟩)
  have hpair :=
    squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
      hfLower N
  have hsum_sq_le :
      ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        (L / ω) * (f x0 - fLower) := by
    have hscaled : (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f x0 - fLower :=
      hpair.1.trans hpair.2
    have hdiv :
        ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          (f x0 - fLower) / (ω / L) := by
      exact (le_div_iff₀ (div_pos hω hL)).2 (by simpa [mul_comm] using hscaled)
    have hrewrite : (f x0 - fLower) / (ω / L) = (L / ω) * (f x0 - fLower) := by
      field_simp [ne_of_gt hL, ne_of_gt hω]
    rwa [hrewrite] at hdiv
  have hsq :
      g⋆[N] ^ (2 : ℕ) ≤ ((L * (f x0 - fLower)) / ω) / (N + 1 : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < (N + 1 : ℝ))).2
    calc
      g⋆[N] ^ (2 : ℕ) * (N + 1 : ℝ) = (N + 1 : ℝ) * g⋆[N] ^ (2 : ℕ) := by ring
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) :=
        minGradientNormAlongIterates_sq_mul_le_sum_sq
          (stepSize := stepSize) (x0 := x0) (f := f) N
      _ ≤ (L / ω) * (f x0 - fLower) := hsum_sq_le
      _ = (L * (f x0 - fLower)) / ω := by
        field_simp [ne_of_gt hω]
  have hsq' :
      g⋆[N] ^ (2 : ℕ) ≤ (L * (f x0 - fLower)) / (ω * (N + 1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hmin_nonneg : 0 ≤ g⋆[N] :=
    minGradientNormAlongIterates_nonneg (stepSize := stepSize) (x0 := x0) (f := f) N
  have hrhs_nonneg : 0 ≤ (L * (f x0 - fLower)) / (ω * (N + 1 : ℝ)) := by
    positivity
  -- Apply the square-root monotonicity step to the squared estimate.
  exact (Real.le_sqrt hmin_nonneg hrhs_nonneg).2 hsq'

/- The owner window minimum `g⋆[N]`, representing the textbook quantity `g_N^*`, is bounded by
the standard `O((N + 1)^{-1/2})` rate obtained from the telescoping descent estimate, with the
exact optimum value exposed by
`IsGLB (Set.range f) fStar`. -/
theorem minGradientNormAlongIterates_le_sqrt
    (hfStar : IsGLB (Set.range f) fStar)
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (N : ℕ) :
    g⋆[N] ≤
      Real.sqrt ((L * (f x0 - fStar)) / (ω * (N + 1 : ℝ))) := by
  -- The exact-infimum rate bound is the lower-bound companion theorem with the GLB witness.
  simpa using
    minGradientNormAlongIterates_le_sqrt_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hL hω hdesc hfStar.1 N

end PositiveSufficientDecrease

end

/-! ### Definition_1_6_9 (from Chap01) -/
open Asymptotics Filter

/-
Primary domain: scalar asymptotic convergence rates for real optimization error sequences.

Source/core/bridge triage for Definition 1.6.9:
* source-facing: `HasConvergenceRateOfOrder r φ`
* core/canonical: the eventual comparison bound
  `∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N`, packaged with
  `IsOptimizationErrorSequence r`
* bridge/view: the asymptotic consequence `HasConvergenceRateOfOrder.isBigO`, and direct
  downstream use of the square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`

Relevant declarations sampled before refining:
* `Asymptotics.isBigO_iff'`
* `Asymptotics.IsBigO.of_bound`
* `HasGeometricRateOfConvergence.isBigO` in `Definition_1_2_6.lean`
* `HasEventuallySuperlinearErrorBound r 0 c 0` in `Definition_1_2_7.lean`, a neighboring
  chapter example where a specialized owner is reused directly instead of wrapped by a duplicate
  local predicate

Owner abstraction:
* the source-facing eventual comparison bound from Definition 1.6.9, packaged with the
  optimization-error-sequence hypothesis; bare `r =O[atTop] φ` is only a companion bridge
  because it inserts absolute values

Primitive data:
* the sequence `r`
* the comparison rate `φ`
* the nonnegativity and convergence-to-zero hypothesis `IsOptimizationErrorSequence r`
* a witness `C > 0` and the eventual bound `r N ≤ C * φ N` along `atTop`

Derived API:
* the projection lemmas `error` and `bound`
* the asymptotic bridge `isBigO`
-/

/-- An optimization error sequence is a nonnegative real sequence converging to `0`. -/
def IsOptimizationErrorSequence (r : ℕ → ℝ) : Prop :=
  (∀ N, 0 ≤ r N) ∧ Tendsto r atTop (nhds 0)

namespace IsOptimizationErrorSequence

variable {r : ℕ → ℝ}

theorem nonneg (h : IsOptimizationErrorSequence r) (N : ℕ) : 0 ≤ r N :=
  h.1 N

theorem tendsto_zero (h : IsOptimizationErrorSequence r) : Tendsto r atTop (nhds 0) :=
  h.2

end IsOptimizationErrorSequence

/-- Definition 1.6.9: a minimization process has convergence rate of order `φ` when its
optimization error sequence is nonnegative, converges to `0`, and is eventually bounded above
by a positive multiple of `φ`. -/
def HasConvergenceRateOfOrder (r φ : ℕ → ℝ) : Prop :=
  IsOptimizationErrorSequence r ∧ ∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N

namespace HasConvergenceRateOfOrder

variable {r φ : ℕ → ℝ}

theorem error (h : HasConvergenceRateOfOrder r φ) : IsOptimizationErrorSequence r :=
  h.1

theorem bound (h : HasConvergenceRateOfOrder r φ) :
    ∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N :=
  h.2

/-- A convergence rate of order `φ` yields the canonical asymptotic estimate `r =O[atTop] φ`. -/
-- Proof sketch: the source-facing eventual bound already forces `φ` to be eventually nonnegative,
-- because `r` is nonnegative and the comparison constant is positive. Convert the resulting
-- norm bound directly with `IsBigO.of_bound`.
theorem isBigO
    (h : HasConvergenceRateOfOrder r φ) :
    r =O[atTop] φ := by
  obtain ⟨C, hC, hbound⟩ := h.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hbound] with N hN
  have hrN : 0 ≤ r N := h.error.nonneg N
  have hφN : 0 ≤ φ N := nonneg_of_mul_nonneg_right (hrN.trans hN) hC
  simpa [Real.norm_eq_abs, abs_of_nonneg hrN, abs_of_nonneg hφN] using hN

end HasConvergenceRateOfOrder
