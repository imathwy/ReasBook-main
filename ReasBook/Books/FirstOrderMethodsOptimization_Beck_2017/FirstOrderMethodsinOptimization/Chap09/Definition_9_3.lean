import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 9.3 is `source-facing`: the textbook specifies a recursive first-order procedure
through explicit iterates `x^k`, chosen positive stepsizes `t_k`, chosen Euclidean subgradients
`f'(x^k)`, and an argmin update over the feasible set `C`. The owner abstractions already present
in the project for these ingredients are the Euclidean subgradient bridge
`euclideanSubdifferentialAt`, the source-facing subdifferential domain `subdifferential_domain`
for the mirror map `ω.toEReal`, Chapter 9's Bregman-distance owner `B[ω]`, and mathlib's
minimizer predicate `IsMinOn` for the argmin step. Since no canonical minimizer has been chosen,
the public object here is a trajectory predicate on the iterate, stepsize, and
selected-subgradient sequences, together with the explicit one-step mirror-descent objective. -/

/-- The one-step mirror-descent objective obtained by linearizing `f` with the chosen
subgradient `g` at the current iterate `x` and keeping the mirror map `ω` explicit. -/
def mirror_descent_update_objective (ω : E → ℝ) (x g : E) (t : ℝ) : E → ℝ :=
  fun y ↦ inner ℝ (t • g) y + B[ω] y x + ω x - inner ℝ (∇ ω x) x

-- Proof sketch: unfold `mirror_descent_update_objective`; the displayed formula is exactly its
-- defining lambda expression.
/-- Evaluating `mirror_descent_update_objective ω x g t` at `y` gives the linearized term
`⟪t • g - ∇ ω x, y⟫` plus the mirror map value `ω y`. -/
@[simp] theorem mirror_descent_update_objective_apply
    (ω : E → ℝ) (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω x g t y =
      inner ℝ (t • g - ∇ ω x) y + ω y := by
  rw [mirror_descent_update_objective, bregmanDistance]
  have hω : (fun z : E ↦ (Function.toEReal ω z).toReal) = ω := by
    funext z
    simp
  rw [hω]
  simp only [Function.comp_apply, EReal.toReal_coe]
  rw [inner_sub_right, inner_sub_left]
  ring

/-- Definition 9.3: sequences of iterates `x`, stepsizes `t`, and chosen Euclidean subgradients
`g` follow the Mirror Descent Method for objective `f`, mirror map `ω`, and feasible set `C` when
for every iteration `k`, the current iterate lies in `C ∩ dom(∂ ω)`, the chosen vector `g k`
belongs to `∂ f(x^k)`, the stepsize `t k` is positive, and the next iterate `x^(k+1)` minimizes
the mirror-descent update objective
`y ↦ ⟪t_k g_k - ∇ ω(x^k), y⟫ + ω(y)` over `C`. -/
def is_mirror_descent_trajectory
    (f ω : E → ℝ) (C : Set E) (x g : ℕ → E) (t : ℕ → ℝ) : Prop :=
  ∀ k,
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1))

-- Proof sketch: specialize the defining universal clause in
-- `is_mirror_descent_trajectory f ω C x g t` at the iteration index `k`.
/-- A mirror-descent trajectory satisfies the feasible-domain, subgradient, positive-stepsize, and
one-step minimization conditions at each iteration. -/
theorem is_mirror_descent_trajectory_step
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1)) := sorry

end
