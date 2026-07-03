import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_6 (from Chap09) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 9.6 is `source-facing`: the textbook gives an iterative composite mirror-descent
procedure through explicit iterates, chosen positive stepsizes, chosen subgradients of `f`, and
the explicit unconstrained argmin update (9.32). The owner abstractions already present in the
project for these ingredients are `effective_domain`, `subdifferential_domain`,
`strongDualSubdifferential`, the continuous-dual derivative `fderiv ℝ (fun y ↦ (ω y).toReal) xk`,
and mathlib's minimizer predicate `IsMinOn`, so this item is best recorded as the explicit
one-step objective together with a trajectory predicate. The later equation-(9.33) Bregman rewrite
belongs in a separate `bridge/view` file and should reuse this equation-(9.32) owner rather than
duplicate it. -/

/-- The continuous linear functional `t s - ω'(xk)` appearing in the one-step Mirror-C problem. -/
def mirror_c_problem_functional
    (ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) : StrongDual ℝ E :=
  t • s - fderiv ℝ (fun y ↦ (ω y).toReal) xk

-- Proof sketch: unfold `mirror_c_problem_functional`; evaluation at `x` is exactly the displayed
-- linear functional `t s x - ω'(xk)(x)`.
/-- Evaluating the Mirror-C problem functional at `x` gives the scalar linear term
`t s(x) - ω'(xk)(x)`. -/
@[simp] theorem mirror_c_problem_functional_apply
    (ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ) :
    mirror_c_problem_functional ω xk s t x =
      t * s x - fderiv ℝ (fun y ↦ (ω y).toReal) xk x :=
  rfl

/-- The one-step Mirror-C objective from equation (9.32), written as the extended-real-valued
function `x ↦ (t s - ω'(xk))(x) + t g(x) + ω(x)` using a chosen strong-dual subgradient
`s ∈ ∂ f(xk)`. -/
def mirror_c_update_objective
    (g ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) : E → EReal :=
  fun x ↦
    (((mirror_c_problem_functional ω xk s t x : ℝ) : EReal) +
      (t : EReal) * g x) +
      ω x

-- Proof sketch: unfold `mirror_c_update_objective`; the displayed identity is exactly its
-- defining lambda expression.
/-- Evaluating the Mirror-C one-step objective at `x` gives the linear term
`(t s - ω'(xk))(x)` together with the composite penalty `t g(x) + ω(x)`. -/
@[simp] theorem mirror_c_update_objective_apply
    (g ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ) :
    mirror_c_update_objective g ω xk s t x =
      (((mirror_c_problem_functional ω xk s t x : ℝ) : EReal) +
        (t : EReal) * g x) +
        ω x := sorry

/-- Definition 9.6: sequences of iterates `x`, chosen subgradients `s`, and stepsizes `t`
follow the Mirror-C Method for the composite objective `f + g` with mirror map `ω` when at every
iteration `k` the current iterate lies in `dom(g) ∩ dom(∂ ω)`, the chosen functional `s k`
belongs to `∂ f(x^k)`, the stepsize `t k` is positive, and the next iterate `x^(k+1)` minimizes
the explicit Mirror-C objective from equation (9.32) over all `x`. -/
def is_mirror_c_trajectory
    (f g ω : E → EReal) (x : ℕ → E) (s : ℕ → StrongDual ℝ E) (t : ℕ → ℝ) : Prop :=
  ∀ k,
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      s k ∈ strongDualSubdifferential f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_c_update_objective g ω (x k) (s k) (t k)) Set.univ (x (k + 1))

-- Proof sketch: specialize the defining universal clause in
-- `is_mirror_c_trajectory f g ω x s t` at the iteration index `k`.
/-- A Mirror-C trajectory satisfies the domain, chosen-subgradient, positive-stepsize, and one-step
minimization conditions at each iteration. -/
theorem is_mirror_c_trajectory_step
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      s k ∈ strongDualSubdifferential f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_c_update_objective g ω (x k) (s k) (t k)) Set.univ (x (k + 1)) := sorry

end

/-! ### Text_9_6 (from Chap09) -/
open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ₂" => (Set.preimage (WithLp.ofLp : E → Fin n → ℝ) Δ : Set E)

/- Text 9.6 is `source-facing`: it specializes mirror descent on the unit simplex to the negative
entropy potential and then records the resulting Kullback-Leibler Bregman geometry and
exponentiated-gradient update formula. The owner abstractions already live upstream:
`negative_entropy_on_stdSimplex` is the simplex potential on coordinates, `B[ω]` is the Chapter 9
Bregman owner on the Euclidean `L²` ambient space, `mirror_descent_update_objective` is the
Chapter 9 one-step mirror-descent owner, and `entropy_linear_objective` / `softmax_point` are the
Chapter 3 simplex-side bridge formulas. This file therefore keeps only the source-facing simplex
specialization theorems and uses the entropy-linear formulas as companions to the owner-level
mirror-descent statement. -/

-- Proof sketch: unfold `entropy_linear_objective` and collect the linear term against
-- `fun i ↦ Real.log (x i) + 1 - t * g i`.
/-- Specializing `entropy_linear_objective` to the shifted log-weights
`i ↦ log (x_i) + 1 - t g_i` gives the explicit negative-entropy mirror-descent objective on the
simplex. -/
theorem entropy_linear_objective_log_add_one_sub_smul_apply
    (x g y : Fin n → ℝ) (t : ℝ) :
    entropy_linear_objective (fun i ↦ Real.log (x i) + 1 - t * g i) y =
      ∑ i, (t * g i - Real.log (x i) - 1) * y i + ∑ i, y i * Real.log (y i) := sorry

-- Proof sketch: unfold `softmax_point`, rewrite `exp (log (x i) - t * g i)` as
-- `x i * exp (-t * g i)` using `hx_pos`, and simplify the common normalization factor.
/-- Evaluating the canonical softmax point of the shifted log-weights
`i ↦ log (x_i) - t g_i` gives the exponentiated-gradient coordinate formula. -/
theorem softmax_point_log_sub_smul_apply
    (x g : Fin n → ℝ) (t : ℝ) (hx_pos : ∀ i, 0 < x i) (i : Fin n) :
    softmax_point (fun j ↦ Real.log (x j) - t * g j) i =
      x i * Real.exp (-t * g i) / ∑ j, x j * Real.exp (-t * g j) := sorry

-- Proof sketch: on simplex points `x` and `y`, rewrite the Chapter 9 mirror-descent objective
-- with `mirror_descent_update_objective_apply`, use the negative-entropy gradient identity
-- `∇ω(x)_i = log (x_i) + 1` at the strictly positive simplex point `x`, and simplify the
-- resulting expression to the Chapter 3 entropy-linear objective.
/-- On the simplex, the Chapter 9 mirror-descent objective for the negative-entropy mirror map is
the entropy-linear objective with shifted log-weights `i ↦ log (x_i) + 1 - t g_i`. -/
theorem mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
    (x g y : E) (t : ℝ)
    (hx : x ∈ Δ₂) (hx_pos : ∀ i, 0 < x i) (hy : y ∈ Δ₂) :
    mirror_descent_update_objective
        (fun z : E ↦ (negative_entropy_on_stdSimplex n z).toReal) x g t y =
      entropy_linear_objective (fun i ↦ Real.log (x i) + 1 - t * g i) y := sorry

-- Proof sketch: expand the Chapter 9 owner formula `B[negative_entropy_on_stdSimplex n] x y`,
-- use the gradient identity `∇ω(y)_i = log (y_i) + 1` at the strictly positive simplex point
-- `y`, and then cancel the linear terms with the simplex identities `∑ i, x i = 1` and
-- `∑ i, y i = 1`.
/-- The Chapter 9 Bregman distance of the simplex negative entropy is the Kullback-Leibler
divergence when the base point has strictly positive coordinates. -/
theorem negative_entropy_bregman_eq_kullbackLeibler
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    B[fun z : E ↦ negative_entropy_on_stdSimplex n z] x y =
      ∑ i, x i * Real.log (x i / y i) := sorry

-- Proof sketch: rewrite `B[negative_entropy_on_stdSimplex n] x y` with the Chapter 9 defining
-- formula, use the negative-entropy gradient identity `∇ω(y)_i = log (y_i) + 1`, and simplify the
-- resulting linear term on the simplex.
/-- Expanding the simplex negative-entropy Bregman distance yields the textbook
entropy-gradient formula. -/
theorem negative_entropy_bregman_eq_kullbackLeibler_expanded
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    (negative_entropy_on_stdSimplex n x).toReal -
      (negative_entropy_on_stdSimplex n y).toReal -
      ∑ i, (Real.log (y i) + 1) * (x i - y i) =
      ∑ i, x i * Real.log (x i / y i) := sorry

-- Proof sketch: first rewrite the simplex subproblem with
-- `mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective`. Then apply the
-- Chapter 3 softmax characterization of simplex minimizers and remove the irrelevant global
-- `+ 1` shift in the softmax weights, which does not change the normalized point.
/-- Text 9.6: on the unit simplex, the Chapter 9 mirror-descent step for the negative-entropy
mirror map is the canonical softmax point of the shifted log-weights
`i ↦ log (x_i) - t g_i`, hence coordinatewise the exponentiated-gradient formula
`x_i^+ = x_i * exp (-t g_i) / ∑_j x_j * exp (-t g_j)`. -/
theorem mirror_descent_step_eq_exponentiated_gradient
    (x g xNext : E) (t : ℝ)
    (hx : x ∈ Δ₂) (hx_pos : ∀ i, 0 < x i) :
    IsMinOn
        (mirror_descent_update_objective
          (fun z : E ↦ (negative_entropy_on_stdSimplex n z).toReal) x g t) Δ₂ xNext ↔
      xNext.ofLp = softmax_point (fun i ↦ Real.log (x i) - t * g i) := sorry

end
