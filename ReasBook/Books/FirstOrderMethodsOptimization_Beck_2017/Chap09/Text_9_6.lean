import Mathlib
import FirstOrderMethodsinOptimization.Chap03.Proposition_3_35
import FirstOrderMethodsinOptimization.Chap04.Proposition_4_16
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsinOptimization.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

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
