import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 9.5 is a `bridge/view` item. The Chapter 9 owner abstraction for the one-step
mirror-descent objective already exists upstream as `mirror_descent_update_objective`, and the
complete-the-square algebra is already owned by Chapter 6's `quadratic_translate_identity`. The
source-facing content here is the quadratic specialization `ω(y) = ‖y‖² / 2` and its equivalence
with the projected-subgradient minimization on the feasible set `C`. Although the textbook states
this in Euclidean space, the reused owner APIs already work over a real complete inner-product
space, so the bridge is stated at that canonical ambient level instead of keeping an unnecessary
finite-dimensional wrapper. -/

-- Proof sketch: differentiate `x ↦ ‖x‖² / 2` in a real Hilbert space and identify the resulting
-- Fréchet derivative with the inner product against `x`.
/-- The gradient of the half squared Euclidean norm is the identity map. -/
theorem gradient_half_squared_norm_eq_self (x : E) :
    ∇ (fun y : E ↦ ‖y‖ ^ (2 : ℕ) / 2) x = x := sorry

-- Proof sketch: start from `mirror_descent_update_objective_apply` for the Euclidean mirror map
-- `ω(y) = ‖y‖² / 2`, use `gradient_half_squared_norm_eq_self` to rewrite the linear term, and then
-- specialize `quadratic_translate_identity` to the center `x - t • g`.
/-- Completing the square rewrites the Euclidean specialization of
`mirror_descent_update_objective` as the half squared distance to `x - t • g`, up to an additive
constant independent of `y`. -/
theorem euclidean_mirror_descent_objective_eq_half_squared_distance
    (x g y : E) (t : ℝ) :
    mirror_descent_update_objective (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) x g t y =
      ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 - ‖x - t • g‖ ^ (2 : ℕ) / 2 := sorry

-- Proof sketch: rewrite the mirror-descent objective with
-- `euclidean_mirror_descent_objective_eq_half_squared_distance`; the additive constant does not
-- affect minimizers, so the specialized mirror-descent step and the projected-subgradient step
-- define the same `IsMinOn` condition on the feasible set `C`.
/-- Text 9.5: in a real Hilbert space, hence in particular in Euclidean space, choosing the
mirror map `ω(x) = ‖x‖² / 2`, for which `∇ω(x) = x`, turns the mirror-descent
one-step minimization into the
projected subgradient one-step minimization of the half squared distance to `x - t • g`.
Equivalently, the two objectives have the same minimizers on the feasible set `C`.
-/
theorem mirror_descent_half_squared_norm_step_iff_projected_subgradient_step
    (C : Set E) (x g xNext : E) (t : ℝ) :
    IsMinOn (mirror_descent_update_objective (fun y : E ↦ ‖y‖ ^ (2 : ℕ) / 2) x g t) C xNext ↔
      IsMinOn (fun y : E ↦ ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2) C xNext := sorry

end
