import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_5 (from Chap09) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g ω : E → EReal} {σ : ℝ}

/- Definition 9.5 is a `source-facing` specialization in the Chapter 9 mirror-descent API. The
`core/canonical` owner remains `IsBregmanPotentialOn`, but the textbook statement is not the bare
owner itself: it is the composite-model specialization obtained by instantiating the constraint set
to `dom(g) = effective_domain g`. The main entry should therefore present that specialized type
expression directly, rather than recalling the unspecialized owner name alone. -/

/- Definition 9.5: in the composite model, the standing assumptions on the mirror map `ω` are
exactly that `ω` is a Bregman potential on `dom(g) = effective_domain g` with modulus `σ`. -/
#check (IsBregmanPotentialOn ω (effective_domain g) σ)

end

/-! ### Text_9_5 (from Chap09) -/
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
