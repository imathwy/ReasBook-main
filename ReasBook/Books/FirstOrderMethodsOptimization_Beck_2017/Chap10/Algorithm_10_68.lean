import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- `prompt_add/` is absent in this workspace, so the nearby Chapter 9 and Chapter 10 files
supply the relevant owner discipline.

Algorithm 10.68 is `source-facing`: it defines the iterate sequence for the non-Euclidean
proximal-gradient method. The domain-style sampling in this part of the project points to:
- `non_euclidean_proximal_gradient_step` from Algorithm 10.67 as the chapter owner of the
  one-step update set;
- `mirror_c_update_objective` from Definition 9.6 as the core one-step linearized mirror
  objective used by that step owner;
- `is_differentiable_at` from Definition 3.10 as the Chapter 3 owner for the genuine textbook
  derivative of `x ↦ f(x)`;
- `effective_domain` and `subdifferential_domain` for the source domain clause
  `x^k ∈ dom(g) ∩ dom(∂ω)`;
- `PosReal` for the positive curvature parameters `L_k`.

The layer split is:
- `source-facing`: the trajectory predicate in this file;
- `core/canonical`: `non_euclidean_proximal_gradient_step`;
- `bridge/view`: Algorithm 10.67's Bregman-model reformulation of that step set.

Primitive data:
- the source domain clause `x^k ∈ dom(g) ∩ dom(∂ω)`;
- the canonical step predicate from Algorithm 10.67, which already packages the Chapter 3
  differentiability clause together with the specialized Mirror-C minimization rule.

Derived API:
- projection lemmas exposing the iterate-domain clause, differentiability, and the specialized
  Mirror-C minimization rule separately.

So the correct refinement is to reuse the Algorithm 10.67 step owner directly, rather than
restating its differentiability and argmin data in a parallel local predicate. -/

/-- Algorithm 10.68: a sequence `x^k` follows the non-Euclidean proximal-gradient method for the
composite objective `f + g` with mirror map `ω` and positive curvature parameters `L_k` when, at
every iteration `k`, the current iterate lies in `dom(g) ∩ dom(∂ω)` and the next iterate
`x^(k+1)` satisfies the canonical Algorithm 10.67 step predicate. That owner already includes the
Chapter 3 differentiability condition at `x^k` together with the specialized Mirror-C minimizer
clause. -/
def is_non_euclidean_proximal_gradient_trajectory
    (f g ω : E → EReal) (x : ℕ → E) (L : ℕ → PosReal) : Prop :=
  ∀ k : ℕ,
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1))

/-- Along a non-Euclidean proximal-gradient trajectory, `f` is differentiable at every iterate
`x^k` in the Chapter 3 sense. -/
theorem is_non_euclidean_proximal_gradient_trajectory_differentiable_at
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    is_differentiable_at f (x k) :=
  (h k).2.differentiable_at

/-- Along a non-Euclidean proximal-gradient trajectory, every iterate `x^k` lies in
`dom(g) ∩ dom(∂ω)`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_mem_domains
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω :=
  (h k).1

/-- Along a non-Euclidean proximal-gradient trajectory, the next iterate `x^(k+1)` belongs to the
canonical one-step update set from Algorithm 10.67. -/
theorem is_non_euclidean_proximal_gradient_trajectory_mem_step
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
  (h k).2

/-- Along a non-Euclidean proximal-gradient trajectory, the next iterate `x^(k+1)` globally
minimizes the specialized Mirror-C update objective at step `k`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_isMinOn
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    IsMinOn
      (mirror_c_update_objective g ω (x k)
        (fderiv ℝ (fun y ↦ (f y).toReal) (x k)) ((L k : ℝ)⁻¹))
      Set.univ (x (k + 1)) :=
  (is_non_euclidean_proximal_gradient_trajectory_mem_step h k).isMinOn

/-- A non-Euclidean proximal-gradient trajectory satisfies the domain condition
`x^k ∈ dom(g) ∩ dom(∂ω)` and the canonical Algorithm 10.67 step predicate at each iteration `k`.
The Chapter 3 differentiability condition at `x^k` is part of that step predicate. -/
theorem is_non_euclidean_proximal_gradient_trajectory_step
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
  h k

end
