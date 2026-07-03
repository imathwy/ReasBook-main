

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_30 (from Chap05) -/
universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

recall effective_domain
recall is_convex_function
recall infimal_convolution

/- Theorem 5.30 is `source-facing` in the chapter infimal-convolution smoothing calculus. The owner
objects are Chapter 2's `effective_domain`, `is_convex_function`, and
`infimal_convolution`, together with Chapter 5's smoothness predicate `is_l_smooth_on`,
specialized to `Set.univ`. The theorem is therefore stated directly for the canonical infimal
convolution `f □ ω`, viewed as the real-valued map `x ↦ ((f □ ω) x).toReal` under the standing
everywhere-finite hypothesis, rather than through an auxiliary wrapper for the minimizing problem.
Because the kernel `ω` is real-valued and `hreal` makes `f □ ω` finite everywhere, the textbook
properness assumption on `f` is derived background data rather than primitive public input. -/

local notation:65 f " □r " ω =>
  infimal_convolution f (fun z ↦ (ω z : EReal))

variable (f : E → EReal) (ω : E → ℝ) (L : NNReal)
variable (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
variable (hω_convex : ConvexOn ℝ Set.univ ω) (hω_smooth : is_l_smooth_on ω Set.univ L)
variable (hreal : ∀ x, ∃ r : ℝ, (f □r ω) x = (r : EReal))

-- Proof sketch: for each `x`, pick a minimizer of `u ↦ f u + ω (x - u)`, use first-order
-- optimality to produce a subgradient of `f` balancing `∇ ω (x - u(x))`, and deduce that this
-- vector is a subgradient of the real-valued infimal convolution. Monotonicity of the
-- subdifferential of `f` together with cocoercivity of the gradient of the convex `L`-smooth
-- kernel `ω` gives the `L`-Lipschitz bound for the resulting gradient field.
/-- Theorem 5.30 (1): if `f` is proper closed convex, `ω` is a convex `L`-smooth real-valued
function, and the infimal convolution `f □ ω` is everywhere finite, then the real-valued map
`x ↦ ((f □ ω) x).toReal` is `L`-smooth. In this owner-level formulation, the properness of `f`
from the textbook statement is forced by the everywhere-finite hypothesis on `f □ ω`, so it is
not kept as separate public data. -/
theorem infimal_convolution_toReal_is_l_smooth
    : is_l_smooth_on (fun x ↦ ((f □r ω) x).toReal) Set.univ L := sorry

-- Proof sketch: the minimizer assumption identifies `u` as an optimizer of the defining infimum at
-- `x`. The optimality condition yields `∇ ω (x - u) ∈ ∂f(u)`, hence the same vector is a
-- subgradient of `y ↦ ((f □ ω) y).toReal` at `x`. Part (1) supplies differentiability of the
-- infimal convolution, so Proposition 3.14 identifies its unique subgradient with its gradient,
-- giving the displayed formula.
/-- Theorem 5.30 (2): if `u` minimizes `v ↦ f(v) + ω(x - v)` at `x`, then the gradient of the
real-valued infimal convolution at `x` is the gradient of `ω` at `x - u`. As in part (1), the
textbook properness hypothesis is derived from the standing finiteness assumption on `f □ ω`
rather than carried separately in the public interface. -/
theorem gradient_infimal_convolution_toReal_eq_gradient_sub_of_isMinOn
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + (ω (x - v) : EReal)) Set.univ u) :
    ∇ (fun y ↦ ((f □r ω) y).toReal) x = ∇ ω (x - u) := sorry

end
