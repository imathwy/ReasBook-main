import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_17_17 (from Chap17) -/
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use Proposition 17.14 to rewrite `u ∈ ∂ f(x)` as the pointwise domination
-- `⟪·,u⟫ ≤ f'(x;·)`. Then unfold the Fenchel conjugate of `f'(x;·)` and apply the
-- Fenchel--Young equality criterion from Proposition 16.10 together with Proposition 13.15 to
-- show that the conjugate value is `0` exactly on `∂ f(x)` and `⊤` off that set.
/-- Proposition 17.17: for a convex `]-∞,+∞]`-valued function and an effective-domain point `x`,
the Fenchel conjugate of the directional derivative `y ↦ f'(x; y)` is the indicator of the
subdifferential `∂ f(x)`. -/
theorem conjugate_directionalDerivative_eq_setIndicator_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    (directionalDerivative f x)∗ = (ι[(∂ f) x]).asEReal := sorry

end DirectionalDerivativesAndSubgradients

end ERealFunction
