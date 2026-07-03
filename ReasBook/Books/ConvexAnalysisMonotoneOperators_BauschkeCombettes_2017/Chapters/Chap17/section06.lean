import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_17_6 (from Chap17) -/
open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
variable {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
variable
  (hgrad :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x)
include hconv hx hgrad

-- Proof sketch: identify the directional derivative of `f` at `x` in the direction `y - x` with
-- the derivative functional `toDualMap ℝ H gradf (y - x) = ⟪gradf, y - x⟫_ℝ` using the Gâteaux
-- differentiability hypothesis, then combine this identity with Proposition 17.2 (2).
/-- Proposition 17.6: at an effective-domain point of a convex extended-real-valued function, a
Gâteaux gradient defines a supporting hyperplane to `f` at `x`. -/
theorem gateauxGradient_add_value_le
    (y : H) :
    (⟪y - x, gradf⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := sorry

/-- Proposition 17.6, canonical Chapter 16 companion: the supporting-hyperplane inequality says
exactly that the Gâteaux gradient is a subgradient at `x`. -/
theorem gateauxGradient_mem_subdifferential
    :
    gradf ∈ (∂ f) x := by
  exact (mem_subdifferential_iff f x gradf).2 (gateauxGradient_add_value_le f hconv hx gradf hgrad)

end DifferentiabilityOfConvexFunctions

end ERealFunction
