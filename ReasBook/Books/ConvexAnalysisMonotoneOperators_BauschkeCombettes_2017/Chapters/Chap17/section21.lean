import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_17_21 (from Chap17) -/
open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: combine the monotonicity of directional difference quotients from Proposition
-- 9.27 with the infimum formula from Proposition 17.2 (1); strict decrease on a short initial ray
-- is equivalent to the limit infimum, hence the directional derivative, being strictly negative.
/-- Proposition 17.21 (1): for a proper convex `]-∞,+∞]`-valued function, a vector `y` is a
descent direction at an effective-domain point `x` exactly when the directional derivative
`f'(x; y)` is strictly negative. -/
theorem isDescentDirectionAt_iff_directionalDerivative_lt_zero
    {x y : H} (hx : x ∈ effectiveDomain f) :
    IsDescentDirectionAt f x y ↔ f′(x; y) < 0 := sorry

end RealVectorSpace

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: Proposition 17.4 turns `x ∉ Argmin f.asEReal` into `gradf ≠ 0`, and
-- the
-- differentiability formula for directional derivatives gives
-- `f′(x; -gradf) = -‖gradf‖^2 < 0`; then apply clause (1).
/-- Proposition 17.21 (2): if a convex `]-∞,+∞]`-valued function has Gâteaux gradient `gradf` at
an effective-domain point `x` and `x` is not a minimizer, then the negative gradient `-gradf` is a
descent direction of `f` at `x`. -/
theorem neg_gateauxGradient_isDescentDirectionAt_of_not_mem_argmin
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x)
    (hxnot : x ∉ Argmin f.asEReal) :
    IsDescentDirectionAt f x (-gradf) := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
