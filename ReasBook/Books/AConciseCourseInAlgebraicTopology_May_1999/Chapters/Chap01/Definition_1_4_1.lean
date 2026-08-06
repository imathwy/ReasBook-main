import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Path.Homotopic.Quotient

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

/- Definition 1.4.1: a continuous map `p : X → Y` induces a map on loop classes, hence on
`π₁(X, x) = Path.Homotopic.Quotient x x`, by sending the class `[f]` to the class `[p ∘ f]`. -/
recall map (γ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁)

/- On loops, the same construction is the canonical induced homomorphism on the based fundamental
group. -/
recall FundamentalGroup.map (f : C(X, Y)) (x : X) :
    FundamentalGroup X x →* FundamentalGroup Y (f x)
