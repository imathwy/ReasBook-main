module

import Mathlib.Algebra.Group.Prod

public section

universe u v w

/- Example 67.2: Realizing binary external direct sums by products, the two
parenthesizations of a three-summand abelian group are canonically additively
equivalent. Lean parses `G₁ × G₂ × G₃` as `G₁ × (G₂ × G₃)`. -/
#check fun (G₁ : Type u) (G₂ : Type v) (G₃ : Type w)
    [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃] ↦
  (AddEquiv.prodAssoc : (G₁ × G₂) × G₃ ≃+ G₁ × (G₂ × G₃))
