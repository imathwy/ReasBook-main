import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {I : Type u}
variable (Ω : I → Type v)

/- Definition 14.1: the product of a family of sets `(Ω i)_{i ∈ I}` is canonically the dependent
function type `((i : I) → Ω i)`. This core Lean type is the owner abstraction for the textbook
product space, so no parallel local wrapper is needed. -/
#check ((i : I) → Ω i)

variable (Ω₀ : Type v)

/- In the homogeneous case `Ω i = Ω₀` for all `i`, the product specializes to the ordinary
function space `I → Ω₀`. -/
#check (I → Ω₀)
