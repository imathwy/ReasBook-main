import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {V' : Type u} [AddCommGroup V'] [Module ℂ V']
variable (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V')

/- Definition 1-1.1-1: a complex linear representation of a group `G` on `V` is the canonical
mathlib notion `Representation ℂ G V`, namely a homomorphism from `G` to the invertible complex
linear endomorphisms of `V`. -/
recall Representation

/- Similarity of two complex representations is modeled by the equivariant linear equivalence type
`ρ.Equiv ρ'`. -/
recall Representation.Equiv

section

variable [FiniteDimensional ℂ V]

/- The degree of a finite-dimensional complex representation is its complex dimension
`Module.finrank ℂ V`. -/
recall Module.finrank

end

namespace Representation.Equiv

-- Proof sketch: forget the equivariance and apply `LinearEquiv.finrank_eq` to the underlying
-- linear equivalence `τ.toLinearEquiv`.
/-- Similar complex representations have the same complex dimension, hence the same degree
whenever both are finite-dimensional. -/
theorem finrank_eq (τ : ρ.Equiv ρ') : Module.finrank ℂ V = Module.finrank ℂ V' :=
  τ.toLinearEquiv.finrank_eq

end Representation.Equiv

end
