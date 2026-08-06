import Mathlib.Topology.VectorBundle.FiniteDimensional

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Bundle

section

variable {B : Type u} {n : ℕ} {E : B → Type v}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [(b : B) → TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [(b : B) → AddCommMonoid (E b)] [(b : B) → Module ℝ (E b)]

/- Definition 23.1.1: an `n`-plane vector bundle over `B` is formalized as a family
`E : B → Type*` of `n`-dimensional real vector spaces that is locally trivial over `B`. In this
chapter's real setting, mathlib formalizes this directly by the canonical owner
`VectorBundle ℝ (Fin n → ℝ) E`; the normed and topological hypotheses required by that owner
remain ambient rather than part of an extra textbook-specific wrapper. -/
#check VectorBundle ℝ (Fin n → ℝ) E

end
