import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {M' : Type z} [AddCommMonoid M'] [Module R M']

/-- Definition 10.88.2: a map `g : M →ₗ[R] M'` dominates a map `f : M →ₗ[R] N` if, after
tensoring with any `R`-module `Q`, the kernel of `f ⊗ 1_Q` is contained in the kernel of
`g ⊗ 1_Q`. -/
@[stacks 059B]
def Dominates (g : M →ₗ[R] M') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u v w z)) [AddCommMonoid Q] [Module R Q],
    ker (f.rTensor Q) ≤ ker (g.rTensor Q)

/-- A linear map `g` dominates `f` exactly when every tensor kernel of `f` is contained in the
corresponding tensor kernel of `g`. -/
theorem dominates_iff (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type (max u v w z)) [AddCommMonoid Q] [Module R Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) :=
  Iff.rfl

end

end LinearMap
