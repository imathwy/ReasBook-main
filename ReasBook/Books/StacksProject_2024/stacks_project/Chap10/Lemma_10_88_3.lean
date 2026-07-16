import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_88_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {M' : Type z} [AddCommMonoid M'] [Module R M']

-- Proof sketch: the forward implication is immediate from the definition. For the converse, write
-- an arbitrary `R`-module as a directed colimit of finitely presented modules and use that tensor
-- product commutes with directed colimits and those colimits are exact.
/-- Lemma 10.88.3: a map `g` dominates a map `f` if and only if it suffices to test the tensor
kernel inclusion `ker (f ⊗ 1_Q) ⊆ ker (g ⊗ 1_Q)` on finitely presented `R`-modules `Q`. -/
theorem dominates_iff_forall_finitePresentation
    (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type (max u v w z)) [AddCommMonoid Q] [Module R Q]
        [Module.FinitePresentation R Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  rw [dominates_iff]
  sorry

end

end LinearMap
