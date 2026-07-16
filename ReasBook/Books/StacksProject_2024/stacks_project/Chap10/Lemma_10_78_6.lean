import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_94_1
import StacksProject_2024.stacks_project.Chap10.Theorem_10_95_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
variable [AddCommGroup M] [Module R M]

/-- An `R`-module is finite projective if it is both finite and projective. -/
def Module.FiniteProjective (R : Type u) (M : Type w) [CommRing R] [AddCommMonoid M] [Module R M] :
    Prop :=
  Module.Finite R M ∧ Module.Projective R M

-- Proof sketch: the forward implication uses base change for finite and projective modules, namely
-- `Module.Finite.base_change` and the canonical owner instance `Projective.tensorProduct`. For the
-- converse, a flat local homomorphism is faithfully flat by
-- `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and the canonical descent theorems recover
-- finiteness and projectivity of `M` from the base change `S ⊗[R] M`.
/-- Lemma 10.78.6: for a flat local homomorphism `R → S` of local rings and an `R`-module `M`,
`M` is finite projective over `R` if and only if the base-change `S ⊗[R] M` is finite projective
over `S`. -/
theorem finite_projective_iff_finite_projective_tensor_of_flat_localHom :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := sorry

end
