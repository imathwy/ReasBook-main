import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.ProofStub

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Exercise 18-18.5-2: every irreducible representation of `S₄` over an algebraically closed
field is realizable over the prime field, i.e. over the smallest subfield `⊥ ≤ k`.
Finite-dimensionality is automatic here. -/
theorem symmetricGroup_four_irreducible_realizable_over_prime_subfield
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    IsRealizableOver ↥(⊥ : Subfield k) ρ := by
  let _ : IsAlgClosed k := inferInstance
  exact symmetricGroup_four_irreducible_realizable_over_prime_subfield_support (ρ := ρ)

end

end Representation
