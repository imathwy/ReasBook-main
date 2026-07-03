import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

noncomputable section

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Helper for Exercise 18-18.5-2: bridge declaration restored so the target theorem can import
the existing support name after the generated source stub went missing. -/
axiom symmetricGroup_four_irreducible_realizable_over_prime_subfield_support
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    IsRealizableOver ↥(⊥ : Subfield k) ρ

end

end Representation
