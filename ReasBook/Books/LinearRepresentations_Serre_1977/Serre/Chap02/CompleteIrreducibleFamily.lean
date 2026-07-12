import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import Mathlib.RepresentationTheory.FDRep

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]
variable {ι : Type v}

/-
This file is a bridge/view layer. The owner declarations
`CategoryTheory.PairwiseNonisomorphic`,
`Representation.IsCompleteIrreducibleFamily`, and
`Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation`
already live canonically in `Serre.Chap03.Theorem_3_3_2_1`.
Only the representation-level companion theorem below is local here.
-/

section Rep

variable {π : ι → Rep K G}
variable [∀ i, FiniteDimensional K (π i)]

/-- Completeness at the canonical `FDRep` owner level implies irreducibility of each
representation in the underlying family. -/
theorem IsCompleteIrreducibleFamily.isIrreducible_of_rep
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) : (π i).ρ.IsIrreducible := by
  letI : Simple (FDRep.of (π i).ρ) := hπ_complete.isSimple i
  exact FDRep.isIrreducible_of_simple (FDRep.of (π i).ρ)

end Rep

end

end Representation
