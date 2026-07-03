import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u x

namespace Representation

section BrauerBasisOverCoefficientRing

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Exercise 18-18.2-9 / LinearRepresentations_Serre_1977 Exercise 18.4: for a complete family of pairwise nonisomorphic
simple finite-dimensional `k[G]`-representations, the corresponding modular characters form a
basis of the coefficient-ring-valued functions on the `p`-regular conjugacy classes. -/
def exercise_18_18_2_9_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring
    (p := p) lift hlift E hE_pairwise hE_complete

@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_apply
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift := by
  -- This is the exercise-facing evaluation identity inherited from the canonical semiring basis.
  rw [exercise_18_18_2_9_irreducible_modular_characters_basis]
  simp

/-- Helper for Exercise 18-18.2-9: the basis coordinates of the `i`-th modular character are the
standard basis vector at `i`. -/
@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_repr_modularCharacter
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    (exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete).repr
      (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift) =
        Finsupp.single i 1 := by
  -- After rewriting the vector as the `i`-th basis element, this is the standard `repr_self`.
  simpa using
    (exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) lift hlift E hE_pairwise hE_complete).repr_self i

end BrauerBasisOverCoefficientRing

end Representation
