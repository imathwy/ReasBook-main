import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u x

namespace Representation

section BrauerBasisOverCoefficientRing

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Exercise 18-18.2-9 / Serre Exercise 18.4: for a complete family of pairwise nonisomorphic
simple finite-dimensional `k[G]`-representations, the corresponding modular characters form a
basis of the field-valued functions on the `p`-regular conjugacy classes.

Serre's original exercise is stated over the coefficient ring `A` of a modular system. The previous
formal statement incorrectly allowed an arbitrary `CommRing A` and an arbitrary injective function
`PrimeToPRoot p k → A`; that is false already for the trivial group unless the lift preserves the
unit and the coefficient owner has the required integral structure. This compiled wrapper records
the sound field-valued form supplied by Theorem `18-18.2-1`; an `A`-valued strengthening should add
the missing modular-system hypotheses rather than quantifying over an arbitrary ring. -/
def exercise_18_18_2_9_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) :=
  -- Route correction: the canonical semiring-level owner is not currently available as a
  -- standalone compiled dependency in this workspace, so this exercise reuses the established
  -- field-valued theorem wrapper.
  irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
    (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_apply
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift) :=
by
  -- Read off the indexed basis vector from the established field-valued theorem wrapper.
  exact
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete i

/-- Helper for Exercise 18-18.2-9: the basis coordinates of the `i`-th modular character are the
standard basis vector at `i`. -/
@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_repr_modularCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    (exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete).repr
      (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift)) =
        Finsupp.single i 1 :=
by
  -- Rewrite the modular character as the `i`-th basis vector and apply the standard
  -- `repr_self` identity.
  rw [← exercise_18_18_2_9_irreducible_modular_characters_basis_apply
    (p := p) (lift := lift) (hlift := hlift) (E := E)
    (hE_pairwise := hE_pairwise) (hE_complete := hE_complete) (i := i)]
  exact
    (exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) lift hlift E hE_pairwise hE_complete).repr_self i

end BrauerBasisOverCoefficientRing

end Representation
