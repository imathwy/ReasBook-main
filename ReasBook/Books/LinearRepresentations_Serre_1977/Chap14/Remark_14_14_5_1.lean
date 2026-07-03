import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open CategoryTheory

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Remark 14-14.5-1: if `K` is sufficiently large, then for every simple finite-dimensional
`k[G]`-representation `S`, the endomorphism space `S ⟶ S` is one-dimensional over
`k = IsLocalRing.ResidueField A`. This is the direct project realization of Serre's statement
`d_E = 1`. -/
theorem simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep k G) [Simple S] :
    Module.finrank k (S ⟶ S) = 1 := by
  -- The current Chapter 14 prefix does not yet expose the source-faithful bridge from the
  -- sufficiently-large generic-field hypothesis to the residue-field splitting statement needed
  -- to apply Schur's lemma downstairs.
  admit

end

end Representation
