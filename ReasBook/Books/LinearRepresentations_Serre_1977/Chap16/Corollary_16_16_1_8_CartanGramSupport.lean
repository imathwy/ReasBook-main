import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u x

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 16-16.1-8: support theorem packaging the source-faithful Gram
factorization of the distinguished Cartan matrix. -/
theorem cartanMatrix_source_faithful_gram_data_support
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hP_envelope :
      ∀ i, ∃ f :
        (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
          f.IsProjectiveEnvelope)
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E ∧ Function.Injective E.mulVec := by
  sorry

end

end Representation
