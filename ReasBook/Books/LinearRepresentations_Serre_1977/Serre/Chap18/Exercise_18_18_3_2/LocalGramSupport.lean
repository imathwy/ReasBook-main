import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8.Index
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_CartanGramSupport
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.CoordinateDescent
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section LocalGramSupport

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 18-18.3-2: once a sufficiently large mixed-character local-ring model is
fixed, Chapter `16` gives the Cartan matrix as the Gram matrix of the decomposition matrix. -/
theorem cartanMatrix_source_faithful_gram_eq_of_support
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  classical
  obtain ⟨κ, πK, hπK_pairwise, hπK_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField (L := K) (G := G)
  letI : Finite κ :=
    finiteOfCompletePairwiseNonisomorphicSimpleFamily
      (F := K) (G := G) πK hπK_pairwise hπK_complete
  letI : Fintype κ := Fintype.ofFinite κ
  letI : DecidableEq κ := Classical.decEq κ
  let bK :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let bk :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let D : Matrix ι κ ℤ :=
    LinearMap.toMatrix bK bk (decompositionHom A K G).toIntLinearMap
  refine ⟨κ, inferInstance, inferInstance, D.transpose, ?_⟩
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  have hGram :=
    cartanMatrix_eq_decomposition_toMatrix_transpose_mul_decomposition_toMatrix
      (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete
      πK hπK_pairwise hπK_complete
      P hP_envelope
  simpa [D, bP, bk, bK] using hGram

end LocalGramSupport

end Representation
