import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.BrauerMultiplicity
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.EntryBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.HomFiber
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

section FiniteRepPositiveSubset

/-- Serre's actual positive subset `R_K^+(G)`, written here as `R⁺[K](G)`, consists of the classes
in `R_K(G)` represented by actual finite-dimensional `K[G]`-representations. -/
def finiteRepPositiveSubset
    (K : Type u) [Field K] (G : Type u) [Group G] :
    Set (R₀[K](G)) :=
  Set.range (finiteRepGrothendieckClass K G)

scoped[Representation] notation:max "R⁺[" K "](" G ")" =>
  finiteRepPositiveSubset K G

/-- Membership in `R_K^+(G)` means being the class of some actual finite-dimensional
`K[G]`-representation. -/
@[simp] theorem mem_finiteRepPositiveSubset_iff
    {x : R₀[K](G)} :
    x ∈ R⁺[K](G) ↔
      ∃ V : FDRep K G, [V]₀ = x :=
  Iff.rfl

/-- Actual finite-dimensional classes have nonnegative coordinates in any complete simple-class
basis. -/
theorem finiteRepPositiveSubset_subset_simpleBasis_positiveCone
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {x : R₀[K](G)}
    (hx : x ∈ R⁺[K](G)) :
    x ∈
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete).positiveCone := by
  rcases (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hx with ⟨V, hV⟩
  subst hV
  intro i
  exact
    simple_finiteRep_classes_basis_repr_class_nonneg
      (L := K) (G := G) π hπ_pairwise hπ_complete V i

end FiniteRepPositiveSubset

variable [Finite G]

/-- Serre's condition `(R)` for a subset `RKplus ⊆ R_K(G)` is the existence of a finite local
overring `A'` of `A` with fraction field `K'`, such that the scalar-extension map
`R_K(G) → R_K'(G)` identifies `RKplus` with the preimage of the actual positive cone in
`R_K'(G)`, and the decomposition map `R_K'(G) → R_k'(G)` sends that actual positive cone onto the
actual positive cone over the residue field `k' = IsLocalRing.ResidueField A'`. -/
def SatisfiesConditionR
    (RKplus : Set (R₀[K](G))) (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A')
      (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : Algebra A A')
      (_ : Module.Finite A A') (K' : Type u) (_ : Field K') (_ : Algebra A' K')
      (_ : Algebra A K') (_ : IsFractionRing A' K') (_ : Algebra K K')
      (_ : IsScalarTower A A' K') (_ : IsScalarTower A K K')
      (_ : FiniteDimensional K K'),
    RKplus = (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) ∧
      decompositionHom A' K' G '' R⁺[K'](G) = R⁺[IsLocalRing.ResidueField A'](G)

end

end Representation
