import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreIntegralRepresentatives
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ReversePointSourceEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductSerreBasisReverseABasis

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance canonicalSourceProductSerreBasisReverseABasisFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductSerreBasisReverseABasisDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [DecidableEq ι] in
/-- A non-fixed reverse point-source representative expands in any complete simple
Grothendieck basis, giving the requested integral linear combination of Serre 18.4 Brauer rows
modulo Serre's regular-value divisibility lattice. -/
theorem canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives_of_reversePointSourceCongruence
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  intro c
  rcases hpoint c with ⟨x, hx⟩
  refine ⟨fun i : ι ↦ bR.repr x i, ?_⟩
  have hχ_expand :
      χ x =
        ∑ i : ι, (bR.repr x i) • χ ([π i]₀ : R₀[k](G)) := by
    calc
      χ x = χ (∑ i : ι, (bR.repr x i) • bR i) := by
          exact congrArg χ (bR.sum_repr x).symm
      _ = ∑ i : ι, χ ((bR.repr x i) • bR i) := by
          rw [map_sum]
      _ = ∑ i : ι, (bR.repr x i) • χ (bR i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [map_zsmul]
      _ = ∑ i : ι, (bR.repr x i) • χ ([π i]₀ : R₀[k](G)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
  have hxD :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        χ x ∈ D := by
    simpa [D, χ,
      canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hx
  simpa [D, χ, hχ_expand]
    using hxD

omit [DecidableEq ι] in
/-- The global source-faithful regular-value congruence supplies reverse point representatives
for any complete Serre 18.4 Brauer basis.

The witness is obtained by taking the virtual modular character with the prescribed integer
regular-class coordinate and expanding it in the chosen simple Grothendieck basis. -/
theorem canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives_of_regularValueCongruenceSourceFaithfulStatement
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π :=
  canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives_of_reversePointSourceCongruence
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
    (canonicalVirtualModularCartanProductReversePointSourceCongruence_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G) hregular)

end CanonicalSourceProductSerreBasisReverseABasis

end Representation
