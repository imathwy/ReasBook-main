import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibilityEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductImageFromSerreBasis

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

local instance canonicalSourceProductImageFromSerreBasisFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageFromSerreBasisDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Forward Serre-basis representatives.

For each simple Brauer basis row, choose an arbitrary integer regular-class function with the
same image modulo Serre's divisibility lattice. This is weaker than asking the row to be
congruent to its own coordinate point mass. -/
def canonicalSourceProductSerreBasisForwardInput
    (π : ι → FDRep k G) : Prop :=
  ∀ i : ι,
    ∃ g : PRegularConjClass G p → ℤ,
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
          canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)

/-- Reverse Serre-basis representatives for the point masses of the diagonal product.

Each integer point mass may be represented by an arbitrary integral linear combination of the
Serre 18.4 simple Brauer basis rows. -/
def canonicalSourceProductSerreBasisReversePointInput
    (π : ι → FDRep k G) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ m : ι → ℤ,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        ∑ i : ι,
          m i •
            virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π i]₀ : R₀[k](G)) ∈
          canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
omit [DecidableEq ι] in
/-- Forward representatives for the canonical source-product image from arbitrary integer
representatives of the Serre 18.4 simple Brauer basis rows. -/
theorem canonicalVirtualModularCartanProduct_forwardRepresentative_of_serreBasis
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hforward :
      canonicalSourceProductSerreBasisForwardInput
        (p := p) (A := A) (K := K) (G := G) π) :
    ∀ x : R₀[k](G),
      ∃ g : PRegularConjClass G p → ℤ,
        cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom k G).range x) =
          regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let S : Submodule A (PRegularConjClass G p → K) :=
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
  let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  choose g hg using hforward
  intro x
  let gsum : PRegularConjClass G p → ℤ := ∑ i : ι, (bR.repr x i) • g i
  refine ⟨gsum, ?_⟩
  have hx_expand :
      x = ∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G)) := by
    calc
      x = ∑ i : ι, (bR.repr x i) • bR i := (bR.sum_repr x).symm
      _ = ∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
  have hχ_expand :
      χ x =
        ∑ i : ι, (bR.repr x i) • χ ([π i]₀ : R₀[k](G)) := by
    calc
      χ x = χ (∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G))) := by
          exact congrArg χ hx_expand
      _ = ∑ i : ι, χ ((bR.repr x i) • ([π i]₀ : R₀[k](G))) := by
          rw [map_sum]
      _ = ∑ i : ι, (bR.repr x i) • χ ([π i]₀ : R₀[k](G)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [map_zsmul]
  have hcast_expand :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
        ∑ i : ι,
          (bR.repr x i) •
            regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) := by
    ext c
    simp [gsum, regularIntegerFunctionCast, Finset.sum_apply]
  have hdiff :
      χ x - regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
        ∑ i : ι,
          (bR.repr x i) •
            (χ ([π i]₀ : R₀[k](G)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)) := by
    rw [hχ_expand, hcast_expand]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [zsmul_sub]
  have hmem :
      χ x - regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum ∈ S := by
    rw [hdiff]
    refine Submodule.sum_mem S ?_
    intro i _hi
    exact S.toAddSubgroup.zsmul_mem (by simpa [S, χ] using hg i) (bR.repr x i)
  have hneg :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum - χ x ∈ S := by
    simpa [S, χ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using S.neg_mem hmem
  exact
    (regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
      (p := p) (A := A) (K := K) (G := G) gsum x hneg).symm

omit [IsFractionRing A K] [DecidableEq ι] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Reverse point-source congruences from arbitrary integral Serre-basis representatives of the
integer point masses. -/
theorem canonicalVirtualModularCartanProduct_reversePointSourceCongruence_of_serreBasis
    (π : ι → FDRep k G)
    (hreverse :
      canonicalSourceProductSerreBasisReversePointInput
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductReversePointSourceCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  intro c
  rcases hreverse c with ⟨m, hm⟩
  refine ⟨∑ i : ι, m i • ([π i]₀ : R₀[k](G)), ?_⟩
  have hχ_sum :
      χ (∑ i : ι, m i • ([π i]₀ : R₀[k](G))) =
        ∑ i : ι, m i • χ ([π i]₀ : R₀[k](G)) := by
    calc
      χ (∑ i : ι, m i • ([π i]₀ : R₀[k](G))) =
          ∑ i : ι, χ (m i • ([π i]₀ : R₀[k](G))) := by
            rw [map_sum]
      _ = ∑ i : ι, m i • χ ([π i]₀ : R₀[k](G)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [map_zsmul]
  change
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
      χ (∑ i : ι, m i • ([π i]₀ : R₀[k](G))) ∈
        canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
  rw [hχ_sum]
  simpa [canonicalSourceProductSerreBasisReversePointInput, χ] using hm

set_option linter.style.longLine false in
omit [DecidableEq ι] in
/-- Reverse representatives for every integer regular-class function from the Serre-basis
reverse point representatives. -/
theorem canonicalVirtualModularCartanProduct_reverseRepresentative_of_serreBasis
    (π : ι → FDRep k G)
    (hreverse :
      canonicalSourceProductSerreBasisReversePointInput
        (p := p) (A := A) (K := K) (G := G) π) :
    ∀ g : PRegularConjClass G p → ℤ,
      ∃ x : R₀[k](G),
        regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
          cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom k G).range x) := by
  have hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G) :=
    canonicalVirtualModularCartanProduct_reversePointSourceCongruence_of_serreBasis
      (p := p) (A := A) (K := K) (G := G) π hreverse
  intro g
  rcases
      canonicalVirtualModularCartanProduct_reverseSourceCongruence_of_reverse_point_source_congruence
        (p := p) (A := A) (K := K) (G := G) hpoint g with
    ⟨x, hx⟩
  exact
    ⟨x,
      regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
        (p := p) (A := A) (K := K) (G := G) g x hx⟩

omit [DecidableEq ι] in
/-- Serre-basis forward and reverse representatives identify the canonical source-product image
with the coordinatewise integer image. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hforward :
      canonicalSourceProductSerreBasisForwardInput
        (p := p) (A := A) (K := K) (G := G) π)
    (hreverse :
      canonicalSourceProductSerreBasisReversePointInput
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProduct_forwardRepresentative_of_serreBasis
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete hforward)
    (canonicalVirtualModularCartanProduct_reverseRepresentative_of_serreBasis
      (p := p) (A := A) (K := K) (G := G) π hreverse)

/-- Projective-restriction witness form of the forward Serre-basis representatives.  This is the
direct place where Serre 18.5(a) applies. -/
def canonicalSourceProductSerreBasisForwardProjectiveWitness
    (π : ι → FDRep k G) : Prop :=
  ∀ i : ι,
    ∃ g : PRegularConjClass G p → ℤ,
      ∃ Φ : A ⊗R[K](G),
        Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
          regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
                ([π i]₀ : R₀[k](G)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g

/-- Projective-restriction witness form of the reverse Serre-basis point representatives. -/
def canonicalSourceProductSerreBasisReversePointProjectiveWitness
    (π : ι → FDRep k G) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ m : ι → ℤ,
      ∃ Φ : A ⊗R[K](G),
        Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
          regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
              ∑ i : ι,
                m i •
                  virtualModularCharacterOnPRegularConjClass
                    (p := p) (A := K) (G := G)
                    (PrimeToPRoot.toFieldLift
                      (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
                    ([π i]₀ : R₀[k](G))

omit [Fintype ι] [DecidableEq ι] in
/-- Serre 18.5(a) turns projective-restriction witnesses into forward Serre-basis
representatives. -/
theorem canonicalSourceProductSerreBasisForwardInput_of_projectiveWitness
    (π : ι → FDRep k G)
    (hwitness :
      canonicalSourceProductSerreBasisForwardProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisForwardInput
      (p := p) (A := A) (K := K) (G := G) π := by
  intro i
  rcases hwitness i with ⟨g, Φ, hΦ, hΦres⟩
  refine ⟨g, ?_⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    ⟨Φ, hΦ, rfl⟩
  have hD :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G), hΦres] using hD

omit [DecidableEq ι] in
/-- Serre 18.5(a) turns projective-restriction witnesses into reverse Serre-basis point
representatives. -/
theorem canonicalSourceProductSerreBasisReversePointInput_of_projectiveWitness
    (π : ι → FDRep k G)
    (hwitness :
      canonicalSourceProductSerreBasisReversePointProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisReversePointInput
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases hwitness c with ⟨m, Φ, hΦ, hΦres⟩
  refine ⟨m, ?_⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    ⟨Φ, hΦ, rfl⟩
  have hD :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G), hΦres] using hD

omit [DecidableEq ι] in
/-- Projective-restriction witnesses for the two Serre-basis representative directions identify
the canonical source-product image with the coordinatewise integer image. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_projectiveWitness
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hforward :
      canonicalSourceProductSerreBasisForwardProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π)
    (hreverse :
      canonicalSourceProductSerreBasisReversePointProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
    (canonicalSourceProductSerreBasisForwardInput_of_projectiveWitness
      (p := p) (A := A) (K := K) (G := G) π hforward)
    (canonicalSourceProductSerreBasisReversePointInput_of_projectiveWitness
      (p := p) (A := A) (K := K) (G := G) π hreverse)

end CanonicalSourceProductImageFromSerreBasis

end Representation
