import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductForward
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductReverse

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProductBasisImage

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]


local instance projectiveCartanSourceProductBasisImageFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceProductBasisImageDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The basis-vector source congruence implies the forward regular-value congruence for every
virtual modular character. -/
theorem canonicalVirtualModularCartanProduct_regularValueCongruence_of_basis_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) [π c]₀ -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ x : R₀[IsLocalRing.ResidueField A](G),
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  let coord : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ) :=
    regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hcoord_repr :
      ∀ y : R₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        bR.repr y c = coord y c := by
    intro y c
    have hcoord_sum :
        coord y =
          ∑ j : PRegularConjClass G p,
            (bR.repr y j) •
              (Pi.single j (1 : ℤ) : PRegularConjClass G p → ℤ) := by
      calc
        coord y = coord (∑ j : PRegularConjClass G p, (bR.repr y j) • bR j) := by
          rw [bR.sum_repr]
        _ =
          ∑ j : PRegularConjClass G p, (bR.repr y j) • coord (bR j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [map_zsmul]
        _ =
          ∑ j : PRegularConjClass G p,
            (bR.repr y j) •
              (Pi.single j (1 : ℤ) : PRegularConjClass G p → ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine congrArg (fun z ↦ (bR.repr y j) • z) ?_
          simpa [coord, bR, simple_finiteRep_classes_basis_of_complete_family_apply] using
            hπ_coord j
    have hvalue := congrArg (fun f : PRegularConjClass G p → ℤ => f c) hcoord_sum
    simpa [Pi.smul_apply, Pi.single_apply] using hvalue.symm
  intro x
  have hx_expand :
      x =
        ∑ c : PRegularConjClass G p,
          (coord x c) • ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
    calc
      x = ∑ c : PRegularConjClass G p, (bR.repr x c) • bR c := by
        exact (bR.sum_repr x).symm
      _ =
        ∑ c : PRegularConjClass G p,
          (coord x c) • ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
        refine Finset.sum_congr rfl ?_
        intro c _hc
        rw [hcoord_repr x c]
        simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
  have hχ_expand :
      χ x =
        ∑ c : PRegularConjClass G p,
          (coord x c) • χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
    calc
      χ x =
        χ (∑ c : PRegularConjClass G p,
          (coord x c) • ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))) := by
          exact congrArg χ hx_expand
      _ =
        ∑ c : PRegularConjClass G p,
          χ ((coord x c) • ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))) := by
          rw [map_sum]
      _ =
        ∑ c : PRegularConjClass G p,
          (coord x c) • χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
          refine Finset.sum_congr rfl ?_
          intro c _hc
          rw [map_zsmul]
  have hcast_expand :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) (coord x) =
        ∑ c : PRegularConjClass G p,
          (coord x c) •
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    ext d
    simp [regularIntegerFunctionCast, Pi.single_apply]
  have hdiff :
      χ x - regularIntegerFunctionCast (p := p) (K := K) (G := G) (coord x) =
        ∑ c : PRegularConjClass G p,
          (coord x c) •
            (χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := by
    rw [hχ_expand, hcast_expand]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [zsmul_sub]
  rw [hdiff]
  refine Submodule.sum_mem D ?_
  intro c _hc
  exact D.toAddSubgroup.zsmul_mem (by simpa [D, χ] using hbasis c) (coord x c)

/-- The basis-vector source congruence closes the canonical source-product image comparison. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_basis_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) [π c]₀ -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  have hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) :=
    canonicalVirtualModularCartanProduct_forwardRepresentative_of_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)
      (canonicalVirtualModularCartanProduct_regularValueCongruence_of_basis_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis)
  have hsingle :
      ∀ c : PRegularConjClass G p,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
    intro c
    have hD :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      have hbase :
          χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
        simpa [χ] using hbasis c
      have hneg :=
        (regularValueDivisibilitySubmodule
          (p := p) (A := A) (K := K) (G := G)).neg_mem
          hbase
      simpa [χ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    have hS :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
      simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G), χ] using hD
    have hmem :
        regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          (cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)).range :=
      canonicalVirtualModularCartanProduct_single_mem_range_of_source_congruence
        (p := p) (A := A) (K := K) (G := G) c
        ⟨([π c]₀ : R₀[IsLocalRing.ResidueField A](G)), by simpa [χ] using hS⟩
    rcases hmem with ⟨q, hq⟩
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro x hq
    exact ⟨x, hq.symm⟩
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G)
      hforward
      (canonicalVirtualModularCartanProduct_reverseRepresentative_of_single
        (p := p) (A := A) (K := K) (G := G) hsingle)

/-- Coordinate-range endpoint from the basis-vector source congruence. -/
theorem existsCartanRangeCoordinateEquiv_of_basis_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) [π c]₀ -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_basis_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis)

end ProjectiveCartanSourceProductBasisImage

end Representation
