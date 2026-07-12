import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceCokernelBridge
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageForward

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProductReverse

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveCartanSourceProductReverseFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceProductReverseDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The canonical source-product equivalence sends the quotient class of a cast integer regular
class function to its coordinatewise integer image.

This is the reverse-side analogue of the coordinate formula needed to compare the canonical
source product map with `regularIntegerDiagonalQuotientToIntegerImageProduct`. -/
theorem canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_regularIntegerFunctionCast
    (f : PRegularConjClass G p → ℤ) :
    canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) =
      regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) := by
  ext c
  unfold canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
  unfold virtualModularCartanRangeASpanQuotientLinearEquivPi
  rw [LinearEquiv.trans_apply]
  rw [Submodule.Quotient.equiv_apply]
  change
    regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := regularValueDivisibilitySubmodule
            (p := p) (A := A) (K := K) (G := G))
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c =
      regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) c
  rw [regularValueDivisibilityQuotientLinearEquivPi_mk_apply]
  unfold regularIntegerDiagonalQuotientToIntegerImageProduct
  change
    Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        ((regularIntegerFunctionCast (p := p) (K := K) (G := G) f) c) =
      integerQuotientImageHom
        (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c)
  rw [integerQuotientImageHom_apply]
  simp [regularIntegerFunctionCast, integerQuotientImageSubmodule]

/-- Exact source-congruence criterion for an integer regular-class function to lie in the range of
the canonical source product map.

The remaining reverse point-mass task is therefore precisely the source-faithful congruence on the
right: find an integral virtual modular character whose regular values agree with the requested
integer function modulo Serre's canonical divisibility lattice. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProduct_mem_canonicalVirtualModularCartanProduct_range_iff_source_congruence
    (f : PRegularConjClass G p → ℤ) :
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) ∈
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range ↔
      ∃ x : R₀[k](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hmem
    rcases hmem with ⟨q, hq⟩
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro x hq
    refine ⟨x, ?_⟩
    let E :=
      canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
    have hprod :
        E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) =
          E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
      calc
        E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x))
            =
          cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom k G).range x) := by
              exact (cartanCokernelToCanonicalVirtualModularCartanProduct_mk
                (p := p) (A := A) (K := K) (G := G) x).symm
        _ =
          regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) := hq
        _ =
          E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
              exact
                (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_regularIntegerFunctionCast
                  (p := p) (A := A) (K := K) (G := G) f).symm
    have hquot :=
      E.injective hprod
    have hquot' :
        Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) =
          Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) :=
      hquot.symm
    exact (Submodule.Quotient.eq
      (canonicalVirtualModularCartanRangeASpan
        (p := p) (A := A) (K := K) (G := G))).mp hquot'
  · rintro ⟨x, hx⟩
    refine ⟨QuotientAddGroup.mk' (cartanHom k G).range x, ?_⟩
    let E :=
      canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
    have hquot :
        Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) =
          Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) := by
      exact (Submodule.Quotient.eq
        (canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))).mpr hx
    calc
      cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk' (cartanHom k G).range x) =
        E
          (Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) := by
            exact cartanCokernelToCanonicalVirtualModularCartanProduct_mk
              (p := p) (A := A) (K := K) (G := G) x
      _ =
        E
          (Submodule.Quotient.mk
            (p := canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
            rw [← hquot]
      _ =
        regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk'
            (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) := by
            exact
              canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_regularIntegerFunctionCast
                (p := p) (A := A) (K := K) (G := G) f

/-- Representative form of the reverse source-congruence criterion. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
    (f : PRegularConjClass G p → ℤ) (x : R₀[k](G))
    (hx :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f -
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
          canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G)) :
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) =
      cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom k G).range x) := by
  let E :=
    canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G)
  have hquot :
      Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) =
        Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) := by
    exact (Submodule.Quotient.eq
      (canonicalVirtualModularCartanRangeASpan
        (p := p) (A := A) (K := K) (G := G))).mpr hx
  calc
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) =
      E
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
        exact
          (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_regularIntegerFunctionCast
            (p := p) (A := A) (K := K) (G := G) f).symm
    _ =
      E
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) := by
        rw [hquot]
    _ =
      cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom k G).range x) := by
        exact (cartanCokernelToCanonicalVirtualModularCartanProduct_mk
          (p := p) (A := A) (K := K) (G := G) x).symm

/-- Point-mass specialization of the reverse source-congruence criterion. -/
theorem canonicalVirtualModularCartanProduct_single_mem_range_iff_source_congruence
    (c : PRegularConjClass G p) :
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range ↔
      ∃ x : R₀[k](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) :=
  regularIntegerDiagonalQuotientToIntegerImageProduct_mem_canonicalVirtualModularCartanProduct_range_iff_source_congruence
    (p := p) (A := A) (K := K) (G := G)
    (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)

/-- Usable one-way form: a source congruence for the integer point mass gives the requested range
membership in the canonical source product. -/
theorem canonicalVirtualModularCartanProduct_single_mem_range_of_source_congruence
    (c : PRegularConjClass G p)
    (hsource :
      ∃ x : R₀[k](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G)) :
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range :=
  (canonicalVirtualModularCartanProduct_single_mem_range_iff_source_congruence
    (p := p) (A := A) (K := K) (G := G) c).2 hsource

/-- Representative form of the point-mass reverse criterion. -/
theorem canonicalVirtualModularCartanProduct_single_reverseRepresentative_of_source_congruence
    (c : PRegularConjClass G p)
    (hsource :
      ∃ x : R₀[k](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G)) :
    ∃ x : R₀[k](G),
      regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk'
            (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
        cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk' (cartanHom k G).range x) := by
  rcases hsource with ⟨x, hx⟩
  exact
    ⟨x,
      regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
        (p := p) (A := A) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) x hx⟩

end ProjectiveCartanSourceProductReverse

end Representation
