import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageForward
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceCokernelBridge

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanProductImageUnconditionalWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanProductImageUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanProductImageUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Unconditional forward image inclusion from the concrete coordinate-normalized projective
Cartan product image to the canonical source-product image.

This uses only the definition-level identification of those two images and does not assume any
point-mass Brauer character value congruence. -/
theorem concreteProjectiveCartanProduct_range_le_canonicalVirtualModularCartanProduct_range
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (projectiveCartanCoordinateASpanQuotientLinearEquivPi
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)).range ≤
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range := by
  rintro y ⟨q, rfl⟩
  refine QuotientAddGroup.induction_on q ?_
  intro f
  let x : R₀[IsLocalRing.ResidueField A](G) :=
    (regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).symm f
  refine ⟨QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x, ?_⟩
  have hxcoord :
      regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x = f := by
    simp [x]
  have hcalc :
      cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (projectiveCartanCoordinateASpanQuotientLinearEquivPi
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (QuotientAddGroup.mk'
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
        cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
    ext c
    rw [concreteProjectiveCartanProduct_integerRepresentative_apply
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord f c]
    rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply
      (p := p) (A := A) (K := K) (G := G) x c]
    let χ : PRegularConjClass G p → K :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x
    let T : (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
      projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hT :
        T χ = regularIntegerFunctionCast (p := p) (K := K) (G := G) f := by
      simpa [T, χ, hxcoord, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
        projectiveCartanASpanBrauerRepr_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x
    have hsymm :
        T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) = χ := by
      rw [← hT]
      simp [T]
    have hcanonical :
        canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
            (p := p) (A := A) (K := K) (G := G)
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G)) χ) c =
          Submodule.Quotient.mk
            (p := Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
            (χ c) := by
      unfold canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
      unfold virtualModularCartanRangeASpanQuotientLinearEquivPi
      rw [LinearEquiv.trans_apply]
      rw [Submodule.Quotient.equiv_apply]
      change
        regularValueDivisibilityQuotientLinearEquivPi
            (p := p) (A := A) (K := K) (G := G)
            (Submodule.Quotient.mk
              (p := regularValueDivisibilitySubmodule
                (p := p) (A := A) (K := K) (G := G)) χ) c =
          Submodule.Quotient.mk
            (p := Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
            (χ c)
      rw [regularValueDivisibilityQuotientLinearEquivPi_mk_apply]
    rw [hcanonical]
    change
      Submodule.Quotient.mk
          (p := Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
          (T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) c) =
        Submodule.Quotient.mk
          (p := Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
          (χ c)
    rw [hsymm]
  exact hcalc.symm

end ProjectiveCartanProductImageUnconditionalWorker

end Representation
