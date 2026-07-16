import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageCriteria

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerImageForward

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageForwardFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageForwardDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Applying the regular-divisibility product quotient to a representative is coordinatewise
quotienting by the corresponding centralizer-`p`-part ideal. -/
theorem regularValueDivisibilityQuotientLinearEquivPi_mk_apply
    (x : PRegularConjClass G p → K) (c : PRegularConjClass G p) :
    regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := regularValueDivisibilitySubmodule
            (p := p) (A := A) (K := K) (G := G)) x) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (x c) := by
  change
    (Submodule.quotientPi
        (fun c : PRegularConjClass G p =>
          Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)))
      (Submodule.Quotient.mk
        (p := Submodule.pi Set.univ fun c : PRegularConjClass G p =>
          Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        x) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (x c)
  rw [Submodule.quotientPi_apply]
  rw [Submodule.quotientPiLift_mk]
  rfl

/-- Source-faithful representative formula for the concrete Cartan product map.

An integer representative in the fixed Cartan-coordinate quotient is first cast to `K`, then
transported by the inverse Brauer-coordinate equivalence before taking the coordinatewise
quotients. Thus the remaining forward representative problem is exactly to show that these
inverse-Brauer coordinate classes have integer representatives. -/
theorem concreteProjectiveCartanProduct_integerRepresentative_apply
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (f : PRegularConjClass G p → ℤ) (c : PRegularConjClass G p) :
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (projectiveCartanCoordinateASpanQuotientLinearEquivPi
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (QuotientAddGroup.mk'
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c) := by
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A (PRegularConjClass G p → K) :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K))
  let T : (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hTD :
      Submodule.map
          (T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K)) D =
        S := by
    simpa [D, S, T, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hSD :
      Submodule.map
          (T.symm : (PRegularConjClass G p → K) →ₗ[A]
            (PRegularConjClass G p → K)) S =
        D :=
    (Submodule.map_symm_eq_iff T).mpr hTD
  have hmap :
      (Submodule.Quotient.equiv S D T.symm hSD)
          (Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) =
        Submodule.Quotient.mk (p := D)
          (T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
    rw [Submodule.Quotient.equiv_apply]
    exact Submodule.mapQ_apply S D
      (T.symm : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K))
      (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)
  change
    (projectiveCartanCoordinateASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      (cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f)) c =
      _
  rw [cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_mk]
  unfold projectiveCartanCoordinateASpanQuotientLinearEquivPi
  rw [LinearEquiv.trans_apply]
  rw [Submodule.Quotient.equiv_symm]
  change
    regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
      ((Submodule.Quotient.equiv S D T.symm hSD)
        (Submodule.Quotient.mk (p := S)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f))) c =
      _
  rw [hmap]
  exact regularValueDivisibilityQuotientLinearEquivPi_mk_apply
    (p := p) (A := A) (K := K) (G := G)
    (T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c

/-- The forward representative condition from
`ProjectiveCartanIntegerImageCriteria` follows from the exact missing integrality statement:
every inverse-Brauer transform of a cast integer function has the same product-quotient class as
some integer-valued regular-class function. -/
theorem concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerQuotient
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hquot :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          ∀ c : PRegularConjClass G p,
            Submodule.Quotient.mk
                (p := Submodule.span A
                  ({algebraMap A K
                    (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
                (((projectiveCartanASpanBrauerReprLinearEquiv
                    (p := p) (A := A) (K := K) (G := G)
                    π hπ_simple hπ_coord).symm
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c) =
              integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c)) :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  intro f
  rcases hquot f with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  ext c
  rw [concreteProjectiveCartanProduct_integerRepresentative_apply
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord f c]
  rw [regularIntegerDiagonalQuotientToIntegerImageProduct_mk]
  exact hg c

/-- Submodule form of the forward representative adapter.

Instead of proving coordinatewise equality in each quotient `K / dA`, it is enough to show that
every inverse-Brauer transform of a cast integer function differs from a cast integer function by
an element of Serre's regular value-divisibility lattice. -/
theorem concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_regularValueDivisibilitySubmodule
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsub :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  refine
    concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerQuotient
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  intro f
  rcases hsub f with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro c
  rw [integerQuotientImageHom_apply]
  change
    Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c) =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (g c : K)
  rw [Submodule.Quotient.eq]
  have hcoord :
      ∀ c' ∈ Set.univ,
        ((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g) c' ∈
          Submodule.span A
            ({algebraMap A K
              (ConjClasses.centralizerPPart p c'.1 : A)} : Set K) := by
    simpa [regularValueDivisibilitySubmodule] using hg
  simpa [Pi.sub_apply, regularIntegerFunctionCast] using hcoord c (by simp)

end ProjectiveCartanIntegerImageForward

end Representation
