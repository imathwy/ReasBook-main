import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageForward

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerImageReverse

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageReverseFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageReverseDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The reverse representative condition from
`ProjectiveCartanIntegerImageCriteria` follows from the exact reverse integrality statement:
every coordinatewise integer quotient class is represented by the inverse-Brauer transform of a
cast integer Cartan-coordinate function. -/
theorem concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerQuotient
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hquot :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          ∀ c : PRegularConjClass G p,
            integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c) =
              Submodule.Quotient.mk
                (p := Submodule.span A
                  ({algebraMap A K
                    (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
                (((projectiveCartanASpanBrauerReprLinearEquiv
                    (p := p) (A := A) (K := K) (G := G)
                    π hπ_simple hπ_coord).symm
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c)) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) := by
  intro g
  rcases hquot g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  ext c
  rw [regularIntegerDiagonalQuotientToIntegerImageProduct_mk]
  rw [concreteProjectiveCartanProduct_integerRepresentative_apply
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord f c]
  exact hf c

/-- Submodule form of the forward representative adapter.

Instead of working coordinate by coordinate in `K / dA`, it is enough to show that every inverse
Brauer transform of a cast integer function differs from a cast integer function by an element of
Serre's regular value-divisibility lattice. -/
theorem concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerSubmodule
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

/-- Submodule form of the reverse representative adapter. -/
theorem concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerSubmodule
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsub :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) := by
  refine
    concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerQuotient
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  intro g
  rcases hsub g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro c
  rw [integerQuotientImageHom_apply]
  change
    Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (g c : K) =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c)
  rw [Submodule.Quotient.eq]
  have hcoord :
      ∀ c' ∈ Set.univ,
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord).symm
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c' ∈
          Submodule.span A
            ({algebraMap A K
              (ConjClasses.centralizerPPart p c'.1 : A)} : Set K) := by
    simpa [regularValueDivisibilitySubmodule] using hf
  simpa [Pi.sub_apply, regularIntegerFunctionCast] using hcoord c (by simp)

/-- Combined concrete image-match adapter: the final product-image identification is reduced to
the two independent quotient-representability directions for inverse Brauer transport. -/
theorem concreteProjectiveCartanProductImageMatchesIntegerImage_of_brauerInverse_integerQuotients
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hforward :
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
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          ∀ c : PRegularConjClass G p,
            integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c) =
              Submodule.Quotient.mk
                (p := Submodule.span A
                  ({algebraMap A K
                    (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
                (((projectiveCartanASpanBrauerReprLinearEquiv
                    (p := p) (A := A) (K := K) (G := G)
                    π hπ_simple hπ_coord).symm
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) c)) :
    concreteProjectiveCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  exact
    concreteProjectiveCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerQuotient
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hforward)
      (concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerQuotient
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hreverse)

/-- Combined submodule-form adapter for the final product-image identification. -/
theorem concreteProjectiveCartanProductImageMatchesIntegerImage_of_brauerInverse_integerSubmodules
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hforward :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    concreteProjectiveCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  exact
    concreteProjectiveCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hforward)
      (concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hreverse)

end ProjectiveCartanIntegerImageReverse

end Representation
