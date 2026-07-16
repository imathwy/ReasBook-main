import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceCokernelBridge
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageForward

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProductForward

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSourceProductForwardFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceProductForwardDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Coordinate formula for the canonical source product before choosing integer representatives.

The canonical source quotient is first identified with Serre's coordinatewise regular-value
divisibility quotient; after that identification, the `c`-coordinate is just the quotient class of
the descended virtual modular character value at `c`. -/
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_regularValueQuotient_mk
    (x : R₀[IsLocalRing.ResidueField A](G)) (c : PRegularConjClass G p) :
    cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        ((virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) c) := by
  rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply]
  unfold canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
  unfold virtualModularCartanRangeASpanQuotientLinearEquivPi
  rw [LinearEquiv.trans_apply]
  rw [Submodule.Quotient.equiv_apply]
  change
    regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        ((virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) c)
  exact regularValueDivisibilityQuotientLinearEquivPi_mk_apply
    (p := p) (A := A) (K := K) (G := G)
    (virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) c

/-- If the descended virtual modular character differs from the fixed integer coordinate function
by Serre's regular-value divisibility lattice, then the canonical source product has the desired
integer representative in every coordinate. -/
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_integerQuotientImageHom_of_regularValueDivisibilitySubmodule
    (x : R₀[IsLocalRing.ResidueField A](G))
    (hmem :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (c : PRegularConjClass G p) :
    cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
      integerQuotientImageHom
        (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)
        (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c) := by
  rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_regularValueQuotient_mk]
  rw [integerQuotientImageHom_apply]
  have hcoord :
      ∀ c' ∈ Set.univ,
        (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) c' ∈
          Submodule.span A
            ({algebraMap A K
              (ConjClasses.centralizerPPart p c'.1 : A)} : Set K) := by
    simpa [regularValueDivisibilitySubmodule] using hmem
  exact
    (Submodule.Quotient.eq
      (p := Submodule.span A
        ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))).2
      (by simpa [Pi.sub_apply, regularIntegerFunctionCast] using hcoord c (by simp))

/-- The exact remaining source-faithful forward gap for the fixed coordinate function.

For a fixed `x`, saying that every canonical source-product coordinate is represented by the
corresponding integer coordinate of `regularClassCoordinateAddEquiv x` is equivalent to the single
regular-value divisibility congruence between the descended virtual modular character and that
integer coordinate function. -/
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_mk_coordinate_integerQuotientImageHom_iff
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    (∀ c : PRegularConjClass G p,
      cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
        integerQuotientImageHom
          (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)
          (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c)) ↔
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hcoord
    have hpi :
        ∀ c : PRegularConjClass G p, c ∈ Set.univ →
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) c ∈
            Submodule.span A
              ({algebraMap A K
                (ConjClasses.centralizerPPart p c.1 : A)} : Set K) := by
      intro c _hc
      have hc := hcoord c
      rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_regularValueQuotient_mk,
        integerQuotientImageHom_apply] at hc
      exact
        (by
          have hdiff :=
            (Submodule.Quotient.eq
              (p := Submodule.span A
                ({algebraMap A K
                  (ConjClasses.centralizerPPart p c.1 : A)} : Set K))).1 hc
          simpa [Pi.sub_apply, regularIntegerFunctionCast] using hdiff)
    simpa [regularValueDivisibilitySubmodule] using hpi
  · intro hmem c
    exact
      cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_integerQuotientImageHom_of_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) x hmem c

/-- Forward representative adapter with the intended representative
`regularClassCoordinateAddEquiv x`. -/
theorem canonicalVirtualModularCartanProduct_coordinateIntegerRepresentatives_of_regularValueDivisibilitySubmodule
    (hmem :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ x : R₀[IsLocalRing.ResidueField A](G),
      ∃ g : PRegularConjClass G p → ℤ,
        g = regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∧
          ∀ c : PRegularConjClass G p,
            cartanCokernelToCanonicalVirtualModularCartanProduct
                (p := p) (A := A) (K := K) (G := G)
                (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
              integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c) := by
  intro x
  refine ⟨regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x, rfl, ?_⟩
  intro c
  exact
    cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply_eq_integerQuotientImageHom_of_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) x (hmem x) c

/-- Product-valued forward representative adapter obtained from the coordinatewise version. -/
theorem canonicalVirtualModularCartanProduct_forwardRepresentative_of_regularValueDivisibilitySubmodule
    (hmem :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ x : R₀[IsLocalRing.ResidueField A](G),
      ∃ g : PRegularConjClass G p → ℤ,
        cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
          regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  refine
    canonicalVirtualModularCartanProduct_forwardRepresentative_of_coordinateQuotients
      (p := p) (A := A) (K := K) (G := G) ?_
  intro x
  rcases
      canonicalVirtualModularCartanProduct_coordinateIntegerRepresentatives_of_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hmem x with
    ⟨g, _hg_eq, hg⟩
  exact ⟨g, hg⟩

end ProjectiveCartanSourceProductForward

end Representation
