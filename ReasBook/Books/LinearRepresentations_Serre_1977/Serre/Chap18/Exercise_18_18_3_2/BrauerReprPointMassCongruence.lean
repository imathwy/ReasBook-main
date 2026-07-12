import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductBasisCongruence

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprPointMassCongruence

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerReprPointMassCongruenceFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprPointMassCongruenceDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The source-side basis congruence for the normalized Brauer family. -/
def brauerPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The quotient identity which is exactly the requested fixed-coordinate point-mass congruence.
-/
def brauerReprPointMassQuotientIdentity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let E := PRegularConjClass G p → K
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  ∀ c : PRegularConjClass G p,
    Submodule.Quotient.mk (p := S)
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
      Submodule.Quotient.mk (p := S)
        (T
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)))

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The Cartan-span point-mass congruence is equivalent to equality in the Cartan-span quotient.
-/
theorem brauerRepr_pointMass_cartanSpan_congruence_iff_quotient_identity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ↔
      brauerReprPointMassQuotientIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  let E := PRegularConjClass G p → K
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  constructor
  · intro h c
    have hc :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          T
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈ S := by
      simpa [S, T, E] using h c
    exact (Submodule.Quotient.eq S).2 hc
  · intro h c
    have hq :
        Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
          Submodule.Quotient.mk (p := S)
            (T
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))) := by
      simpa [brauerReprPointMassQuotientIdentity, S, T, E] using h c
    simpa [S, T, E] using (Submodule.Quotient.eq S).1 hq

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The quotient identity closes the requested point-mass congruence. -/
theorem brauerRepr_pointMass_cartanSpan_congruence_of_quotient_identity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hquot :
      brauerReprPointMassQuotientIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) :=
  (brauerRepr_pointMass_cartanSpan_congruence_iff_quotient_identity
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hquot

/-- The existing reductions turn the source-side basis congruence into the requested
Cartan-span point-mass congruence. -/
theorem brauerRepr_pointMass_cartanSpan_congruence_of_source_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) := by
  intro c
  have hinv :
      (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    exact
      (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).1
        (by simpa [brauerPointMassSourceCongruence] using hsource c)
  exact
    (brauerInverse_single_congruence_iff_brauerRepr_single_cartanSpan_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).1 hinv

/-- Source-side and fixed-coordinate point-mass congruences are equivalent. -/
theorem brauerPointMassSourceCongruence_iff_brauerRepr_pointMass_cartanSpan_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      ∀ c : PRegularConjClass G p,
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) := by
  constructor
  · exact
      brauerRepr_pointMass_cartanSpan_congruence_of_source_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · intro hcartan c
    have hinv :
        (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
      (brauerInverse_single_congruence_iff_brauerRepr_single_cartanSpan_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2 (hcartan c)
    exact
      (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2 hinv

end BrauerReprPointMassCongruence

end Representation
