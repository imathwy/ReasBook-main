import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassSourceCriterion

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassDivisibilityProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassDivisibilityProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassDivisibilityProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-facing witness for the point-mass divisibility condition: for each normalized Brauer
row, the difference from the corresponding integer point mass is the regular restriction of a
projective character. This is exactly the construction requested by Serre 18.5(a). -/
def brauerPointMassProjectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)

/-- A projective-character restriction witness gives the coordinatewise Serre 18.5(a)
divisibility condition for every point mass. -/
theorem brauerPointMassCoordinateDivisibility_of_projectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    ⟨Φ, hΦ, rfl⟩
  have hdiv :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    have hD :
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hmap
    simpa [hΦres] using hD
  exact
    by
      simpa [virtualModularCharacterOnPRegularConjClass_class] using
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G) _).1 hdiv d

/-- The same projective-restriction witness closes the existing global source-faithful endpoint.
-/
theorem regularValueCongruenceSourceFaithfulStatement_of_brauerPointMassProjectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulStatement_of_brauerPointMassCoordinateDivisibility
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (brauerPointMassCoordinateDivisibility_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness)

end BrauerPointMassDivisibilityProof

end Representation
