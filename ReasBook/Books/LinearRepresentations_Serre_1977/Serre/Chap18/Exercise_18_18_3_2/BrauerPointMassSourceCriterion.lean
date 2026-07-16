import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassSourceCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassSourceCriterionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassSourceCriterionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The coordinatewise divisibility statement exactly equivalent to the normalized point-mass
source congruence. This is the literal Serre 18.5(a) condition for the difference between the
Brauer row of `[π c]₀` and the corresponding regular-class point mass. -/
def brauerPointMassCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The normalized point-mass source congruence is exactly the coordinatewise divisibility
condition above. -/
theorem brauerPointMassSourceCongruence_iff_coordinateDivisibility
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
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hsource c d
    have hcoord :
        ∃ a : A,
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) d =
            algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) :=
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) _).1
        (by simpa [brauerPointMassSourceCongruence] using hsource c) d
    simpa [virtualModularCharacterOnPRegularConjClass_class] using hcoord
  · intro hcoord c
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) _).2 ?_
    intro d
    simpa [brauerPointMassCoordinateDivisibility,
      virtualModularCharacterOnPRegularConjClass_class] using hcoord c d

/-- The coordinatewise divisibility blocker closes the global regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_brauerPointMassCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcoord :
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruenceSourceFaithfulStatement_of_canonicalProductInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  exact
    (brauerPointMassCanonicalProductIdentity_iff_source_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2
      ((brauerPointMassSourceCongruence_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcoord)

end BrauerPointMassSourceCriterion

end Representation
