import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibilityEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerReprPointMassEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularValueCongruenceSourceFaithful

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance regularValueCongruenceSourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueCongruenceSourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The global regular-value congruence for the canonical source-product route. -/
def regularValueCongruenceSourceFaithfulStatement : Prop :=
  ∀ x : R₀[IsLocalRing.ResidueField A](G),
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- Inverse-Brauer congruence on all integer regular-class coordinate functions. -/
def regularValueCongruenceSourceFaithfulBrauerInverseInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ f : PRegularConjClass G p → ℤ,
    (projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- Exact adapter from the already-proved endpoint: the global congruence is the same as the
inverse-Brauer congruence for any fixed coordinate-normalized Brauer family. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_brauerInverseInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerInverseInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  exact
    virtualModularCharacter_integerCoordinate_congruence_iff_brauerInverse_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Existential all-coordinate inverse-Brauer input. The normalized family is available from the
local Brauer-coordinate API; the remaining content is the congruence itself. -/
def regularValueCongruenceSourceFaithfulExistsBrauerInverseInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        regularValueCongruenceSourceFaithfulBrauerInverseInput
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Global regular-value congruence is equivalent to the existence of one normalized family
satisfying the all-coordinate inverse-Brauer congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerInverseInput :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsBrauerInverseInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hglobal
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerInverseInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hglobal
  · rintro ⟨π, hπ_simple, hπ_coord, hbrauer⟩
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerInverseInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hbrauer

/-- Point-mass inverse-Brauer congruence. This is the smallest basis-vector congruence used by
the current source-product route. -/
def regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    (projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The point-mass inverse-Brauer congruences imply the global regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_brauerInversePointMassInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruence_of_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  intro c
  exact
    (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2
      (hbasis c)

/-- Existential point-mass inverse-Brauer input. This is the minimal remaining statement after
the finite-basis reduction. -/
def regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The global target is equivalent to proving the point-mass inverse-Brauer congruence for one
coordinate-normalized Brauer family. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerInversePointMassInput :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hglobal
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hbrauer :
        regularValueCongruenceSourceFaithfulBrauerInverseInput
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerInverseInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hglobal
    intro c
    exact hbrauer (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  · rintro ⟨π, hπ_simple, hπ_coord, hbasis⟩
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis

/-- Cartan-span point-mass input for the Brauer-coordinate map itself. -/
def regularValueCongruenceSourceFaithfulPointMassCartanSpanInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
      (projectiveCartanASpanBrauerReprLinearEquiv
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))

/-- The Cartan-span point-mass input closes the global regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_pointMassCartanSpanInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcartan :
      regularValueCongruenceSourceFaithfulPointMassCartanSpanInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruence_of_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  exact
    (brauerPointMassSourceCongruence_iff_brauerRepr_pointMass_cartanSpan_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcartan

/-- Source-product point-mass identity. This is the source-faithful product-side version of the
same remaining basis-vector input. -/
def regularValueCongruenceSourceFaithfulCanonicalProductInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  brauerPointMassCanonicalProductIdentity
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The source-product point-mass identity implies the global regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_canonicalProductInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hprod :
      regularValueCongruenceSourceFaithfulCanonicalProductInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruence_of_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  exact
    (brauerPointMassCanonicalProductIdentity_iff_source_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hprod

/-- The fixed-coordinate quotient identity for point masses implies the global regular-value
congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_pointMassQuotientIdentity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hquot :
      brauerReprPointMassQuotientIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) := by
  have hprod :
      regularValueCongruenceSourceFaithfulCanonicalProductInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
    (brauerReprPointMassQuotientIdentity_iff_canonicalProductIdentity
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hquot
  exact
    regularValueCongruenceSourceFaithfulStatement_of_canonicalProductInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hprod

end RegularValueCongruenceSourceFaithful

end Representation
