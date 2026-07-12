import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerOrthogonalityCongruenceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassRowsReadbackSourceHelper
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerReadbackDivisibilitySourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterCongruenceSourceWorker

/-!
Direct orthogonality/source bridges for the fixed-coordinate Brauer readback residual.

The unconditional fixed-family statement
`coordinateNormalizedBrauerBasisPairingResidualDivisibility` is still not available from the
current source inputs alone.  This file keeps the frontier explicit: either the Serre
pairing-sum congruence itself, the point-mass regular-value row input, or the equivalent
projective-character lattice/source witness closes the A-side residual and fixed-coordinate
readback without using Cartan range, cokernel, product, or determinant endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerReadbackOrthogonalityDirectWorker

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

local instance brauerReadbackOrthogonalityDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReadbackOrthogonalityDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Explicit Serre `18.4`/orthogonality pairing sums close the coordinate-normalized A-side
pairing residual.

This is the smallest direct orthogonality frontier: after the two visible pairing sums are
identified by `<Φ_E, φ_E'> = δ_EE'` and Exercise `18.4`, no fixed-coordinate readback or Cartan
endpoint is used. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (orthogonalityPairingSumResidualCongruence_iff_coordinateNormalizedPairingResidual
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope).1 horth

/-- The same explicit orthogonality pairing-sum congruence closes the fixed-coordinate
Brauer-basis readback for the supplied coordinate-normalized family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_direct_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_orthogonalityPairingSum
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope horth)

/-- Direct point-mass regular-value row divisibility closes the coordinate-normalized A-side
pairing residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_pointMassRows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord hrows

/-- Direct point-mass regular-value row divisibility closes fixed-coordinate Brauer readback for
the same coordinate-normalized family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_direct_of_pointMassRows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_pointMassRowsInRegularValueSubmodule
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord hrows

/-- The local projective-character lattice congruence closes the coordinate-normalized A-side
pairing residual for any fixed coordinate-normalized family. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice_rows
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord hlattice

/-- The local projective-character lattice congruence closes fixed-coordinate Brauer readback
for any fixed coordinate-normalized family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_direct_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveCharacter_lattice_rows
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord hlattice

/-- The smaller point-mass projective-row source input implies the projective-character lattice
and hence closes the A-side pairing residual for any fixed coordinate-normalized family. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_pointMassProjectiveRows_source
    (hsource :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G))
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord
    ((projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G)).2 hsource)

/-- The explicit projective-restriction source witness closes the A-side pairing residual for
any fixed coordinate-normalized family. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_projectiveRestrictionWitness_source
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G))
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_direct_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitness_source
      (p := p) (A := A) (K := K) (G := G) hwitness)

end LocalBrauerReadbackOrthogonalityDirectWorker

section FullMixedBrauerReadbackOrthogonalityDirectWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReadbackOrthogonalityDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReadbackOrthogonalityDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model direct provider: the point-mass projective-row source input closes the
coordinate-normalized A-side pairing residual in every mixed model. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualDivisibility_direct_of_pointMassProjectiveRows_source
    (hsource :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisPairingResidualDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G)
      (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows_source
        (p := p) (k := k) (G := G) hsource)
      (A := A) (K := K) e0 π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model direct provider: explicit point-mass projective-restriction witnesses close
the coordinate-normalized A-side pairing residual in every mixed model. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualDivisibility_direct_of_projectiveRestrictionWitness_source
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisPairingResidualDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G)
      (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitnessBlocker_source
        (p := p) (k := k) (G := G) hwitness)
      (A := A) (K := K) e0 π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model visible readback provider from the point-mass projective-row source input.
This is the readback-facing form of the previous residual theorem. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackDivisibility_direct_of_pointMassProjectiveRows_source
    (hsource :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G)
      (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows_source
        (p := p) (k := k) (G := G) hsource)
      (A := A) (K := K) e0 π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model visible readback provider from explicit point-mass projective-restriction
witnesses. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackDivisibility_direct_of_projectiveRestrictionWitness_source
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G)
      (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitnessBlocker_source
        (p := p) (k := k) (G := G) hwitness)
      (A := A) (K := K) e0 π hπ_simple hπ_coord

end FullMixedBrauerReadbackOrthogonalityDirectWorker

end Representation
