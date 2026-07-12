import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PairingResidualDirectWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance pairingResidualDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pairingResidualDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side row input for the direct pairing-residual bridge.

For each coordinate-normalized Brauer row, the row minus the corresponding integral point mass
already lies in Serre's regular-value divisibility lattice.  This is the exact row form of the
Serre `18.5(a)` input used below; the bridge itself only subtracts the projective-envelope row
computed by Exercise `18.4` orthogonality. -/
def coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep k G) : Prop :=
  ∀ c : PRegularConjClass G p,
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The projective-character lattice representative congruence supplies the direct point-mass
row input.  This is just Serre `18.5(a)` rewritten through
`projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule`, specialized to
the coordinate-normalized simple rows. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  have hrowMap := hlattice ([π c]₀ : R₀[k](G))
  have hrowD :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hrowMap
  simpa [hπ_coord c, virtualModularCharacterOnPRegularConjClass_class] using hrowD

/-- Direct conditional bridge from the Serre `18.5(a)` row input to the pure `A`-valued
pairing residual.

The proof chooses projective envelopes for the fixed coordinate-normalized family, uses
Exercise `18.4` plus projective-envelope orthogonality to identify the row subtracted in the
pairing residual, and then descends the resulting fraction-field equality by injectivity of
`A → K`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
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
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  let row : PRegularConjClass G p → K :=
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) (π c)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) row).1
        (by simpa [row,
          coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule] using hrows c)
        d with
    ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  apply IsFractionRing.injective A K
  have hproj :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K (z * coeff) := by
    simpa [z, coeff, bA] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  have hfield :
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K
          (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            z * coeff) := by
    simpa [z, coeff, bA] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  change
    algebraMap A K
        (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff) =
      algebraMap A K (z * (a - coeff))
  calc
    algebraMap A K
        (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff)
        =
          (FDRep.modularCharacterOnPRegularConjClass
                (p := p) (G := G) (A := K) (π c)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
          rw [hfield]
    _ = algebraMap A K (z * a) - algebraMap A K (z * coeff) := by
          rw [show
            FDRep.modularCharacterOnPRegularConjClass
                  (p := p) (G := G) (A := K) (π c)
                  (PrimeToPRoot.toFieldLift
                    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
                regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
              row d by rfl]
          rw [ha, hproj]
    _ = algebraMap A K (z * (a - coeff)) := by
          rw [← map_sub, ← mul_sub]

/-- Direct source-side provider from the projective-character lattice congruence to the pure
`A`-valued pairing residual, routed through the point-mass row input above. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice_rows
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
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) π hπ_coord hlattice)

end PairingResidualDirectWorker

end Representation
