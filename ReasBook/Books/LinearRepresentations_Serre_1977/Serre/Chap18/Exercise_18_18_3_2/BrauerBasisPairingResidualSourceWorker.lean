import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.OrthogonalityResidualMicroWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PairingResidualDirectWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerBasisPairingResidualSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance brauerBasisPairingResidualSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisPairingResidualSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Existential source-row input for the pairing residual route.

For one coordinate-normalized complete simple family, each point-mass row difference already
lies in Serre's regular-value divisibility lattice.  This is the row-level form supplied by the
projective-character lattice before Exercise `18.4` orthogonality subtracts the visible
projective-envelope row. -/
def regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
          (p := p) (A := A) (K := K) (G := G) π

/-- The source-row input is enough for the named existential A-valued pairing residual.

The bridge is exactly the fixed-family direct worker: choose projective envelopes, use
Exercise `18.4` and projective-envelope orthogonality for the subtracted row, then descend by
fraction-field injectivity. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_sourceRows
    (hrows :
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
      (p := p) (A := A) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hrows

/-- The projective-character lattice supplies the existential source rows by specializing to a
coordinate-normalized complete family. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  have hrowMap := hlattice ([π c]₀ : R₀[kA](G))
  have hrowD :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[kA](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G))) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hrowMap
  simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
    hπ_coord c, virtualModularCharacterOnPRegularConjClass_class] using hrowD

/-- Source-side provider from Serre's projective-character lattice congruence to the named
existential pairing residual.

This uses the overall projective-character row divisibility and the direct Exercise `18.4`
orthogonality bridge; it does not pass through Cartan range, cokernel, or product endpoints. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_sourceRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

/-- Source-side orthogonality input for the existential pairing-residual route.

This is the explicit Serre `18.4`/projective-envelope pairing-sum congruence for one
coordinate-normalized complete Brauer family.  It is kept separate from the readback endpoint:
the bridge below sends it directly to the pairing residual. -/
def regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
          ∃ _hP_envelope :
            ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope,
            let hπ_pairwise :=
              pairwiseNonisomorphic_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_coord
            let hπ_complete :=
              complete_irreducible_family_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_simple hπ_coord
            orthogonalityPairingSumResidualCongruence
              (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P

/-- The explicit orthogonality pairing-sum congruence closes the named existential pairing
residual directly.

The proof uses only the micro bridge
`coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence`;
it does not pass through the fixed-coordinate readback equivalence or any Cartan
range/cokernel/product endpoint. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
    (horth :
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
      (p := p) (A := A) (G := G) := by
  classical
  rcases horth with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hcongr⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  have hpoint :=
    coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hcongr
  simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility, canonicalDVRBrauerBasis]
    using hpoint

end LocalBrauerBasisPairingResidualSourceWorker

section FullMixedBrauerBasisPairingResidualSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisPairingResidualSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisPairingResidualSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from the projective-character lattice congruence to the
existential pairing-residual blocker. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic orthogonality input for the existential pairing-residual route. -/
def fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from the explicit source-side orthogonality congruence
to the existential pairing-residual blocker. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
      (p := p) (A := A) (K := K) (G := G)
      (horth (A := A) (K := K) e0)

end FullMixedBrauerBasisPairingResidualSourceWorker

end Representation
