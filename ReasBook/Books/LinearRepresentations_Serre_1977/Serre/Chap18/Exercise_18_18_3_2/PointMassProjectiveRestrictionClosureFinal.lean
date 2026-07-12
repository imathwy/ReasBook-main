import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassNontrivialResidualProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRestrictionClosureFinal

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

local instance pointMassProjectiveRestrictionClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRestrictionClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family version of the source bridge: the A-side pairing residual left by Exercise
`18.4` plus projective-envelope orthogonality is sufficient for the local point-mass
projective-restriction witness. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_fixedFamilyPairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) ?_
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassBasisResidualDivisibility_of_coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

/-- The same fixed-family residual supplies the row package used by
`RegularValueRowSourceFinal`. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_fixedFamilyPairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_fixedFamilyPairingResidual
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hresidual)

/-- Nontrivial-column pointwise residual form of the same bridge.  The
`centralizerPPart = 1` columns are filled by the existing pointwise Exercise `18.4` API. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_fixedFamilyNontrivialResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      ∀ c d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
          let hπ_pairwise :=
            pairwiseNonisomorphic_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_coord
          let hπ_complete :=
            complete_irreducible_family_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_simple hπ_coord
          let bA :=
            canonicalDVRBrauerBasis
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
          ∃ a : A,
            bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              (ConjClasses.centralizerPPart p d.1 : A) *
                (bA.repr
                  (primeToP_regular_indicator
                    (p := p) (A := A) (G := G)
                    (inversePRegularConjClass (p := p) d)) c) =
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_nontrivialResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) ?_
  exact ⟨π, hπ_simple, hπ_coord, hresidual⟩

/-- Existential pairing-residual closure for the local point-mass projective-restriction
witness.  This is the smallest existing existential wrapper around the residual isolated by the
source route. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_fixedFamilyPairingResidual
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hresidual

/-- Existential pairing-residual closure for the local point-mass projective row input. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G) hresidual)

/-- Universal pointwise residual closure for the local point-mass projective-restriction
witness. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_pointwiseResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulPointwiseResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_brauerBasisReadbackInput
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
      (p := p) (A := A) (G := G) hresidual)

/-- Universal pointwise residual closure for the local point-mass projective row input. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_pointwiseResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulPointwiseResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_pointwiseResidualProof
      (p := p) (A := A) (K := K) (G := G) hresidual)

end LocalPointMassProjectiveRestrictionClosureFinal

section FullMixedPointMassProjectiveRestrictionClosureFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRestrictionClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRestrictionClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model closure from the existential pairing-residual blocker to the point-mass
projective-restriction witness blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model closure from the existential pairing-residual blocker to the point-mass
projective row input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model closure from the universal pointwise residual blocker to the point-mass
projective-restriction witness blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_pointwiseResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_pointwiseResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model closure from the universal pointwise residual blocker to the point-mass
projective row input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_pointwiseResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_pointwiseResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

end FullMixedPointMassProjectiveRestrictionClosureFinal

end Representation
