import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRowsWorker

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

local instance pointMassProjectiveRowsWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRowsWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Worker-C source-side residual witness closest to Serre's orthogonality route.

For one coordinate-normalized Brauer family, the residual left after subtracting the visible
projective-envelope row supplied by Exercise `18.4` and projective-envelope orthogonality is
centralizer-`p`-part divisible. -/
def workerCPointMassProjectiveRowsPairingResidualWitness : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The pure `A`-basis residual is already enough to construct the point-mass projective-row
input.  This factors through the explicit projective-restriction witness, not through any
Cartan range, cokernel, or product endpoint. -/
theorem workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_basisResidual
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) hbasis)

/-- Fixed-family pairing residual provider for the requested point-mass projective-row input. -/
theorem workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_fixedFamilyPairingResidual
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
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_basisResidual
      (p := p) (A := A) (K := K) (G := G) ?_
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassBasisResidualDivisibility_of_coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

/-- Existential pairing-residual provider for the requested point-mass projective-row input. -/
theorem workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_pairingResidualWitness
    (hresidual :
      workerCPointMassProjectiveRowsPairingResidualWitness
        (p := p) (A := A) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  exact
    workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_fixedFamilyPairingResidual
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hresidual

/-- The row input also recovers the same pairing-residual witness, so this worker file records
the exact remaining source-side datum in Serre's orthogonality notation. -/
theorem workerC_pairingResidualWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    workerCPointMassProjectiveRowsPairingResidualWitness
      (p := p) (A := A) (G := G) := by
  have hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) :=
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G) hrows
  rcases
      existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G) hread with
    ⟨π, hπ_simple, hπ_coord, hbasis⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_brauerPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hbasis

/-- Local equivalence between the requested row input and the pairing residual isolated by the
point-mass projective-row route. -/
theorem workerC_regularValueSourceCompletionPointMassProjectiveRowInput_iff_pairingResidualWitness :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      workerCPointMassProjectiveRowsPairingResidualWitness
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      workerC_pairingResidualWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_pairingResidualWitness
        (p := p) (A := A) (K := K) (G := G)

end LocalPointMassProjectiveRowsWorker

section FullMixedPointMassProjectiveRowsWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRowsWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRowsWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic version of the Worker-C pairing-residual witness. -/
def workerCFullMixedPointMassProjectiveRowsPairingResidualWitness : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      workerCPointMassProjectiveRowsPairingResidualWitness
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed pure basis-residual blockers produce the requested full mixed row input. -/
theorem workerC_fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_basisResidualBlocker
    (hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_basisResidual
      (p := p) (A := A) (K := K) (G := G)
      (hbasis (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed pairing-residual witness provider for the requested full mixed row input. -/
theorem workerC_fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_pairingResidualWitness
    (hresidual :
      workerCFullMixedPointMassProjectiveRowsPairingResidualWitness
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    workerC_regularValueSourceCompletionPointMassProjectiveRowInput_of_pairingResidualWitness
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed row input recovers the Worker-C full mixed pairing-residual witness. -/
theorem workerC_fullMixedPointMassProjectiveRowsPairingResidualWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    workerCFullMixedPointMassProjectiveRowsPairingResidualWitness
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    workerC_pairingResidualWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed equivalence between the requested row input and the Worker-C source residual
witness. -/
theorem workerC_fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_pairingResidualWitness :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      workerCFullMixedPointMassProjectiveRowsPairingResidualWitness
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      workerC_fullMixedPointMassProjectiveRowsPairingResidualWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)
  · exact
      workerC_fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_pairingResidualWitness
        (p := p) (k := k) (G := G)

end FullMixedPointMassProjectiveRowsWorker

end Representation
