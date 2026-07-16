import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRegularValueWitnessSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionClosureFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityInputSourceProofWorker

/-!
Source-side completion boundary for the point-mass projective-restriction witness.

This file does not use the Cartan range/cokernel/product/determinant endpoints and does not
derive the target from the projective-character lattice theorem.  It records that the requested
projective-restriction witness is exactly the same remaining source datum as the direct
regular-value point-mass rows, the Exercise `18.4` orthogonality residual input, and the pure
point-mass row congruence isolated by the source route.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRestrictionWitnessCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance pointMassProjectiveRestrictionWitnessCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRestrictionWitnessCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local exact source boundary: the requested projective-restriction witness is equivalent to
the direct point-mass regular-value row input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_pairingResidualSourceRows :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hwitness
    have hregular :
        regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
          (p := p) (A := A) (K := K) (G := G) :=
      existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) hwitness
    simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
      (existsPointMassRegularValueWitness_iff_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G)).1 hregular
  · intro hrows
    have hregular :
        regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
          (p := p) (A := A) (K := K) (G := G) :=
      (existsPointMassRegularValueWitness_iff_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G)).2
        (by
          simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
            hrows)
    exact
      existsPointMassProjectiveRestrictionWitness_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G) hregular

/-- Local exact source boundary against the explicit Exercise `18.4` / projective-envelope
orthogonality residual input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_orthogonalityInput :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hwitness
    have hrows :
        regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
          (p := p) (A := A) (K := K) (G := G) :=
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_pairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G)).1 hwitness
    exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsPairingResidualProof
        (p := p) (A := A) (K := K) (G := G)
        ((regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_sourceRows
          (p := p) (A := A) (K := K) (G := G)).2 hrows)
  · intro horth
    exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_existsPairingResidualProof
        (p := p) (A := A) (K := K) (G := G)
        (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
          (p := p) (A := A) (K := K) (G := G) horth)

/-- Local point-mass source congruence form of the same remaining witness. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_orthogonalityPointMassSourceBlocker :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_orthogonalityInput
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G))

/-- One-way local completion from the pure point-mass source blocker. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_orthogonalityPointMassSourceBlocker
    (hsource :
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_orthogonalityPointMassSourceBlocker
    (p := p) (A := A) (K := K) (G := G)).2 hsource

end LocalPointMassProjectiveRestrictionWitnessCompletionWorker

section FullMixedPointMassProjectiveRestrictionWitnessCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRestrictionWitnessCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRestrictionWitnessCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact source boundary: projective-restriction witnesses are equivalent to direct
point-mass regular-value rows. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hwitness
    exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G)
        (fullMixedModelPointMassRegularValueWitnessBlocker_of_projectiveRestrictionWitnessBlocker
          (p := p) (k := k) (G := G) hwitness)
  · intro hrows
    exact
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G)
        (fullMixedModelPointMassRegularValueWitnessBlocker_of_pointMassRowsInRegularValueSubmoduleInput
          (p := p) (k := k) (G := G) hrows)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact source boundary against the explicit Exercise `18.4` orthogonality
residual input. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_orthogonalityInput :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed point-mass source congruence form of the same projective-restriction witness. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_orthogonalityPointMassSourceBlocker :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_orthogonalityInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- One-way full mixed completion from the pure point-mass source blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_orthogonalityPointMassSourceBlocker
    (hsource :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_orthogonalityPointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

end FullMixedPointMassProjectiveRestrictionWitnessCompletionWorker

end Representation
