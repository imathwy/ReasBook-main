import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassRowsReadbackSourceHelper
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassRegularValueWitnessSourceWorker

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

local instance pointMassRegularValueWitnessSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassRegularValueWitnessSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/- The direct fixed-family row-submodule input from `PairingResidualDirectWorker` is exactly the
regular-value point-mass witness from `BrauerPointMassCoordinateProof`, after rewriting the
single-representation modular character as the virtual modular character of `[π c]₀`.

This is the smallest non-Cartan bridge for the A-side row route: it only changes notation for
Serre `18.5(a)`'s row divisibility condition. -/
omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
theorem brauerPointMassRegularValueDivisibilityWitness_iff_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · intro hwitness c
    simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
      virtualModularCharacterOnPRegularConjClass_class] using hwitness c
  · intro hrows c
    simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
      virtualModularCharacterOnPRegularConjClass_class] using hrows c

/- Direct row-submodule input gives the local existential regular-value point-mass witness. -/
omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
theorem existsPointMassRegularValueWitness_of_pointMassRowsInRegularValueSubmodule
    (hrows :
      ∃ π : PRegularConjClass G p → FDRep kA G,
        ∃ _hπ_simple : ∀ c, Simple (π c),
          ∃ _hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
              (p := p) (A := A) (K := K) (G := G) π) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  exact
    ⟨π, hπ_simple, hπ_coord,
      (brauerPointMassRegularValueDivisibilityWitness_iff_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hrows⟩

/- The local regular-value witness is equivalent to the direct fixed-family row-submodule input.
No projective Cartan range, cokernel, or product endpoint is used. -/
omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
theorem existsPointMassRegularValueWitness_iff_pointMassRowsInRegularValueSubmodule :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      ∃ π : PRegularConjClass G p → FDRep kA G,
        ∃ _hπ_simple : ∀ c, Simple (π c),
          ∃ _hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
              (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, hwitness⟩
    exact
      ⟨π, hπ_simple, hπ_coord,
        (brauerPointMassRegularValueDivisibilityWitness_iff_pointMassRowsInRegularValueSubmodule
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hwitness⟩
  · exact
      existsPointMassRegularValueWitness_of_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G)

/-- A point-mass projective-row input also gives the A-side regular-value witness, by Serre
`18.5(a)` in the already formalized projective-restriction equivalence. -/
theorem existsPointMassRegularValueWitness_of_pointMassProjectiveRowInput
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) :=
  existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (projectiveRestrictionWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) hrows)

end LocalPointMassRegularValueWitnessSourceWorker

section FullMixedPointMassRegularValueWitnessSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassRegularValueWitnessSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassRegularValueWitnessSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model bridge from the direct row-submodule input to the requested A-side
regular-value witness blocker.  This is the strict row-divisibility source form of Serre
`18.5(a)`. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_of_pointMassRowsInRegularValueSubmoduleInput
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRegularValueWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassRegularValueWitness_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The requested full mixed regular-value witness blocker gives back the direct row-submodule
input, so the remaining gap can be stated without projective rows or readback notation. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_regularValueWitnessBlocker
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hwitness (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hwitness⟩
  exact
    ⟨π, hπ_simple, hπ_coord,
      (brauerPointMassRegularValueDivisibilityWitness_iff_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hwitness⟩

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model equivalence between the requested A-side witness and the direct row
submodule input. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput :
    fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassRegularValueWitnessBlocker_of_pointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-row input from `RegularValueRowSourceFinal` is also sufficient for the
requested A-side regular-value witness blocker. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_of_regularValueSourceCompletionPointMassProjectiveRowInput
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRegularValueWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassRegularValueWitness_of_pointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Combining the new reverse bridge with the existing provider in `RegularValueRowSourceFinal`
records the exact non-Cartan equivalence between regular-value row divisibility and projective
point-mass rows. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_iff_regularValueSourceCompletionPointMassProjectiveRowInput :
    fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassRegularValueWitnessBlocker_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)

end FullMixedPointMassRegularValueWitnessSourceWorker

end Representation
