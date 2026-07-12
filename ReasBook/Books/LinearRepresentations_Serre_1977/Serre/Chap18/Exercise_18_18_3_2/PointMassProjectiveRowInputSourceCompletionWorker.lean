import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassExplicitRowsSourceCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionClosureFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRegularValueWitnessSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Serre18_5ASourceTextRouteWorker

/-!
Source-side completion boundary for the point-mass projective-row input.

This worker stays at the literal Serre `18.5(a)` level.  The support/value row package gives
projective-row representatives by applying the source criterion to each full residual class
function, and the existing reverse adapter shows this is exactly the same full mixed source
obligation as the point-mass source theorem isolated from Exercise `18.4` and projective-envelope
orthogonality.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRowInputSourceCompletionWorker

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

local instance pointMassProjectiveRowInputSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRowInputSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre support/value representatives close the local point-mass projective-row input.

For each residual row, Serre `18.5(a)` turns the full class-function representative, zero on the
`p`-singular locus and centralizer-`p`-part divisible on the regular locus, into a member of the
projective-character submodule.  Its regular restriction is the requested point-mass row. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_serreSupportValueRows
    (hsource :
      regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hsource⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases hsource c with ⟨Φ, hzero, hvalue, hres⟩
  refine Submodule.mem_map.2 ?_
  refine ⟨Φ, ?_, ?_⟩
  · exact
      mem_projectiveCharacterSubmodule_of_serre18_5a_rhs_of_enoughRoots
        (p := p) (A := A) (K := K) (G := G) hzero hvalue
  · simpa [regularRestrictionLinearMap, coordinateNormalizedPointMassExplicitResidualRow,
      virtualModularCharacterOnPRegularConjClass_class] using hres

/-- Local exact source boundary: point-mass projective rows are equivalent to the literal
support/value row package of Serre `18.5(a)`. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_iff_serreSupportValueRows :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_pointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueSourceCompletionPointMassProjectiveRowInput_of_serreSupportValueRows
        (p := p) (A := A) (K := K) (G := G)

end LocalPointMassProjectiveRowInputSourceCompletionWorker

section FullMixedPointMassProjectiveRowInputSourceCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRowInputSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRowInputSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed support/value representatives close the full mixed point-mass projective-row
input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_serreSupportValueSourceBlocker
    (hsource :
      fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_serreSupportValueRows
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact source boundary between the target row input and the literal Serre
support/value row package. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_serreSupportValueSourceBlocker :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_pointMassProjectiveRowInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_serreSupportValueSourceBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-text theorem isolated from Exercise `18.4` and the orthogonality relation closes
the requested full mixed point-mass projective-row input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_serre18_5ASourceTextTheorem
    (hsource :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have horth :
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) :=
    ((fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof
      (p := p) (k := k) (G := G)).1 hsource) (A := A) (K := K) e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
        (p := p) (A := A) (K := K) (G := G) horth)

omit [IsAlgClosed k] [CharP k p] in
/-- Strongest current source-side form: the requested full mixed point-mass projective-row input
is equivalent to the Serre `18.5(a)` source-text theorem at the point-mass boundary. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_serre18_5ASourceTextTheorem :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hrows
    have hwitness :
        fullMixedModelPointMassRegularValueWitnessBlocker
          (p := p) (k := k) (G := G) :=
      fullMixedModelPointMassRegularValueWitnessBlocker_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) hrows
    have hrow :
        fullMixedModelPointMassRowsInRegularValueSubmoduleInput
          (p := p) (k := k) (G := G) :=
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G) hwitness
    have horth :
        fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
          (p := p) (k := k) (G := G) :=
      (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
        (p := p) (k := k) (G := G)).1 hrow
    exact
      (fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof
        (p := p) (k := k) (G := G)).2 horth
  · exact
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_serre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)

end FullMixedPointMassProjectiveRowInputSourceCompletionWorker

end Representation
