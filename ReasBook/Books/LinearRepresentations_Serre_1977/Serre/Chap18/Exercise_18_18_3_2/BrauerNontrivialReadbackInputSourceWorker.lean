import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackInputCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerNontrivialCentralizerRowCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCharacterPointwiseSourceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Serre18_5ASourceTextRouteWorker

/-!
Source-side bridges for the nontrivial Brauer-character readback input.

This worker keeps the remaining statement on the Serre `18.5(a)` source side.  It does not
invoke Cartan range, cokernel, Smith/product, determinant, or endpoint theorems.  The strongest
unconditional progress available here is to identify the requested local/full nontrivial-column
input with the already isolated full-row Brauer-character source theorem; the residual blocker is
the actual Brauer-character row congruence on the nontrivial centralizer-`p`-part columns.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalNontrivialReadbackInputSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerNontrivialReadbackInputSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerNontrivialReadbackInputSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The local pointwise readback package is equivalent to the nontrivial-column
Brauer-character readback input.  The columns with centralizer `p`-part equal to `1` are
absorbed by `brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial`. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_iff_brauerCharacterNontrivialReadbackInput :
    regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource
    rcases hsource with ⟨π, hπ_simple, hπ_coord, hpoint⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hrow :
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hpoint
    exact
      (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
        (p := p) (A := A) (G := G) π).1 hrow
  · intro hnontrivial
    rcases hnontrivial with ⟨π, hπ_simple, hπ_coord, hrow_nontrivial⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hrow :
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
        (p := p) (A := A) (G := G) π).2 hrow_nontrivial
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hrow

/-- Forward adapter from the already isolated pointwise source package to the requested local
nontrivial-column input. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_pointwiseReadbackSource
    (hsource :
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_iff_brauerCharacterNontrivialReadbackInput
    (p := p) (A := A) (G := G)).1 hsource

/-- Conversely, the local nontrivial-column input recovers the pointwise source package because
the omitted `centralizerPPart = 1` columns are automatic. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_brauerCharacterNontrivialReadbackInput_source
    (hnontrivial :
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_iff_brauerCharacterNontrivialReadbackInput
    (p := p) (A := A) (G := G)).2 hnontrivial

/-- A global source API for every coordinate-normalized Brauer row closes the local
nontrivial-column existential input. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_pointwiseReadbackSource
    (p := p) (A := A) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_brauerCharacterPointwiseSourceAPI
      (p := p) (A := A) (G := G) hapi)

/-- Minimal local blocker form: it is enough to prove the A-valued nontrivial-column row
congruence for every coordinate-normalized Brauer family. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_nontrivialPointwiseReadbackCongruenceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases
      (exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (G := G) :
        ∃ π : PRegularConjClass G p → FDRep k G,
          (∀ c, Simple (π c)) ∧
            (∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
            PairwiseNonisomorphic π ∧
            IsCompleteIrreducibleFamily π ∧
            ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
              ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  simpa [fixedCoordinateBrauerCharacterNontrivialReadbackCongruence,
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence] using
    hapi π hπ_simple hπ_coord

/-- The Serre `18.5(a)` point-mass source theorem closes the local nontrivial-column
Brauer-character input.  This is only a source-side transport through the existing
Exercise `18.4`/orthogonality row equivalence. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_serre18_5aSourceTextPointMassReadbackTheorem
    (hsource :
      serre18_5aSourceTextPointMassReadbackTheorem
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_pointwiseReadbackSource
    (p := p) (A := A) (G := G)
    ((serre18_5aSourceTextPointMassReadbackTheorem_iff_pointwiseReadbackSource
      (p := p) (A := A) (G := G)).1 hsource)

end LocalNontrivialReadbackInputSourceWorker

section LocalFieldRowNontrivialReadbackInputSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerNontrivialFieldReadbackInputSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerNontrivialFieldReadbackInputSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- K-valued version of the local nontrivial-column input.  It is the same source row after
applying the canonical fraction-field lift of prime-to-`p` roots. -/
def regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
          (p := p) (A := A) (K := K) (G := G) π

/-- The K-valued source row package descends to the requested A-valued nontrivial-column input. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_fieldRowInput
    (hfield :
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hfield with ⟨π, hπ_simple, hπ_coord, hrow_field⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  have hrow :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π :=
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_of_fieldRowSource
      (p := p) (A := A) (K := K) (G := G) π hrow_field
  simpa [fixedCoordinateBrauerCharacterNontrivialReadbackCongruence,
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence] using hrow

/-- The A-valued nontrivial-column input maps to the K-valued source row package. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput_of_readbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hrow_readback⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  have hrow :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
    simpa [fixedCoordinateBrauerCharacterNontrivialReadbackCongruence,
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence] using hrow_readback
  exact
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSource_of_pointwiseReadbackCongruence
      (p := p) (A := A) (K := K) (G := G) π hrow

/-- Exact local boundary: the requested A-valued input is equivalent to the K-valued source row
package. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_iff_fieldRowInput :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialFieldRowInput_of_readbackInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_fieldRowInput
        (p := p) (A := A) (K := K) (G := G)

end LocalFieldRowNontrivialReadbackInputSourceWorker

section FullMixedNontrivialReadbackInputSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerNontrivialReadbackInputSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerNontrivialReadbackInputSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed boundary: the full-row direct Brauer-character congruence is equivalent to the
nontrivial-column readback input. -/
theorem fullMixedModelBrauerCharacterPointwiseReadbackCongruence_iff_nontrivialReadbackInput :
    fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hpoint A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hpoint (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hrow⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
        (p := p) (A := A) (G := G) π).1 hrow
  · intro hnontrivial A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hnontrivial (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hrow_nontrivial⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
        (p := p) (A := A) (G := G) π).2 hrow_nontrivial

omit [IsAlgClosed k] [CharP k p] in
/-- Forward full mixed adapter from the full-row direct Brauer-character congruence to the
requested nontrivial-column input. -/
theorem fullMixedModelBrauerCharacterNontrivialReadbackInput_of_pointwiseReadbackCongruence
    (hpoint :
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hpoint (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hrow⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
      (p := p) (A := A) (G := G) π).1 hrow

omit [IsAlgClosed k] [CharP k p] in
/-- Reverse full mixed adapter: the nontrivial-column input recovers the full-row congruence,
again because the `centralizerPPart = 1` columns are automatic. -/
theorem fullMixedModelBrauerCharacterPointwiseReadbackCongruence_of_nontrivialReadbackInput
    (hnontrivial :
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterPointwiseReadbackCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hnontrivial (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hrow_nontrivial⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
      (p := p) (A := A) (G := G) π).2 hrow_nontrivial

omit [IsAlgClosed k] [CharP k p] in
/-- A full mixed source API for the Brauer-character rows closes the nontrivial-column input. -/
theorem fullMixedModelBrauerCharacterNontrivialReadbackInput_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      fullMixedModelBrauerCharacterPointwiseSourceAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerCharacterPointwiseSourceAPI
      (p := p) (A := A) (G := G)
      (hapi (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full Serre `18.5(a)` source-text point-mass theorem closes the requested full mixed
nontrivial-column Brauer-character input. -/
theorem fullMixedModelBrauerCharacterNontrivialReadbackInput_of_serre18_5ASourceTextTheorem
    (hsource :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G) := by
  have hpoint :
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
    fullMixedModelBrauerCharacterPointwiseReadbackCongruence_of_serre18_5ASourceTextTheorem
      (p := p) (k := k) (G := G) hsource
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hpoint (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hrow⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
      (p := p) (A := A) (G := G) π).1 hrow

end FullMixedNontrivialReadbackInputSourceWorker

end Representation
