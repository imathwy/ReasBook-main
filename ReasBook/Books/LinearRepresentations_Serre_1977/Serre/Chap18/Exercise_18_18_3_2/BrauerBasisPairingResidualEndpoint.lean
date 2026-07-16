import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerBasisPairingResidualEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisPairingResidualEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisPairingResidualEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Existential A-side form of the pairing residual.  Unlike
`regularValueCongruenceSourceFaithfulPairingResidualProof`, this asks only for one
coordinate-normalized complete simple family, matching the readback input endpoint. -/
def regularValueCongruenceSourceFaithfulExistsPairingResidualProof : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The existential pairing residual is exactly the existing point-mass basis residual, after
aligning the two definitions pointwise. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, hresidual⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      brauerPointMassBasisResidualDivisibility_of_coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual
  · rintro ⟨π, hπ_simple, hπ_coord, hbasis⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hbasis

/-- An existential pairing residual closes the local Brauer-basis readback input directly, by
adding back the visible projective-envelope row isolated by Exercise `18.4` and orthogonality. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual)

set_option linter.style.longLine false in
/-- The existential pairing residual and the fixed-coordinate Brauer-basis readback input are the
same local missing datum.  The forward direction keeps the chosen coordinate-normalized family
and only rewrites the residual formula; it does not replace the fixed
`regularClassCoordinateAddEquiv` coordinates by a natural Brauer table coordinate. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPairingResidualProof :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hread
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
        (p := p) (A := A) (G := G)).2
        ((regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_basisResidual
          (p := p) (A := A) (G := G)).1 hread)
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
        (p := p) (A := A) (G := G)

end LocalBrauerBasisPairingResidualEndpoint

section FullMixedBrauerBasisPairingResidualEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisPairingResidualEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisPairingResidualEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic existential pairing-residual blocker.  This is weaker than the
universal `fullMixedModelBrauerBasisPairingResidualBlocker`, but has the same quantifier shape as
`fullMixedModelBrauerBasisReadbackInput`. -/
def fullMixedModelBrauerBasisExistsPairingResidualBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed existential pairing-residual blocker is the point-mass basis-residual blocker
with the residual formula written in pairing notation. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_basisResidualDivisibilityBlocker :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
        (p := p) (A := A) (G := G)).1
        (hblock (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
        (p := p) (A := A) (G := G)).2
        (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The universal pairing-residual blocker supplies the existential version by choosing the
standard coordinate-normalized complete family. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_pairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact hresidual (A := A) (K := K) e0 π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- Existential pairing residuals close the full mixed Brauer-basis readback input without using
the final Cartan range endpoint. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
      (p := p) (A := A) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed existential pairing-residual blocker is equivalent to the full mixed
fixed-coordinate Brauer-basis readback input.  This records that the residual route has not
removed the fixed-coordinate readback problem; it has only put the same datum in the Serre
`18.4` pairing notation. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_readbackInput :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisReadbackInput_of_existsPairingResidualBlocker
        (p := p) (k := k) (G := G)
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPairingResidualProof
        (p := p) (A := A) (G := G)).1
        (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- A universal pairing-residual blocker also gives the point-mass basis residual blocker; this
is just the existential specialization plus the formula alignment above. -/
theorem fullMixedModelPointMassBasisResidualDivisibilityBlocker_of_pairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassBasisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
      (p := p) (A := A) (G := G)).1
      (by
        rcases exists_coordinate_normalized_complete_family_with_projective_envelopes
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
          ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
        refine ⟨π, hπ_simple, hπ_coord, ?_⟩
        exact hresidual (A := A) (K := K) e0 π hπ_simple hπ_coord)

end FullMixedBrauerBasisPairingResidualEndpoint

end Representation
