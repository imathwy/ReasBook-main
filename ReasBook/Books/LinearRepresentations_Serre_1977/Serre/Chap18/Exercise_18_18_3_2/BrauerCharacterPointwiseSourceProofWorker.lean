import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointwiseReadbackDirectProofWorker

/-!
Source-side worker for the final Brauer-character pointwise readback blocker.

This file keeps the remaining source theorem on the Brauer-character side.  It opens the
canonical DVR Brauer basis far enough to expose its row values as
`FDRep.modularCharacterOnPRegularConjClass ... primeToPRoot_canonicalLift`, then isolates the
only missing non-Cartan input: the coordinate-normalized Brauer rows are congruent to the
corresponding point masses modulo the centralizer `p`-part.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerCharacterPointwiseSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerCharacterPointwiseSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerCharacterPointwiseSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Opening `canonicalDVRBrauerBasis`: its rows are exactly the Brauer characters with the
canonical Hensel lift of prime-to-`p` roots. -/
theorem canonicalDVRBrauerBasis_apply_eq_modularCharacterOnPRegularConjClass
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : PRegularConjClass G p) :
    canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete c =
      FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := A) (π c)
        (primeToPRoot_canonicalLift (p := p) (A := A)) := by
  simp [canonicalDVRBrauerBasis]

/-- The exact local source API still missing for the direct Brauer-character route.

For every coordinate-normalized complete Brauer family, the actual Brauer-character row value
must be congruent to the corresponding point mass modulo the `p`-part of the target
centralizer. -/
def coordinateNormalizedBrauerCharacterPointwiseSourceAPI : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π

/-- The API above is exactly the canonical-basis pointwise readback statement after opening
`canonicalDVRBrauerBasis` with
`canonicalDVRBrauerBasis_apply_eq_modularCharacterOnPRegularConjClass`. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_pointwiseReadbackSource :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hapi π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hapi π hπ_simple hπ_coord)
  · intro hread π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hread π hπ_simple hπ_coord)

/-- Local adapter: a proof of the pointwise Brauer-character source API supplies the existing
local existential source package. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
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
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
      (hapi π hπ_simple hπ_coord)

end LocalBrauerCharacterPointwiseSourceProofWorker

section FullMixedBrauerCharacterPointwiseSourceProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerCharacterPointwiseSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerCharacterPointwiseSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed form of the precise local source API isolated above. -/
def fullMixedModelBrauerCharacterPointwiseSourceAPI : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Adapter for the requested full mixed theorem.

The only missing input is the local theorem
`coordinateNormalizedBrauerCharacterPointwiseSourceAPI`, i.e. the centralizer-`p`-part
congruence for the actual Brauer-character rows after opening
`FDRep.modularCharacterOnPRegularConjClass` and `primeToPRoot_canonicalLift`. -/
theorem fullMixedModelBrauerCharacterPointwiseReadbackCongruence_sourceProof_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      fullMixedModelBrauerCharacterPointwiseSourceAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterPointwiseReadbackCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      (exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (G := G) :
        ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
          (∀ c, Simple (π c)) ∧
            (∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
            PairwiseNonisomorphic π ∧
            IsCompleteIrreducibleFamily π ∧
            ∃ P : PRegularConjClass G p →
                FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
              ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
                f.IsProjectiveEnvelope) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact hapi (A := A) (K := K) e0 π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- The same adapter landing in the existing canonical-basis pointwise source package. -/
theorem fullMixedModelBrauerBasisPointwiseReadbackSource_sourceProof_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      fullMixedModelBrauerCharacterPointwiseSourceAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseReadbackSource
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_brauerCharacterPointwiseSourceAPI
      (p := p) (A := A) (G := G)
      (hapi (A := A) (K := K) e0)

end FullMixedBrauerCharacterPointwiseSourceProofWorker

end Representation
