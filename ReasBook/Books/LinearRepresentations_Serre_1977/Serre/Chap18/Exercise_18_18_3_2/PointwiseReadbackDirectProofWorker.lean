import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceClosureWorker

/-!
Direct pointwise readback worker.

This file opens the canonical DVR Brauer basis far enough to identify the remaining source
blocker with a row-value congruence for the actual Brauer characters
`FDRep.modularCharacterOnPRegularConjClass (π c) primeToPRoot_canonicalLift`.

No Cartan range, cokernel, product, or final endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointwiseReadbackDirectProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance pointwiseReadbackDirectProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointwiseReadbackDirectProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The direct row-value API still missing from `canonicalDVRBrauerBasis`.

After unfolding `canonicalDVRBrauerBasis`, its `c`-th row is the Brauer character of `π c`
with the canonical Hensel lift of prime-to-`p` roots.  Thus the exact remaining pointwise
input is that this row is congruent to the coordinate point mass modulo the target
centralizer `p`-part. -/
def brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := A) (π c)
          (primeToPRoot_canonicalLift (p := p) (A := A)) d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The existing canonical-basis pointwise source is definitionally the direct Brauer-character
row-value congruence above, once `canonicalDVRBrauerBasis` is opened. -/
theorem coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  constructor
  · intro hsource c d
    simpa [coordinateNormalizedBrauerBasisPointwiseReadbackSource,
      brauerCharacterPointwiseReadbackCongruence, canonicalDVRBrauerBasis,
      hπ_pairwise, hπ_complete] using hsource c d
  · intro hapi c d
    simpa [coordinateNormalizedBrauerBasisPointwiseReadbackSource,
      brauerCharacterPointwiseReadbackCongruence, canonicalDVRBrauerBasis,
      hπ_pairwise, hπ_complete] using hapi c d

/-- Forward adapter from the direct Brauer-character row-value congruence to the existing
canonical-basis pointwise readback source. -/
theorem coordinateNormalizedBrauerBasisPointwiseReadbackSource_of_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hapi :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    coordinateNormalizedBrauerBasisPointwiseReadbackSource
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hapi

end LocalPointwiseReadbackDirectProofWorker

section FullMixedPointwiseReadbackDirectProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointwiseReadbackDirectProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointwiseReadbackDirectProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the direct Brauer-character row-value API isolated in
this file.  This is the missing upstream input for an unconditional proof of
`fullMixedModelBrauerBasisPointwiseReadbackSource`. -/
def fullMixedModelBrauerCharacterPointwiseReadbackCongruence : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ _ : ∀ c, Simple (π c),
          ∃ _ :
            (∀ c : PRegularConjClass G p,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
            brauerCharacterPointwiseReadbackCongruence
              (p := p) (A := A) (G := G) π

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model equivalence: the exact requested pointwise source is equivalent to the
direct Brauer-character row-value congruence for one coordinate-normalized family in every
mixed model. -/
theorem fullMixedModelBrauerBasisPointwiseReadbackSource_sourceProof_iff_brauerCharacterPointwiseReadbackCongruence :
    fullMixedModelBrauerBasisPointwiseReadbackSource
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hsource A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hsource (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hpoint⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hpoint
  · intro hapi A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hapi (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hpoint⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

omit [IsAlgClosed k] [CharP k p] in
/-- Conditional source proof: an upstream proof of the direct Brauer-character row congruence
closes the requested full mixed-model pointwise readback source. -/
theorem fullMixedModelBrauerBasisPointwiseReadbackSource_sourceProof_of_brauerCharacterPointwiseReadbackCongruence
    (hapi :
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseReadbackSource
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hapi (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hpoint⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

end FullMixedPointwiseReadbackDirectProofWorker

end Representation
