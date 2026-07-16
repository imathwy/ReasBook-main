import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFixedFamilyCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassOrthogonalitySourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualSourceWorker

/-!
Source-side closure adapters for the fixed-coordinate Brauer-basis readback input.

This file stays on the local Exercise `18.4`/orthogonality side.  It packages the exact
pointwise row-entry congruence which remains to be proved, and records that the existing
pairing-sum, visible point-mass, and projective-envelope residual inputs all close
`regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerBasisReadbackSourceClosureWorker

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

local instance brauerBasisReadbackSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact remaining fixed-family source theorem in pointwise row-entry form.

For a coordinate-normalized complete family `π`, each canonical DVR Brauer-basis row must be
congruent to the corresponding point mass modulo the `p`-part of the target centralizer. -/
def coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- For a coordinate-normalized family, the pointwise row-entry source theorem is equivalent
to the canonical fixed-coordinate readback divisibility. -/
theorem coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  constructor
  · intro hsource c d
    rcases hsource c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hcoord_d :
        ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
      rw [hπ_coord c]
    simpa [coordinateNormalizedBrauerBasisPointwiseReadbackSource,
      brauerBasisFixedCoordinateReadbackDivisibility, hπ_pairwise, hπ_complete, hcoord_d]
      using ha
  · intro hread c d
    rcases hread c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hcoord_d :
        ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
      rw [hπ_coord c]
    simpa [coordinateNormalizedBrauerBasisPointwiseReadbackSource,
      brauerBasisFixedCoordinateReadbackDivisibility, hπ_pairwise, hπ_complete, hcoord_d]
      using ha

/-- Existential package of the exact pointwise source theorem needed for the local readback
input. -/
def regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The exact pointwise source package closes the local readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseReadbackSource
    (hsource :
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hsource⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, an existing local readback input supplies the same pointwise source package.
This records that the named pointwise proposition is precisely the remaining local blocker. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_readbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
      (p := p) (A := A) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Local equivalence between the readback input and the exact pointwise source package. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_pointwiseReadbackSource :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_readbackInput
        (p := p) (A := A) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseReadbackSource
        (p := p) (A := A) (G := G)

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family adapter from the visible point-mass source congruence to the local readback
input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_visibleDivisibilitySource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      coordinateNormalizedPointMassVisibleDivisibilitySource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_visibleDivisibilitySource
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hsource

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family adapter from the orthogonality-worker point-mass source congruence to the
local readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

/-- Fixed-family adapter from the explicit Exercise `18.4`/projective-envelope pairing-sum
residual congruence to the local readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_orthogonalityPairingSum_direct
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope horth

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family adapter from the A-side pairing residual to the local readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pairingResidual
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
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

/-- Fixed-family adapter from the projective-envelope residual formula to the local readback
input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveEnvelopeResidualFormula
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual :
      ∀ c d : PRegularConjClass G p,
        ∃ a : A,
          (FDRep.modularCharacterOnPRegularConjClass
                (p := p) (G := G) (A := K) (π c)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
              algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualFormula
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential adapter from the A-side projective-envelope residual source input to the local
readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveEnvelopeResidualSourceInput
    (hsource :
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pairingResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

end LocalBrauerBasisReadbackSourceClosureWorker

section FullMixedBrauerBasisReadbackSourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisReadbackSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisReadbackSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic package of the exact pointwise source theorem. -/
def fullMixedModelBrauerBasisPointwiseReadbackSource : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed adapter from the pointwise source package to the Brauer readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pointwiseReadbackSource
    (hsource :
      fullMixedModelBrauerBasisPointwiseReadbackSource
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseReadbackSource
      (p := p) (A := A) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed adapter from the A-side projective-envelope residual source input to the Brauer
readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_projectiveEnvelopeResidualSourceInput_sourceClosure
    (hsource :
      fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveEnvelopeResidualSourceInput
      (p := p) (A := A) (G := G)
      (hsource (A := A) (K := K) e0)

end FullMixedBrauerBasisReadbackSourceClosureWorker

end Representation
