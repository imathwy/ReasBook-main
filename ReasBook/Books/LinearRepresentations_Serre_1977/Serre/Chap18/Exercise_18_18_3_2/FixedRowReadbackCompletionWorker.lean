import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackInputCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PairingFunctionalPointMassRowWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker

/-!
Fixed-row readback completion boundary for Serre `18.5(a)`.

Exercise `18.4` supplies the `A`-basis of Brauer character rows.  The orthogonality relation
`<Phi_E, phi_E'> = delta_EE'` is already available as
`projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta`: the projective-envelope
pairing functional reads the fixed coordinate of a Brauer-basis row.

The remaining fixed-row lemma is therefore only the readout comparison between ordinary
evaluation at a regular class `d` and that projective-envelope coordinate functional, modulo the
`p`-part of the centralizer of `d`.  This file packages the sharp nontrivial-column form of that
input and proves that it closes the requested full mixed readback inputs and the regular-value
source statement, without using Cartan cokernel/product/Smith/determinant endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalFixedRowReadbackCompletionWorker

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

local instance fixedRowReadbackCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fixedRowReadbackCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The minimal nontrivial-column fixed-row readout lemma still missing after Exercise `18.4`
orthogonality.

For a coordinate-normalized Brauer family and chosen projective envelopes, ordinary evaluation
of the canonical DVR Brauer row at `d`, minus the `d`-th projective-envelope pairing functional
applied to that row, must be a `centralizerPPart(d)`-multiple.  The columns with
`centralizerPPart(d) = 1` are automatic and are intentionally not required here. -/
def fixedRowPairingFunctionalNontrivialReadout
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G) : Prop :=
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
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum
              (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- Unconditional fixed-row readback equality supplied by Exercise `18.4` and
projective-envelope orthogonality.

This is the local source-side equality behind the nontrivial fixed-row input: after the
`d`-th projective-envelope pairing functional is evaluated on the `c`-th canonical DVR
Brauer-basis row, the field-side residual is exactly the image of the visible
`bA c d - delta_cd` residual.  The remaining source obligation is only the divisibility of this
visible residual by `centralizerPPart(d)`. -/
theorem fixedRowPairingFunctional_visibleResidual_algebraMap_eq
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    algebraMap A K
        (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) =
      algebraMap A K (bA c d) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hdelta :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
        algebraMap A K
          (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d
  simp [map_sub, hdelta, bA]

/-- Fixed-family adapter: the nontrivial-column readout comparison, together with the already
formalized orthogonality readout `<Phi_E, phi_E'> = delta`, gives the direct Brauer-character
nontrivial fixed-row congruence. -/
theorem fixedCoordinateBrauerCharacterNontrivialReadbackCongruence_of_fixedRowPairingFunctionalNontrivialReadout
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hreadout :
      fixedRowPairingFunctionalNontrivialReadout
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
      (p := p) (A := A) (G := G) π := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  intro c d hd
  rcases hreadout c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  have hdelta :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
        algebraMap A K
          (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d
  have hbasis :
      bA c d =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := A) (π c)
          (primeToPRoot_canonicalLift (p := p) (A := A)) d := by
    simp [bA, canonicalDVRBrauerBasis]
  calc
    algebraMap A K
        (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        =
          algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum
              (p := p) (A := A) (K := K) (G := G) (P d) (bA c) := by
            simp [map_sub, hbasis, hdelta]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
          simpa [fixedRowPairingFunctionalNontrivialReadout, hπ_pairwise, hπ_complete,
            bA] using ha

/-- Local existential package for the minimal fixed-row readout lemma. -/
def regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
          ∃ _hP_envelope :
            ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope,
            fixedRowPairingFunctionalNontrivialReadout
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P

/-- The minimal fixed-row readout input closes the local direct nontrivial Brauer-character
readback package. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
    (hreadout :
      regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hreadout with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hrow⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    fixedCoordinateBrauerCharacterNontrivialReadbackCongruence_of_fixedRowPairingFunctionalNontrivialReadout
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hrow

/-- The same local fixed-row readout input closes the local Brauer-basis readback input through
the existing nontrivial-column adapter. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
    (hreadout :
      regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
    (p := p) (A := A) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
      (p := p) (A := A) (K := K) (G := G) hreadout)

end LocalFixedRowReadbackCompletionWorker

section FullMixedFixedRowReadbackCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedFixedRowReadbackCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedFixedRowReadbackCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model form of the minimal fixed-row readout input. -/
def fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed fixed-row adapter landing in the requested nontrivial Brauer-character
readback input. -/
theorem fullMixedModelBrauerCharacterNontrivialReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
    (hreadout :
      fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
      (p := p) (A := A) (K := K) (G := G)
      (hreadout (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed fixed-row adapter landing in the requested Brauer-basis readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
    (hreadout :
      fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
      (p := p) (A := A) (K := K) (G := G)
      (hreadout (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed fixed-row adapter all the way to the regular-value source statement consumed by
the non-endpoint range bridge. -/
theorem fullMixedModelRegularValueSourceStatement_of_fixedRowPairingFunctionalNontrivialReadout
    (hreadout :
      fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedRowPairingFunctionalNontrivialReadout
        (p := p) (A := A) (K := K) (G := G)
        (hreadout (A := A) (K := K) e0))

end FullMixedFixedRowReadbackCompletionWorker

end Representation
