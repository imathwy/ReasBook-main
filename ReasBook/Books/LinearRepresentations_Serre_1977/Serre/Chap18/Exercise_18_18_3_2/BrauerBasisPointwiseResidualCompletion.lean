import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisPointwiseResidualCompletion

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

local instance brauerBasisPointwiseResidualCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisPointwiseResidualCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Source-faithful regular-value congruence supplies the A-side pairing residual.

This is the direct Serre `18.5(a)` reduction: the regular-value congruence gives the fixed
Brauer-row divisibility, and the pure A-side Exercise `18.4` residual endpoint subtracts the
projective-envelope row isolated by orthogonality. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    refine
      (fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete).1 ?_
    intro c
    simpa [hπ_coord c] using hregular ([π c]₀ : R₀[k](G))
  exact
    brauerPointMassBasisResidualDivisibility_of_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Universal pairing residual form obtained from the local regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulPairingResidualProof_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPairingResidualProof
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hregular

/-- The full pairing residual immediately gives the reduced pointwise residual form. -/
theorem regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_pairingResidualProof
    (hpairing :
      regularValueCongruenceSourceFaithfulPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseResidualProof
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord c d _hd
  exact hpairing π hπ_simple hπ_coord c d

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Universal pointwise residual form obtained from the local regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseResidualProof
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_pairingResidualProof
    (p := p) (A := A) (G := G)
    (regularValueCongruenceSourceFaithfulPairingResidualProof_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G) hregular)

end BrauerBasisPointwiseResidualCompletion

section FullMixedModelBrauerBasisPointwiseResidualCompletion

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisPointwiseResidualCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisPointwiseResidualCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model pairing residual blocker from an independent source-faithful regular-value
congruence proof. -/
theorem fullMixedModelBrauerBasisPairingResidualBlocker_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulPairingResidualProof_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model pointwise residual blocker from an independent source-faithful
regular-value congruence proof.  This is the form that feeds directly into
`fullMixedModelBrauerBasisReadbackInput_of_pointwiseResidualBlocker`. -/
theorem fullMixedModelBrauerBasisPointwiseResidualBlocker_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice source input gives the requested full mixed pointwise residual
blocker, via Serre `18.5(a)` and the A-side pairing residual bridge above. -/
theorem fullMixedModelBrauerBasisPointwiseResidualBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  let hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) :=
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G) hlattice
  exact
    regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Readback input closed from an independent source-faithful regular-value congruence, routed
through the pointwise residual blocker requested by the final integration API. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_regularValueCongruence_via_pointwiseResidual
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
      (p := p) (A := A) (G := G)
      (regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        (hregular (A := A) (K := K) e0))

end FullMixedModelBrauerBasisPointwiseResidualCompletion

end Representation
