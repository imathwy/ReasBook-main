import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualSourceValuationWorker

/-!
High-order DVR valuation route for the remaining Serre `18.5(a)` source input.

This file keeps the target on the source side.  It does not use the Cartan cokernel/product/Smith
or determinant endpoints.  The main point is that the Exercise `18.4` point-mass row congruence is
equivalent to the higher-order statement
`centralizerPPart p d = p ^ n -> (p : A) ^ n | pairingResidual c d`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalDVRValuationRegularValueSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance dvrValuationRegularValueSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance dvrValuationRegularValueSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local universal high-order residual statement for the coordinate-normalized Brauer families
used by the Exercise `18.4` source row congruence. -/
def coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- For one coordinate-normalized family, Exercise `18.4`'s row congruence is exactly the
high-order `p^n` DVR residual divisibility input. -/
theorem exercise18_4PointMassRowCongruenceAPI_iff_pairingResidualPrimePowInput
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
    ((coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).symm.trans
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_divisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).symm)

/-- Local source-theorem form: the Exercise `18.4` point-mass row theorem is equivalent to the
universal higher-order `p^n` residual divisibility statement. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_pairingResidualPrimePowSourceTheorem :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource π hπ_simple hπ_coord
    exact
      (exercise18_4PointMassRowCongruenceAPI_iff_pairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hsource π hπ_simple hπ_coord)
  · intro hpow π hπ_simple hπ_coord
    exact
      (exercise18_4PointMassRowCongruenceAPI_iff_pairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hpow π hπ_simple hπ_coord)

end LocalDVRValuationRegularValueSourceWorker

section FullMixedDVRValuationRegularValueSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedDVRValuationRegularValueSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedDVRValuationRegularValueSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed higher-order residual blocker is sufficient for the regular-value source
statement. -/
theorem fullMixedModelRegularValueSourceStatement_of_pairingResidualPrimePowBlocker
    (hpow :
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) := by
    refine
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_universalReadback
        (p := p) (A := A) (G := G) ?_
    intro π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord
          (hpow (A := A) (K := K) e0 π hπ_simple hπ_coord))
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the regular-value source statement supplies the same higher-order residual
blocker, through the existing source-side projective-character lattice equivalence. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_of_regularValueSourceStatement
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
      (p := p) (k := k) (G := G) := by
  have hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
    (fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof
      (p := p) (k := k) (G := G)).1 hregular
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact boundary for the high-order DVR route: proving the `p^n` pairing-residual
blocker is equivalent to proving the regular-value source statement. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_iff_regularValueSourceStatement :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelRegularValueSourceStatement_of_pairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_of_regularValueSourceStatement
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The same boundary, phrased against the projective-character lattice source theorem. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_iff_projectiveCharacter_lattice :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_iff_regularValueSourceStatement
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof
      (p := p) (k := k) (G := G))

end FullMixedDVRValuationRegularValueSourceWorker

end Representation
