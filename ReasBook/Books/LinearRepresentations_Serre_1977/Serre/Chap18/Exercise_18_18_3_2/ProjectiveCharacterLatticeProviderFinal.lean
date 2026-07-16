import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceFaithful
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionClosureFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRowsProviderFinal

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterLatticeProviderFinal

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

local instance projectiveCharacterLatticeProviderFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeProviderFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side provider for the projective-character lattice congruence.

This is the direct `g/hrow/hcompat` instantiation of
`projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_*`: for a
coordinate-normalized family we take `g c = Pi.single c 1`; the row hypothesis is exactly the
point-mass projective-character row input, and the compatibility with the fixed integer
representatives is zero by `hπ_coord`. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrow⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  refine
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_projectiveLatticeRepresentatives_rowwiseModuloDiagonal
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete
      (fun c : PRegularConjClass G p =>
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ?_ ?_
  · intro c
    simpa using hrow c
  · intro c
    rw [hπ_coord c]
    simp

/-- Equivalent explicit source-witness version of the local provider. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) hwitness)

/-- Source-side provider from the existential pairing residual isolated by Exercise `18.4`.

This is the smallest currently available non-Cartan input for the projective-character lattice
route: the pairing residual constructs the point-mass projective rows, and the rows give the
lattice congruence by the Serre-basis representative adapter above. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueSourceCompletionPointMassProjectiveRowInput_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G) hresidual)

/-- Source-side provider from the projective-envelope residual isolated by the Serre
`18.5(a)` route.

The residual input is upstream of the lattice statement: it constructs the point-mass
projective-character rows, and the existing row adapter then applies the global
projective-character divisibility lattice. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveEnvelopeResidual
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G) hresidual)

end LocalProjectiveCharacterLatticeProviderFinal

section FullMixedProjectiveCharacterLatticeProviderFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeProviderFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeProviderFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from the exact point-mass projective row input. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from explicit point-mass projective-restriction witnesses.

An unconditional proof of this hypothesis is the remaining source-side row construction:
for one coordinate-normalized complete Brauer family, construct a projective character whose
regular restriction is each row difference
`virtualModularCharacterOnPRegularConjClass ... [π c]₀ -
regularIntegerFunctionCast ... (Pi.single c 1)`. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from the projective-envelope residual blocker.

This is the non-Cartan bridge from the current smallest projective-envelope residual input to
the global projective-character lattice provider. -/
theorem
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveEnvelopeResidualBlocker
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidualBlocker
      (p := p) (k := k) (G := G) hresidual)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic provider from the existential pairing-residual blocker. -/
theorem
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

end FullMixedProjectiveCharacterLatticeProviderFinal

end Representation
