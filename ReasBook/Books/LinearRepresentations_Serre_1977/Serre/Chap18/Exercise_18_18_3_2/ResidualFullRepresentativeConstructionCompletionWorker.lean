import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SupportValueResidualRowsDirectWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionWitnessCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker

/-!
Residual full-representative construction frontier.

This worker keeps the Serre `18.5(a)` source route explicit.  The construction below starts
from the Exercise `18.4` point-mass row congruence, i.e. the `A`-basis/readback statement after
the projective-envelope orthogonality relation `<Phi_E, phi_E'> = delta_EE'` has been evaluated.
It then constructs the full class-function representatives required by the support/value API.

No Cartan cokernel/product/Smith/determinant endpoint, and no projective-character lattice
statement, is used as source input for the construction direction.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalResidualFullRepresentativeConstructionCompletionWorker

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

local instance residualFullRepresentativeConstructionCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance residualFullRepresentativeConstructionCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family construction of full projective representatives for the coordinate-normalized
residual rows from the Exercise `18.4` point-mass row congruence for the same family.

The support/value rows are built by
`coordinateNormalizedPointMassResidualSerreSupportValueSource_of_exercise18_4PointMassRowCongruenceAPI`;
Serre `18.5(a)` then turns those pointwise conditions into projective-character membership for
the chosen full representative. -/
theorem coordinateNormalizedPointMassResidualFullRepresentativeWitness_of_exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hapi :
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedPointMassResidualFullRepresentativeWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  have hsource :
      coordinateNormalizedPointMassResidualSerreSupportValueSource
        (p := p) (A := A) (K := K) (G := G) π :=
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hapi
  intro c
  rcases hsource c with ⟨Φ, hzero, hvalue, hres⟩
  refine ⟨Φ, ?_, hres⟩
  exact
    mem_projectiveCharacterSubmodule_of_serre18_5a_rhs_of_enoughRoots
      (p := p) (A := A) (K := K) (G := G) hzero hvalue

/-- Local construction of the support/value API from the source-side Exercise `18.4`/
orthogonality point-mass blocker.

This is the residual full-representative construction in package form.  The only hypothesis is
the point-mass congruence left after Exercise `18.4` and orthogonality readback; the zero
off the `p`-regular locus and centralizer-`p`-part value divisibility are constructed by the
fixed-family support/value theorem. -/
theorem projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_orthogonalityPointMassSourceBlocker
    (hsource :
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G)) :
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, _P, _hP_envelope, hapi⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (by
        simpa [exercise18_4PointMassRowCongruenceAPI] using hapi)

/-- Exact local boundary for this construction route.

Thus the remaining local gap is not the full representative, zero-off-regular, or
value-divisibility adapter: it is precisely the Exercise `18.4`/orthogonality point-mass source
blocker. -/
theorem projectiveCharacterLatticeSourceTextLocalSupportValueAPI_iff_orthogonalityPointMassSourceBlocker :
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_orthogonalityPointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).1
        (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
          (p := p) (A := A) (K := K) (G := G) hsource)
  · exact
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_orthogonalityPointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)

end LocalResidualFullRepresentativeConstructionCompletionWorker

section FullMixedResidualFullRepresentativeConstructionCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedResidualFullRepresentativeConstructionCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedResidualFullRepresentativeConstructionCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed construction of the support/value API from the Exercise `18.4`/orthogonality
point-mass source blocker in every mixed-characteristic model. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_orthogonalityPointMassSourceBlocker
    (hsource :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_orthogonalityPointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary: the constructed support/value package is equivalent to the
Exercise `18.4`/orthogonality point-mass source blocker. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_orthogonalityPointMassSourceBlocker :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hsource A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (projectiveCharacterLatticeSourceTextLocalSupportValueAPI_iff_orthogonalityPointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).1
        (hsource (A := A) (K := K) e0)
  · exact
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_orthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed construction from the larger explicit orthogonality input. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hblock :
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) :=
    (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G)).1
      (horth (A := A) (K := K) e0)
  exact
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_orthogonalityPointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G) hblock

omit [IsAlgClosed k] [CharP k p] in
/-- Conditional endpoint adapter: once the Exercise `18.4`/orthogonality input is supplied, the
constructed support/value package closes `fullMixedModelRegularValueSourceStatement`. -/
theorem fullMixedModelRegularValueSourceStatement_of_residualFullRepresentativeConstruction
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  have hsupport :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) :=
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_orthogonalityInput
      (p := p) (k := k) (G := G) horth
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) :=
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsupport (A := A) (K := K) e0)
  exact
    (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)).1 hlattice

end FullMixedResidualFullRepresentativeConstructionCompletionWorker

end Representation
