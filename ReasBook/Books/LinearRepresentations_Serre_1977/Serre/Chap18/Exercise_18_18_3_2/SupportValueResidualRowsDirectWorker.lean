import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceTextProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Direct support/value construction for the point-mass residual rows.

This worker stays on Serre's source-text route.  It turns the Exercise `18.4` point-mass row
congruence into the literal support/value package for the residual rows:

* choose the coordinate-normalized `A`-basis family;
* read the row congruence as fixed-coordinate Brauer-basis readback;
* subtract the projective-envelope row to get the A-side pairing residual;
* add it back to obtain the regular-value row divisibility;
* use the support/value criterion to choose full representatives.

No Cartan cokernel/product/Smith/determinant endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalSupportValueResidualRowsDirectWorker

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

local instance supportValueResidualRowsDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance supportValueResidualRowsDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family direct construction of the full support/value residual-row representatives
from the Exercise `18.4` point-mass row congruence for the same normalized family. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_exercise18_4PointMassRowCongruenceAPI
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
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  have hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
    (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hapi
  have hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread
  have hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π :=
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hresidual
  have hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
    intro c
    simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
      virtualModularCharacterOnPRegularConjClass_class] using hrows c
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

/-- The local Exercise `18.4` row theorem gives the literal support/value residual-row package
by constructing full representatives row by row. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := kA) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (hsource π hπ_simple hπ_coord)

/-- Local provider for the projective-character source-text support/value API from the
Exercise `18.4` row theorem. -/
theorem projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) := by
  simpa [projectiveCharacterLatticeSourceTextLocalSupportValueAPI] using
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G) hsource

/-- Conversely, the literal support/value API implies the same Exercise `18.4` row theorem.
Thus the support/value construction has not weakened the target: it is exactly the row
congruence blocker. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  exercise18_4PointMassRowCongruenceSourceTheorem_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hsource)

/-- Exact local boundary for the direct support/value residual-row route. -/
theorem projectiveCharacterLatticeSourceTextLocalSupportValueAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem :
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) ↔
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)
  · exact
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (K := K) (G := G)

end LocalSupportValueResidualRowsDirectWorker

section FullMixedSupportValueResidualRowsDirectWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedSupportValueResidualRowsDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedSupportValueResidualRowsDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic package of the Exercise `18.4` row theorem. -/
def fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed provider from Exercise `18.4` row congruence to the literal support/value API. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The literal support/value API gives back the full mixed Exercise `18.4` row theorem. -/
theorem fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary for the direct support/value residual-row route. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) ↔
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)

end FullMixedSupportValueResidualRowsDirectWorker

end Representation
