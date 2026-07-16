import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackResidualProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerVisibleReadbackSourceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityInputSourceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Point-mass rows regular-value source completion boundary.

This worker keeps the source-side gap in the Exercise `18.4` / orthogonality form.  The key
fixed-family result below shows that the direct point-mass row regular-value input is exactly
the same local source theorem as the already isolated Exercise `18.4` point-mass row
congruence.  No Cartan range, cokernel, product, Smith, or determinant endpoint is used.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassRowsRegularValueSourceCompletionWorker

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

local instance pointMassRowsRegularValueSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassRowsRegularValueSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family exact boundary: the direct regular-value row input is equivalent to the
Exercise `18.4` / orthogonality point-mass row congruence for the same coordinate-normalized
Brauer family. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π ↔
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hrows
    have hresidual :
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_pairingResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hrows
    have hread :
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual
    exact
      (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread
  · intro hapi
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
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread
    exact
      (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_pairingResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hresidual

/-- Exercise `18.4` / orthogonality point-mass row congruence supplies the direct
regular-value point-mass rows. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_exercise18_4PointMassRowCongruenceAPI
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
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π :=
  (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_exercise18_4PointMassRowCongruenceAPI
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hapi

/-- The same source blocker closes visible readback through
`coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_pointMassRows`. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_exercise18_4PointMassRowCongruenceAPI
    (K0 : Type u) [Field K0] [Algebra A K0] [IsFractionRing A K0] [CharZero K0]
    [HasEnoughRootsOfUnity K0 (Monoid.exponent G)]
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
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  exact
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_pointMassRows
      (p := p) (A := A) (K := K0) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (K := K0) (G := G) π hπ_simple hπ_coord hapi)

end LocalPointMassRowsRegularValueSourceCompletionWorker

section FullMixedPointMassRowsRegularValueSourceCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassRowsRegularValueSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassRowsRegularValueSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact boundary: the direct point-mass regular-value row input is equivalent to
the explicit Exercise `18.4` / orthogonality point-mass source blocker. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityPointMassSourceBlocker :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- One-way source theorem form: the explicit Exercise `18.4` / orthogonality point-mass
blocker supplies the requested direct point-mass regular-value row input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_orthogonalityPointMassSourceBlocker
    (hblock :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hblock (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, _P, _hP_envelope, hsource⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (by
        simpa [exercise18_4PointMassRowCongruenceAPI] using hsource)

end FullMixedPointMassRowsRegularValueSourceCompletionWorker

end Representation
