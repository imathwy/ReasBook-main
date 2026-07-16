import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerOrthogonalityCongruenceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassRowsReadbackSourceHelper

/-!
Source-side closure for the A-valued point-mass row input.

The main local contribution is the reverse direction to `PairingResidualDirectWorker`: once the
pure A-side pairing residual is known, adding back the projective-envelope row computed from
Exercise `18.4` and `<Phi_E, phi_E'> = delta_EE'` recovers the point-mass regular-value
divisibility row.  No Cartan range, cokernel, product, or determinant endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassRowsSourceClosureWorker

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

local instance pointMassRowsSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassRowsSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The pure A-side pairing residual implies the direct point-mass regular-value row
divisibility.

For each row, the residual gives divisibility after subtracting the projective-envelope row.
Exercise `18.4` plus projective-envelope orthogonality identifies that subtracted row as
`p^{z(s)}` times an `A`-coefficient, so adding it back preserves the same regular-value
divisibility condition. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
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
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  classical
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  intro c
  let row : PRegularConjClass G p → K :=
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) (π c)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  refine (mem_regularValueDivisibilitySubmodule_iff
    (p := p) (A := A) (K := K) (G := G) row).2 ?_
  intro d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d))) c
  let proj : K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
  rcases hresidual c d with ⟨a, ha⟩
  refine ⟨a + coeff, ?_⟩
  have ha' :
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff =
          z * a := by
    simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility,
      hπ_pairwise, hπ_complete, bA, z, coeff] using ha
  have hresK : row d - proj = algebraMap A K (z * a) := by
    calc
      row d - proj =
          algebraMap A K
            (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              z * coeff) := by
            simpa [row, proj, hπ_pairwise, hπ_complete, bA, z, coeff] using
              (canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
                (p := p) (A := A) (K := K) (G := G)
                π hπ_simple hπ_coord P hP_envelope c d)
      _ = algebraMap A K (z * a) := by
            rw [ha']
  have hproj : proj = algebraMap A K (z * coeff) := by
    simpa [proj, hπ_pairwise, hπ_complete, bA, z, coeff] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  calc
    row d = (row d - proj) + proj := by
      rw [sub_add_cancel]
    _ = algebraMap A K (z * a) + algebraMap A K (z * coeff) := by
      rw [hresK, hproj]
    _ = algebraMap A K (z * (a + coeff)) := by
      simp [mul_add]

/-- Fixed-family equivalence between the direct point-mass row divisibility input and the
pure A-side pairing residual. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_pairingResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord

/-- Existential pairing residuals give the corresponding existential point-mass row source. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  exact
    ⟨π, hπ_simple, hπ_coord,
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord hresidual⟩

/-- The existential point-mass row source and the existential A-side pairing residual are the
same local source datum. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_sourceRows :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_existsPairingResidualProof
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_sourceRows
        (p := p) (A := A) (K := K) (G := G)

/-- A residual proof can be re-expressed as the explicit Serre `18.4`/orthogonality pairing-sum
input, by choosing projective envelopes for the same coordinate-normalized family. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    orthogonalityPairingSumResidualCongruence_of_coordinateNormalizedPairingResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual

/-- The explicit orthogonality source input is equivalent to the existential A-side pairing
residual. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_orthogonalityInput :
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsPairingResidualProof
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
        (p := p) (A := A) (K := K) (G := G)

end LocalPointMassRowsSourceClosureWorker

section FullMixedPointMassRowsSourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassRowsSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassRowsSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed bridge from the existential A-side pairing residual to the requested direct
point-mass regular-value row input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the direct point-mass regular-value row input gives the existential A-side
pairing residual. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_pointMassRowsInRegularValueSubmoduleInput
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_sourceRows
      (p := p) (A := A) (K := K) (G := G)
      (by
        simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
          hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed equivalence between the requested direct row input and the existential A-side
pairing residual. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_existsPairingResidualBlocker :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_pointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_existsPairingResidualBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed residuals can be written as the explicit Serre `18.4`/orthogonality source input. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed existential pairing residual and the explicit orthogonality source input are
equivalent. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_orthogonalityInput :
    fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_of_existsPairingResidualBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_orthogonalityInput
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Final source compression: the requested direct point-mass row input is equivalent to the
explicit Exercise `18.4` / projective-envelope orthogonality source input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_existsPairingResidualBlocker
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_orthogonalityInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- One-way form most useful to downstream workers: explicit orthogonality closes the requested
direct point-mass row input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
    (p := p) (k := k) (G := G)).2 horth

end FullMixedPointMassRowsSourceClosureWorker

end Representation
