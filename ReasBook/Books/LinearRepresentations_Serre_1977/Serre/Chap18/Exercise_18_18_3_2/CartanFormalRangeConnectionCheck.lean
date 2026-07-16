import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPointwiseResidualCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassNontrivialResidualProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeNontrivialResidualSplit
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCastRegularValueProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeConnectionCheck

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeConnectionCheckFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeConnectionCheckDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Connection check: the final maximum-parallel inputs close the Cartan range support theorem
directly. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_cast_connectionCheck
    (hnontrivial :
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_projectiveEnvelopeCast
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hnontrivial (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hcast (A := A) (K := K) e0)

/-- Connection check: a full mixed Brauer-basis readback input closes the Cartan range support
theorem through the maximum-parallel split. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_readbackInput_connectionCheck
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hnontrivial :
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)).2
        (hread (A := A) (K := K) e0)
  let hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
    exact
      coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope
        (hread (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_cast_connectionCheck
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hnontrivial (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hcast (A := A) (K := K) e0)

/-- Connection check: a full mixed pointwise residual blocker closes the Cartan range support
theorem after converting it to the readback input. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointwiseResidual_connectionCheck
    (hpointwise :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
          (p := p) (A := A) (G := G)
          (hpointwise (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_readbackInput_connectionCheck
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hread (A := A) (K := K) e0)

/-- Connection check: a source-faithful regular-value congruence closes the Cartan range support
theorem by first producing the pointwise residual input, then using the same split. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValue_connectionCheck
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hpointwise :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        (hregular (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointwiseResidual_connectionCheck
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hpointwise (A := A) (K := K) e0)

end CartanFormalRangeConnectionCheck

end Representation
