import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeParallelSplit
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalBasis
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateDivisibilityProducer

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeReadbackCastSplit

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeReadbackCastSplitFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeReadbackCastSplitDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Final two-source split for the support theorem.

This packages the current maximum-parallel frontier faithfully:

* `hread` is the fixed-coordinate Brauer-basis readback congruence from Serre `18.5(a)` and
  Exercise `18.4`.
* `hcast` is the projective-envelope readback-preservation statement needed for the forward
  Cartan-coordinate divisibility half.

No Cartan range/product conclusion is used to prove either input. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_projectiveEnvelopeCast
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)
        (hread (A := A) (K := K) e0)
  have hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        (hbasis (A := A) (K := K) e0)
  have hcoord :
      fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hcast (A := A) (K := K) e0 with
      ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hcast_rows⟩
    have hbasis_div :
        ∀ c d : PRegularConjClass G p,
          ∃ a : ℤ,
            cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
              (ConjClasses.centralizerPPart p d.1 : ℤ) * a :=
      coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
        (p := p) (A := A) (K := K) (G := G) P hcast_rows
    exact
      cartanCoordinateAddHom_coordinate_divisible_of_projectiveEnvelope_basis_vectors
        (p := p) (A := A) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope hbasis_div
  have hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (hcoord (A := A) (K := K) e0)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_residualPointMass_and_forwardDiagonal
      (p := p) (k := k) (G := G) hresidual hforward

end CartanFormalRangeReadbackCastSplit

end Representation
