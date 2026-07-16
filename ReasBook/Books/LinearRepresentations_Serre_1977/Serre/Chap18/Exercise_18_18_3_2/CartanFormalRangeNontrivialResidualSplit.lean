import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeReadbackCastSplit

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeNontrivialResidualSplit

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeNontrivialResidualSplitFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeNontrivialResidualSplitDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Maximum-parallel endpoint with the 18.5(a) side reduced to nontrivial residual columns.

The two inputs are independent:
* `hnontrivial` is the A-side residual only at coordinates with nontrivial centralizer `p`-part;
  the `centralizerPPart = 1` coordinates are filled by the local pointwise residual API.
* `hforward` is the forward fixed-coordinate diagonal congruence used for the source-span side.

No final Cartan range, cokernel-product, or determinant endpoint is used to prove either input. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_forwardDiagonal
    (hnontrivial :
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
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
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_of_nontrivialResidualDivisibility
        (p := p) (A := A) (G := G)
        (hnontrivial (A := A) (K := K) e0)
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
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_residualPointMass_and_forwardDiagonal
      (p := p) (k := k) (G := G) hresidual hforward

/-- Same maximum-parallel endpoint with the forward side stated as projective-envelope
cast-preservation. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_projectiveEnvelopeCast
    (hnontrivial :
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
        (p := p) (k := k) (G := G) :=
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_projectiveEnvelope_castRegularValue
      (p := p) (k := k) (G := G) hcast
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialResidual_and_forwardDiagonal
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
        hforward (A := A) (K := K) e0)

end CartanFormalRangeNontrivialResidualSplit

end Representation
