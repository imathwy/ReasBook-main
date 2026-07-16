import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCoordinateDivisibilityClosureWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanRingEquivTransport

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeRegularValueSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeRegularValueSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeRegularValueSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Non-endpoint regular-value source adapter for the formal Cartan range target.

The only source input is the full mixed-model regular-value congruence from Serre `18.5(a)`.
The proof then uses the fixed-coordinate p-primary route and coefficient-field transport; it does
not appeal to the downstream Cartan cokernel product or determinant endpoints. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoeth,
      instComplete, K, instField, instAlg, instFrac, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlg
  letI : IsFractionRing A K := instFrac
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom
      (R := k) (A := IsLocalRing.ResidueField A) (f := e0.symm.toRingHom)
      e0.symm.injective p
  have hrange :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    fullMixedModelFixedCartanCoordinateRangeStatement_of_regularValue_pPrimaryRoute
      (p := p) (k := k) (G := G) hregular
      (A := A) (K := K) e0
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
      (p := p) (G := G) e0
      (existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hrange)

end CartanFormalRangeRegularValueSourceWorker

end Representation
