import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration

/-!
Audit adapter for the `CartanFormalRange.lean` support gap.

Minimal non-circular import path for the Brauer readback input:

`BrauerReadbackFinalIntegration`
  imports `CartanCokernelProductDirect`,
  which imports `CartanFormalRangeCokernelProductEndpoint`,
  which imports the source-product/formal transport endpoint.

This path does not import `CartanFormalRange.lean`.  The smallest API placement for the final
support theorem is therefore the existing readback endpoint in `BrauerReadbackFinalIntegration`;
this file only re-exports it under an audit-specific name that matches the remaining support gap.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeIntegrationAuditFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeIntegrationAuditFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeIntegrationAuditFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Audit alias: the full mixed Brauer-basis readback input closes the formal Cartan range
support theorem without importing `CartanFormalRange.lean`. -/
theorem cartanFormalRange_support_of_brauerReadbackInput_audit
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelBrauerBasisReadbackInput
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact hread (A := A) (K := K) e0

include p in
/-- Audit alias for the truly minimal direct source-side input. -/
theorem cartanFormalRange_support_of_regularValueCongruenceSourceFaithful_audit
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact hregular (A := A) (K := K) e0

end CartanFormalRangeIntegrationAuditFinal

end Representation
