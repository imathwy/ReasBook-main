import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SupportValueToFormalRangeWorker

/-!
Direct support/value boundary for the Cartan formal range target.

The literal Serre `18.5(a)` criterion is already closed: it recognizes which full
class functions lie in the projective-character submodule from support and value
divisibility.  What it does not construct by itself is the full residual-row
representative package for the coordinate-normalized Brauer rows.  This file keeps
that remaining input explicit and then sends it through the non-product
regular-value source bridge.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section SupportValueDirectFormalRangeCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance supportValueDirectFormalRangeCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance supportValueDirectFormalRangeCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The already closed literal Serre `18.5(a)` support/value criterion, restated here as the
starting point for this worker. -/
theorem fullMixedModelSerre18_5ASupportValueCriterion_direct_holds :
    fullMixedModelSerre18_5ASupportValueCriterion
      (p := p) (k := k) (G := G) :=
  fullMixedModelSerre18_5ASupportValueCriterion_holds
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Name for the exact extra row/descent input not supplied by the pointwise membership
criterion alone: every residual row has a full class-function representative satisfying the two
support/value hypotheses of Serre `18.5(a)`. -/
def fullMixedModelSerre18_5ASupportValueRowsDescent : Prop :=
  fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Explicit blocker form for the support/value rows descent: constructing the full residual
row representatives closes the row/descent target.  This is the missing source-side input, not
a Cartan endpoint. -/
theorem fullMixedModelSerre18_5ASupportValueRowsDescent_of_pointMassResidualFullRepresentativeBlocker
    (hblock :
      fullMixedModelPointMassResidualFullRepresentativeBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelSerre18_5ASupportValueRowsDescent
      (p := p) (k := k) (G := G) := by
  change
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G)
  change
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G)
  exact
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_fullRepresentativeBlocker
      (p := p) (k := k) (G := G) hblock

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the row/descent package supplies the same visible full-representative blocker:
Serre `18.5(a)` turns the support/value representatives into projective-restriction witnesses,
and the visible residual-row representative API is just that witness with the row unfolded. -/
theorem fullMixedModelPointMassResidualFullRepresentativeBlocker_of_serre18_5ASupportValueRowsDescent
    (hrows :
      fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassResidualFullRepresentativeBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) := by
    change
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) at hrows
    exact hrows
  rcases hsource (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hsupport⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases hsupport c with ⟨Φ, hzero, hvalue, hres⟩
  refine ⟨Φ, ?_, hres⟩
  exact
    mem_projectiveCharacterSubmodule_of_serre18_5a_rhs_of_enoughRoots
      (p := p) (A := A) (K := K) (G := G) hzero hvalue

omit [IsAlgClosed k] [CharP k p] in
/-- Exact formal blocker for the direct support/value route.  The non-equivalence provider above
is the usable closure direction; this statement records that no weaker row API is hidden in the
current definitions. -/
theorem fullMixedModelSerre18_5ASupportValueRowsDescent_iff_pointMassResidualFullRepresentativeBlocker :
    fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassResidualFullRepresentativeBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassResidualFullRepresentativeBlocker_of_serre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelSerre18_5ASupportValueRowsDescent_of_pointMassResidualFullRepresentativeBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The row/descent input is exactly the regular-value source statement used by the existing
non-product formal-range bridge. -/
theorem fullMixedModelSerre18_5ASupportValueRowsDescent_iff_regularValueSourceStatement :
    fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  simpa [fullMixedModelSerre18_5ASupportValueRowsDescent] using
    (fullMixedModelRegularValueSourceStatement_iff_sourceTextSupportValueRows_worker
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Direct source-side use of Serre `18.5(a)`: once the residual support/value rows are
available, they close the projective-character lattice congruence. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_supportValueRowsDescent_direct
    (hrows :
      fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  change
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G) at hrows
  exact
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
      (p := p) (k := k) (G := G) hrows

omit [IsAlgClosed k] [CharP k p] in
/-- The same bridge in the exact source statement expected by
`CartanFormalRangeRegularValueSourceWorker`. -/
theorem fullMixedModelRegularValueSourceStatement_of_supportValueRowsDescent_direct
    (hrows :
      fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelSerre18_5ASupportValueRowsDescent_iff_regularValueSourceStatement
    (p := p) (k := k) (G := G)).1 hrows

include p in
/-- Strongest direct formal-range completion available from the closed Serre `18.5(a)`
criterion without fixed-row readback.

The remaining hypothesis is precisely the residual-row support/value descent package above; no
Cartan cokernel/product/Smith/determinant endpoint is used to prove that source-side input here.
-/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_supportValueRowsDescent_direct
    (hrows :
      fullMixedModelSerre18_5ASupportValueRowsDescent
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource_worker
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueSourceStatement_of_supportValueRowsDescent_direct
      (p := p) (k := k) (G := G) hrows)

include p in
/-- Entailment form of the missing bridge: if the closed membership criterion were accompanied by
a proof that it constructs the residual support/value row package, then the target `∃ e` follows.

This theorem isolates the minimum absent implication in the current API. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_supportValueCriterion_to_rowsDescent_direct
    (hdescent :
      fullMixedModelSerre18_5ASupportValueCriterion
          (p := p) (k := k) (G := G) →
        fullMixedModelSerre18_5ASupportValueRowsDescent
          (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_supportValueRowsDescent_direct
    (p := p) (k := k) (G := G)
    (hdescent
      (fullMixedModelSerre18_5ASupportValueCriterion_direct_holds
        (p := p) (k := k) (G := G)))

end SupportValueDirectFormalRangeCompletionWorker

end Representation
