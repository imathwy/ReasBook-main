import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeRegularValueSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.FinalSourceBlockerEquivalenceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASourceTextRouteWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerCharacterPointwiseSourceProofWorker

/-!
Final integration audit for the remaining support theorem in `CartanFormalRange.lean`.

This worker records the shortest conditional closures of
`existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_support`
from the currently isolated source-side inputs.  It is an audit/adapter file only: it does not
modify `CartanFormalRange.lean` and it does not use the downstream Cartan cokernel/product/range
endpoints to manufacture any source-side input.

Import-cycle audit:

* The main bridge is
  `CartanFormalRangeRegularValueSourceWorker.existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource`.
  That file imports `CartanCoordinateDivisibilityClosureWorker` and `CartanRingEquivTransport`,
  not `CartanFormalRange.lean`.
* The four stronger source packages are reduced to
  `fullMixedModelRegularValueSourceStatement` before invoking the main bridge.
* The checked transitive import closure for this worker contains endpoint-labelled infrastructure
  such as `CartanFormalRangeTransport`, `CartanFormalRangeSourceProductTransport`, and
  `CartanFormalRangeCokernelProductEndpoint`, but it does not contain `CartanFormalRange.lean`
  itself.  Therefore importing this worker from `CartanFormalRange.lean` is acyclic, although it is
  not the strictest endpoint-free import set.
* Acyclic patch strategy: if a source theorem is available, import this worker in
  `CartanFormalRange.lean` and replace the open proof gap by the matching adapter below.  If a
  smaller patch is preferred, import only `CartanFormalRangeRegularValueSourceWorker` plus the
  source-side conversion file for the theorem actually obtained.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeFinalSorryIntegrationWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeFinalSorryIntegrationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeFinalSorryIntegrationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Minimal adapter.  Patch strategy if this source theorem is proved: import
`CartanFormalRangeRegularValueSourceWorker` into `CartanFormalRange.lean` and use this bridge
directly. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
    (p := p) (k := k) (G := G) hregular

include p in
/-- Direct Brauer-character row congruence adapter.  Patch strategy: import
`CartanFormalRangeRegularValueSourceWorker` and `FinalSourceBlockerEquivalenceWorker`, then convert
the row congruence to the regular-value source theorem and invoke the minimal adapter. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_brauerCharacterPointwise
    (hpointwise :
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hpointwise (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hpoint⟩
    let hsource :
        regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) :=
      ⟨π, hπ_simple, hπ_coord,
        (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint⟩
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseReadbackSource
          (p := p) (A := A) (G := G) hsource)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

include p in
/-- Projective-character lattice adapter.  Patch strategy: import
`CartanFormalRangeRegularValueSourceWorker` and `RegularValueSourceStatementSourceWorker`; the
lattice theorem is converted to `fullMixedModelRegularValueSourceStatement` without appealing to a
Cartan range endpoint. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_projectiveCharacterLattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
        (hlattice (A := A) (K := K) e0)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

include p in
/-- Serre 18.5(a) source-text adapter.  Patch strategy: import
`CartanFormalRangeRegularValueSourceWorker` and `Serre18_5ASourceTextRouteWorker`; the source-text
theorem first closes the regular-value source theorem. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_serre18_5ASourceText
    (hserre :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hserre (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hpoint⟩
    have hsourcePoint :
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) := by
      refine ⟨π, hπ_simple, hπ_coord, ?_⟩
      exact
        (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsourcePoint
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) hread
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

include p in
/-- Pointwise source API adapter.  Patch strategy: import
`CartanFormalRangeRegularValueSourceWorker`, `FinalSourceBlockerEquivalenceWorker`, and
`BrauerCharacterPointwiseSourceProofWorker`; the API first gives the direct Brauer-character row
congruence, then the regular-value source theorem. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      fullMixedModelBrauerCharacterPointwiseSourceAPI
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    let hpoint :
        regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource_of_brauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)
        (hapi (A := A) (K := K) e0)
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseReadbackSource
          (p := p) (A := A) (G := G) hpoint)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_finalSorry_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

end CartanFormalRangeFinalSorryIntegrationWorker

end Representation
