import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackInputCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeRegularValueSourceWorker

/-!
Support/value to fixed-row readback boundary for Serre `18.5(a)`.

The literal support/value criterion in `Serre18_5ASupportValueCriterionWorker` proves
projective-character membership for any full class function satisfying Serre's two pointwise
conditions.  It does not, by itself, identify the chosen coordinate-normalized Brauer rows with
the fixed `regularClassCoordinateAddEquiv` rows.

This file records the exact remaining fixed-row input.  No Cartan cokernel/product/Smith/
determinant endpoint is used to manufacture a source-side theorem.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FullMixedSupportValueFixedRowCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedSupportValueFixedRowCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedSupportValueFixedRowCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed form of the literal Serre `18.5(a)` support/value membership criterion.

This is only the membership criterion
`Φ ∈ A ⊗ P_k(G) ↔ support/value conditions`; it carries no fixed-coordinate Brauer-row
readback assertion. -/
def fullMixedModelSerre18_5ALiteralSupportValueCriterion : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∀ Φ : A ⊗R[K](G),
        Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ↔
          (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
            ∀ g : G, IsPRegular p g →
              ∃ a : A, (Φ : G → K) g =
                algebraMap A K ((centralizerPPart p g : A) * a)

omit [IsAlgClosed k] [CharP k p] in
/-- The literal support/value membership criterion is already closed by the source-side
Serre `18.5(a)` API. -/
theorem fullMixedModelSerre18_5ALiteralSupportValueCriterion_holds :
    fullMixedModelSerre18_5ALiteralSupportValueCriterion
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP _e0 Φ
  exact
    mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs_of_enoughRoots
      (p := p) (A := A) (K := K) (G := G) Φ

omit [IsAlgClosed k] [CharP k p] in
/-- Exact boundary: after adding the already-closed support/value membership criterion, the
full regular-value source statement is equivalent to the fixed-coordinate Brauer-basis readback
input.

Thus support/value alone does not close the source statement in the current API; the missing
fixed-row readback lemma is `fullMixedModelBrauerBasisReadbackInput`. -/
theorem fullMixedModelRegularValueSourceStatement_iff_supportValueCriterion_and_fixedRowReadback :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelSerre18_5ALiteralSupportValueCriterion
          (p := p) (k := k) (G := G) ∧
        fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular
    constructor
    · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP _e0 Φ
      exact
        mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs_of_enoughRoots
          (p := p) (A := A) (K := K) (G := G) Φ
    · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueCongruence_via_projectiveEnvelopeResidual
          (p := p) (A := A) (K := K) (G := G)
          (hregular (A := A) (K := K) e0)
  · rintro ⟨_hsupport, hread⟩
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Same boundary with the fixed-row readback input opened to its most explicit nontrivial-column
Brauer-character form.

The missing fixed-row lemma can be stated as
`fullMixedModelBrauerCharacterNontrivialReadbackInput`: in every mixed-characteristic model,
there is a coordinate-normalized family `π` such that for every regular-class row `c` and every
column `d` with nontrivial centralizer `p`-part, the Brauer character row differs from
`Pi.single c 1` by a multiple of `centralizerPPart p d.1`. -/
theorem fullMixedModelRegularValueSourceStatement_iff_supportValueCriterion_and_nontrivialFixedRowReadback :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelSerre18_5ALiteralSupportValueCriterion
          (p := p) (k := k) (G := G) ∧
        fullMixedModelBrauerCharacterNontrivialReadbackInput
          (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular
    constructor
    · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP _e0 Φ
      exact
        mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs_of_enoughRoots
          (p := p) (A := A) (K := K) (G := G) Φ
    · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      have hread :
          regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
            (p := p) (A := A) (G := G) :=
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueCongruence_via_projectiveEnvelopeResidual
          (p := p) (A := A) (K := K) (G := G)
          (hregular (A := A) (K := K) e0)
      exact
        regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
          (p := p) (A := A) (G := G) hread
  · rintro ⟨_hsupport, hnontrivial⟩
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)
        (hnontrivial (A := A) (K := K) e0)
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) hread

omit [IsAlgClosed k] [CharP k p] in
/-- Since the literal Serre `18.5(a)` support/value criterion is already closed, the regular-value
source statement is exactly the fixed-row Brauer-basis readback input. -/
theorem fullMixedModelRegularValueSourceStatement_iff_fixedRowReadback :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueCongruence_via_projectiveEnvelopeResidual
        (p := p) (A := A) (K := K) (G := G)
        (hregular (A := A) (K := K) e0)
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Equivalently, after closing the literal Serre `18.5(a)` membership criterion, the only
remaining source-side input is the nontrivial-column fixed Brauer-character readback. -/
theorem fullMixedModelRegularValueSourceStatement_iff_nontrivialFixedRowReadback :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueCongruence_via_projectiveEnvelopeResidual
        (p := p) (A := A) (K := K) (G := G)
        (hregular (A := A) (K := K) e0)
    exact
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G) hread
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    have hreadModel :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)
        (hread (A := A) (K := K) e0)
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) hreadModel

omit [IsAlgClosed k] [CharP k p] in
/-- The fixed-row readback input is the exact extra source-side ingredient needed to produce the
unconditional input expected by
`existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource`. -/
theorem fullMixedModelRegularValueSourceStatement_of_nontrivialFixedRowReadback
    (hread :
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hreadModel :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) :=
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G)
      (hread (A := A) (K := K) e0)
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hreadModel

include p in
/-- Conditional final adapter from the explicit fixed-row readback lemma.  This calls only the
regular-value source bridge, not a Cartan cokernel/product/Smith/determinant endpoint. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_nontrivialFixedRowReadback
    (hread :
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
    (p := p) (k := k) (G := G)
    (by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      have hreadModel :
          regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
            (p := p) (A := A) (G := G) :=
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
          (p := p) (A := A) (G := G)
          (hread (A := A) (K := K) e0)
      exact
        regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
          (p := p) (A := A) (K := K) (G := G) hreadModel)

end FullMixedSupportValueFixedRowCompletionWorker

end Representation
