import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeRegularValueSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceTextProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker

/-!
Support/value route audit for the Cartan formal range.

This worker keeps the source-side route explicit.  The literal Serre `18.5(a)` support/value
criterion is already formalized, but the regular-value source statement is equivalent to the
remaining Exercise `18.4` point-mass row readback congruence.  The final formal-range adapter below
uses the non-product `regularValueSource` bridge.
-/

noncomputable section

set_option linter.style.longLine false

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalSupportValueToFormalRangeWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance supportValueToFormalRangeWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance supportValueToFormalRangeWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local exact boundary: the needed regular-value congruence is equivalent to the literal
support/value row package to which Serre `18.5(a)` applies. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_sourceTextSupportValueRows_worker :
    regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) ↔
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)).symm.trans
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G))

end LocalSupportValueToFormalRangeWorker

section FullMixedSupportValueToFormalRangeWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedSupportValueToFormalRangeWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedSupportValueToFormalRangeWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed package saying only that the literal Serre `18.5(a)` support/value criterion is
available in every mixed-characteristic model.  This statement is closed unconditionally. -/
def fullMixedModelSerre18_5ASupportValueCriterion : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      serre18_5aSourceTextSupportValueCriterion
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The formalized Serre `18.5(a)` support/value criterion holds in every full mixed model. -/
theorem fullMixedModelSerre18_5ASupportValueCriterion_holds :
    fullMixedModelSerre18_5ASupportValueCriterion
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP _e0
  exact
    serre18_5aSourceTextSupportValueCriterion_holds
      (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact boundary: the requested regular-value source statement is equivalent to the
named Serre `18.5(a)` source-text point-mass readback theorem. -/
theorem fullMixedModelRegularValueSourceStatement_iff_serre18_5aSourceTextTheorem_worker :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G) :=
  (fullMixedModelSerre18_5ASourceTextTheorem_iff_regularValueSourceStatement
    (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- The same boundary opened to the direct Brauer-character pointwise readback congruence. -/
theorem fullMixedModelRegularValueSourceStatement_iff_brauerCharacterPointwiseReadback_worker :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceStatement_iff_brauerCharacterPointwiseReadbackCongruence_sourceClosure
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact boundary to the literal Serre `18.5(a)` support/value row API.  This is
the source-side form before opening the remaining point-mass row readback congruence. -/
theorem fullMixedModelRegularValueSourceStatement_iff_sourceTextSupportValueRows_worker :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_sourceTextSupportValueAPI
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The source-faithful spelling of the same full mixed target has the same direct pointwise
readback boundary.  The proof does not use a Cartan product endpoint; the two full mixed
regular-value statements are definitionally the same predicate. -/
theorem fullMixedRegularValueSourceFaithful_iff_pointwiseReadback_worker :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) := by
  change fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
    fullMixedModelBrauerCharacterPointwiseReadbackCongruence
      (p := p) (k := k) (G := G)
  exact
    fullMixedModelRegularValueSourceStatement_iff_brauerCharacterPointwiseReadback_worker
      (p := p) (k := k) (G := G)

include p in
/-- Conditional formal-range closure from the regular-value source statement, using the
non-product bridge isolated in `CartanFormalRangeRegularValueSourceWorker`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource_worker
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
    (p := p) (k := k) (G := G) hregular

end FullMixedSupportValueToFormalRangeWorker

end Representation
