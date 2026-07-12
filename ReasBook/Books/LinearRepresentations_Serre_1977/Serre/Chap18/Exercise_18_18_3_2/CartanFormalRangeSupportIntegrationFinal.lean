import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerReadbackNonCircularCompletion
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerInversePointMassSourceClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRegularValueWitnessSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueSourceCompletion
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.SourceProductSmithCompletion

/-!
Final non-circular integration adapters for the Cartan formal range support gap.

This file deliberately does not import `CartanFormalRange.lean`.  The direct minimal input is
`fullMixedModelRegularValueCongruenceSourceFaithfulStatement`; stronger source-side packages are
recorded below only as convenience adapters into the same endpoint.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeSupportIntegrationFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeSupportIntegrationFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeSupportIntegrationFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Minimal direct source-input replacement for
`existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_support`.

Input needed: the full mixed-model source-faithful regular-value congruence.  The proof is the
already compiled non-circular route
regular-value congruence `→` abstract Cartan cokernel product `→` diagonal Cartan range. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceInputs_final
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
    (p := p) (k := k) (G := G) hregular

include p in
/-- Same minimal bridge, using the source-product route's name for the same regular-value
congruence input. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_regularValueSource_final
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceInputs_final
    (p := p) (k := k) (G := G) hregular

include p in
/-- Brauer-readback version of the final bridge.

Input needed: `fullMixedModelBrauerBasisReadbackInput`.  This is stronger than the direct
regular-value input because readback supplies the source-faithful regular-value congruence in
every full mixed model. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_brauerReadback_final
    (hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceInputs_final
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

include p in
/-- Projective-character lattice version of the final bridge.

Input needed: `fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence`.  The
bridge rewrites Serre's projective-character lattice congruence as the source-faithful
regular-value congruence before invoking the minimal final endpoint. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_final
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceInputs_final
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G) hlattice)

include p in
/-- Point-mass projective-row version of the final bridge.

Input needed: `fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput`, the smaller
row package isolated in `RegularValueSourceCompletion`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassProjectiveRows_final
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceInputs_final
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_pointMassProjectiveRows
      (p := p) (k := k) (G := G) hrows)

include p in
/-- Row-divisibility version of the final bridge.

Input needed: `fullMixedModelPointMassRegularValueWitnessBlocker`, the fixed-coordinate
row-difference divisibility form closest to Serre `18.5(a)`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassRegularValueWitness_final
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassProjectiveRows_final
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_regularValueWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

include p in
/-- Direct row-submodule version of the final bridge.

Input needed: `fullMixedModelPointMassRowsInRegularValueSubmoduleInput`, the smallest current
row-divisibility form of Serre `18.5(a)`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassRows_final
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassRegularValueWitness_final
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassRegularValueWitnessBlocker_of_pointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) hrows)

include p in
/-- Orthogonality-source version of the final bridge.

Input needed: the explicit Exercise `18.4` / Brauer orthogonality residual package.  This is the
current smallest A-side source form feeding the final Cartan-range support bridge. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pairingResidualOrthogonality_final
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_pointMassRows_final
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_orthogonalityInput
      (p := p) (k := k) (G := G) horth)

include p in
/-- Inverse-Brauer point-mass version of the final bridge.

Input needed: `fullMixedModelBrauerInversePointMassSourceInput`, the source-side point-mass
congruence equivalent to the regular-value source statement. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_brauerInversePointMass_final
    (hinv :
      fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_regularValueSource_final
    (p := p) (k := k) (G := G)
    (fullMixedModelRegularValueSourceStatement_of_brauerInversePointMassSourceInput
      (p := p) (k := k) (G := G) hinv)

include p in
/-- Non-circular readback closure from the projective-character lattice input. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_readback_final
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_brauerReadback_final
    (p := p) (k := k) (G := G)
    (@fullMixedModelBrauerBasisReadbackInput_of_projectiveCharacter_lattice_nonCircular.{u}
      p k inferInstance G inferInstance inferInstance inferInstance hlattice)

include p in
/-- Serre-basis source-representative version of the final bridge.

Input needed: forward and reverse integer representatives modulo Serre's regular-value
divisibility lattice, packaged as
`fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_serreBasisSourceRepresentatives_final
    (hreps :
      fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterCokernelProduct
      (p := p) (k := k) (G := G)
      (@fullMixedModelCartanCokernelProductStatement_of_serreBasisIntegerRepresentativesModuloD.{u}
        p k inferInstance G inferInstance inferInstance inferInstance hreps)

include p in
/-- Projective-character forward plus reverse source-representative version of the final bridge.

Input needed: `fullMixedModelProjectiveCharacterLatticeReverseSourceStatement`, i.e. the
projective-character lattice representative congruence together with reverse source
representatives for every integer regular-class function. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_sourceRepresentatives_final
    (hsource :
      fullMixedModelProjectiveCharacterLatticeReverseSourceStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have himage :
      fullMixedModelCanonicalSourceProductImageStatement
        (p := p) (k := k) (G := G) :=
    fullMixedModelCanonicalSourceProductImageStatement_of_projectiveCharacterLattice_reverseSource
      (p := p) (k := k) (G := G) hsource
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterCokernelProduct
      (p := p) (k := k) (G := G)
      (@fullMixedModelCartanCokernelProductStatement_of_canonicalSourceProductImage.{u}
        p k inferInstance G inferInstance inferInstance inferInstance himage)

include p in
/-- Projective-witness source-representative version of the final bridge. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveWitnessSourceRepresentatives_final
    (hwitness :
      fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_serreBasisSourceRepresentatives_final
    (p := p) (k := k) (G := G)
    (fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_projectiveWitness
      (p := p) (k := k) (G := G) hwitness)

end CartanFormalRangeSupportIntegrationFinal

end Representation
