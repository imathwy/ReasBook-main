import StacksProject_2024.stacks_project.Chap04.Lemma_4_43_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_55_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped IdealEtaComplex

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
variable {I : Subobject 𝒪X}
local notation "ℐ" => (I : ModX)

/- Domain-style sampling for Lemma 20.55.9:
- primary domain: cochain complexes of `𝒪X`-modules on a ringed space, together with the
  Berthelot-Ogus construction `η[I]` and exactness of tensoring by an invertible module;
- sampled owner declarations:
  `CategoryTheory.tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`,
  `(tensorRight 𝒢).mapHomologicalComplex (up ℤ)`,
  `idealEtaComplex`,
  `IdealEtaComplex.torsionFreeFunctor`,
  `IsIdealTorsionFreeComplex`,
  `idealEtaComplexAmbientObj`,
  `idealEtaComplexToQuotient`,
  `SatisfiesLocallyPrincipalRegularIdealCondition`,
  `BraidedCategory.tensorLeftIsoTensorRight`;
- best owner abstraction:
  `source-facing`: Lemma `20.55.9`, the compatibility of `η[I]` with tensoring on the right by an
    invertible module;
  `core/canonical`: the already defined Berthelot-Ogus owner
    `IdealEtaComplex.torsionFreeFunctor I` from Lemma `20.55.6`, together with the chapter’s
    invertibility owner `Functor.IsEquivalence (tensorRight 𝒢)` and the canonical complex functor
    `(tensorRight 𝒢).mapHomologicalComplex (up ℤ)`, under the primitive source-facing hypothesis
    `[SatisfiesLocallyPrincipalRegularIdealCondition I]`;
  `bridge/view`: the internal comparison between tensoring `η[I] K hK` on the right and applying
    `η[I]` after right tensoring `K`, whose component at `K` is the complex
    isomorphism comparing
    `((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj (idealEtaComplex I K hK)` with
    `idealEtaComplex I (((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj K) ...`.

Primitive data are therefore imported from Lemma `20.55.5`; this file should not re-own local
copies of `idealEtaComplex`, `IsIdealTorsionFreeComplex`, or the Situation `20.55.2` hypothesis.
Only the source-facing tensor-right comparison for complexes remains public here; any
full-subcategory comparison functor belongs only to the internal proof of that result. -/

section TensorRight

variable (I : Subobject 𝒪X)
variable [SatisfiesLocallyPrincipalRegularIdealCondition I]

private abbrev tensorRightComplex (𝒢 : ModX) : CpxX ⥤ CpxX :=
  (tensorRight 𝒢).mapHomologicalComplex (up ℤ)

section

-- Proof sketch: tensoring on the right by a module whose right tensor functor is an equivalence is
-- exact, hence preserves monomorphisms. Apply this pointwise to the action maps defining
-- `ℐ`-torsion freeness.
namespace IsIdealTorsionFreeComplex

/-- Right tensoring by a module whose right tensor functor is an equivalence preserves
`ℐ`-torsion freeness of cochain complexes. -/
instance tensorRight
    (𝒢 : ModX) (K : CpxX)
    [Functor.IsEquivalence (tensorRight 𝒢)] [IsIdealTorsionFreeComplex I K] :
    IsIdealTorsionFreeComplex I ((tensorRightComplex 𝒢).obj K) := sorry

end IsIdealTorsionFreeComplex

/-- Explicit witness form of `IsIdealTorsionFreeComplex.tensorRight`, for source-facing
comparisons involving `η[I]`. -/
theorem isIdealTorsionFreeComplex_tensorRight
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : IsIdealTorsionFreeComplex I K)
    (𝒢 : ModX) [Functor.IsEquivalence (tensorRight 𝒢)] :
    IsIdealTorsionFreeComplex I ((tensorRightComplex 𝒢).obj K) := by
  sorry

namespace IdealEtaComplex

private noncomputable abbrev tensorRightAmbientIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    (tensorRight 𝒢).obj (idealEtaComplexAmbientObj I K i) ≅
      idealEtaComplexAmbientObj I ((tensorRightComplex 𝒢).obj K) i :=
  α_ ((I : ModX) ^⊗ i) (K.X i) 𝒢

private noncomputable abbrev tensorRightDifferentialTargetIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    (tensorRight 𝒢).obj (idealEtaComplexDifferentialTarget I K i) ≅
      idealEtaComplexDifferentialTarget I ((tensorRightComplex 𝒢).obj K) i :=
  α_ ((I : ModX) ^⊗ i) (K.X (i + 1)) 𝒢

private theorem tensorRightAmbientDifferential_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    CommSq
      (tensorRightAmbientIso I K 𝒢 i).hom
      ((tensorRight 𝒢).map (idealEtaComplexAmbientDifferential I K i))
      (idealEtaComplexAmbientDifferential I ((tensorRightComplex 𝒢).obj K) i)
      (tensorRightDifferentialTargetIso I K 𝒢 i).hom := by
  sorry

private theorem tensorRightNextPowerInclusion_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    CommSq
      (tensorRightAmbientIso I K 𝒢 (i + 1)).hom
      ((tensorRight 𝒢).map (idealEtaComplexNextPowerInclusion I K i))
      (idealEtaComplexNextPowerInclusion I ((tensorRightComplex 𝒢).obj K) i)
      (tensorRightDifferentialTargetIso I K 𝒢 i).hom := by
  sorry

private noncomputable def tensorRightQuotientIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    (tensorRight 𝒢).obj (idealEtaComplexQuotientTarget I K i) ≅
      idealEtaComplexQuotientTarget I ((tensorRightComplex 𝒢).obj K) i :=
  (PreservesCokernel.iso (tensorRight 𝒢) (idealEtaComplexNextPowerInclusion I K i)) ≪≫
    cokernel.mapIso
      ((tensorRight 𝒢).map (idealEtaComplexNextPowerInclusion I K i))
      (idealEtaComplexNextPowerInclusion I ((tensorRightComplex 𝒢).obj K) i)
      (tensorRightAmbientIso I K 𝒢 (i + 1))
      (tensorRightDifferentialTargetIso I K 𝒢 i)
      (tensorRightNextPowerInclusion_commSq I K 𝒢 i).w.symm

private theorem tensorRightToQuotient_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) (i : ℤ) :
    CommSq
      (tensorRightAmbientIso I K 𝒢 i).hom
      ((tensorRight 𝒢).map (idealEtaComplexToQuotient I K i))
      (idealEtaComplexToQuotient I ((tensorRightComplex 𝒢).obj K) i)
      (tensorRightQuotientIso I K 𝒢 i).hom := by
  sorry

private noncomputable def tensorRightObjIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (𝒢 : ModX) [Functor.IsEquivalence (tensorRight 𝒢)] (i : ℤ) :
    (tensorRight 𝒢).obj (idealEtaComplexObj I K i) ≅
      idealEtaComplexObj I ((tensorRightComplex 𝒢).obj K) i :=
  let _ : PreservesFiniteLimits (tensorRight 𝒢) := by
    let _ : Functor.IsEquivalence (tensorLeft 𝒢) :=
      (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence 𝒢).2 inferInstance
    exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight 𝒢)
  (PreservesKernel.iso (tensorRight 𝒢) (idealEtaComplexToQuotient I K i)) ≪≫
    kernel.mapIso
      ((tensorRight 𝒢).map (idealEtaComplexToQuotient I K i))
      (idealEtaComplexToQuotient I ((tensorRightComplex 𝒢).obj K) i)
      (tensorRightAmbientIso I K 𝒢 i)
      (tensorRightQuotientIso I K 𝒢 i)
      (tensorRightToQuotient_commSq I K 𝒢 i).w.symm

private theorem tensorRightObjIso_comm
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : IsIdealTorsionFreeComplex I K)
    (𝒢 : ModX) [Functor.IsEquivalence (tensorRight 𝒢)]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (tensorRightObjIso I K 𝒢 i).hom ≫
        ((η[I] ((tensorRightComplex 𝒢).obj K)
          (isIdealTorsionFreeComplex_tensorRight I K hK 𝒢)).d i j) =
      (((tensorRightComplex 𝒢).obj (η[I] K hK)).d i j) ≫
        (tensorRightObjIso I K 𝒢 j).hom := by
  sorry

/-- Lemma 20.55.9: tensoring a complex of `ℐ`-torsion free `𝒪X`-modules on the right by a module
whose right tensor functor is an equivalence commutes with the Berthelot-Ogus construction
`η[I]`, up to isomorphism. -/
@[stacks 0F9W]
noncomputable def tensorRightIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : IsIdealTorsionFreeComplex I K)
    (𝒢 : ModX) [Functor.IsEquivalence (tensorRight 𝒢)] :
    (((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj (η[I] K hK)) ≅
      (η[I] (((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj K)
        (isIdealTorsionFreeComplex_tensorRight I K hK 𝒢)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ tensorRightObjIso I K 𝒢 i)
    (fun i j hij ↦ tensorRightObjIso_comm I K hK 𝒢 i j hij)

/-- Lemma 20.55.9, companion form: the canonical comparison isomorphism `tensorRightIso` yields
an `IsIsomorphic` witness for the two complexes. -/
@[stacks 0F9W]
theorem tensorRight_isomorphic
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : IsIdealTorsionFreeComplex I K)
    (𝒢 : ModX) [Functor.IsEquivalence (tensorRight 𝒢)] :
    IsIsomorphic
      (((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj (η[I] K hK))
      (η[I] (((tensorRight 𝒢).mapHomologicalComplex (up ℤ)).obj K)
        (isIdealTorsionFreeComplex_tensorRight I K hK 𝒢)) := by
  exact ⟨tensorRightIso I K hK 𝒢⟩

end IdealEtaComplex

end

end TensorRight

end AlgebraicGeometry.RingedSpace
