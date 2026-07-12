import StacksProject_2024.Chap13.Proposition_13_39_2
import StacksProject_2024.Chap21.Lemma_21_43_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe uC vC uD' vD'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type uC} [Category.{vC} C]
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{uC})

local notation "Ring𝒜" => 𝒜 ⋙ forget₂ CommRingCat RingCat
local notation "DModA" => DerivedCategory (PresheafOfModules Ring𝒜)

variable [HasZeroObject DModA] [HasShift DModA ℤ] [Preadditive DModA]
variable [∀ n : ℤ, (shiftFunctor DModA n).Additive]
variable [Pretriangulated DModA] [IsTriangulated DModA] [HasCoproducts.{uC} DModA]
variable
  (RGamma :
    ∀ U : C,
      DModA ⥤ DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒜.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable [∀ U : C, (RGamma U).CommShift ℤ]
variable [∀ U : C, (RGamma U).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).CommShift ℤ]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ]

local notation "QCP" => isQuasiCoherent 𝒜 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒜 RGamma derivedRestrict comparison
local notation "ιQC" => ObjectProperty.ι QCP

variable [HasZeroObject QCoh] [HasShift QCoh ℤ] [Preadditive QCoh]
variable [∀ n : ℤ, (shiftFunctor QCoh n).Additive]
variable [Pretriangulated QCoh] [IsTriangulated QCoh] [HasCoproducts.{max uC vC} QCoh]

local notation "brownSetQC" =>
  let ⟨κ, hsmall, hfactor⟩ :=
    exists_cardinal_for_small_sources_and_countable_coproduct_factorizations
      𝒜 RGamma derivedRestrict comparison
  ⟨boundedObjects 𝒜 RGamma derivedRestrict comparison κ,
    boundedObjects_isBrownRepresentabilitySet
      𝒜 RGamma derivedRestrict comparison hsmall hfactor⟩

variable (H : QCohᵒᵖ ⥤ AddCommGrpCat.{max uC vC})
variable (hH : H.rightOp.IsHomological)
variable (hprod : ∀ J : Type (max uC vC), PreservesLimitsOfShape (Discrete J) H)

/- Remark 24.33.3 (1): in the differential-graded setting of Definition `24.33.1`, Brown
representability for `QC(\mathcal A, d)` is obtained by combining the Section `21.43` Brown-set
bridge with the canonical Chapter `13` Brown representability theorem. -/
#check
  match brownSetQC with
  | ⟨S, hS⟩ => brown_representability_of_detecting_factorization_set S hS H hH hprod

section RightAdjoints

variable {D' : Type uD'} [Category.{vD'} D']
variable [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
variable [∀ n : ℤ, (shiftFunctor D' n).Additive]
variable [Pretriangulated D'] [IsTriangulated D']

variable (F : QCoh ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
variable [∀ J : Type (max uC vC), PreservesColimitsOfShape (Discrete J) F]

/- Remark 24.33.3 (2): every exact coproduct-preserving functor out of `QC(\mathcal A, d)` is a
left adjoint; this is the canonical Chapter `13` owner specialized using the Section `21.43`
Brown-set bridge. -/
#check exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F brownSetQC

/- Remark 24.33.3 (2), exact-right-adjoint companion: the chosen right adjoint is triangulated. -/
#check exactFunctor_hasExactRightAdjoint_of_exists_brownRepresentabilitySet F brownSetQC

end RightAdjoints

variable [∀ J : Type (max uC vC), ∀ U : C, PreservesColimitsOfShape (Discrete J) (RGamma U)]
variable [∀ J : Type (max uC vC),
  ∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete J) (derivedRestrict f)]

/- Remark 24.33.3 (3): the inclusion functor `QC(\mathcal A, d) ↪ D(\mathcal A, d)` is a left
adjoint; this is the same Chapter `13` owner applied to the canonical inclusion `ιQC`. -/
#check exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet ιQC brownSetQC

/- Remark 24.33.3 (3), exact-right-adjoint companion: the chosen right adjoint to the inclusion
functor is triangulated. -/
#check exactFunctor_hasExactRightAdjoint_of_exists_brownRepresentabilitySet ιQC brownSetQC

end

end CategoryTheory.ModulesOnCategory
