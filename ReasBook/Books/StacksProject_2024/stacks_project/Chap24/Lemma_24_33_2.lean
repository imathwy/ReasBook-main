import StacksProject_2024.Chap21.Lemma_21_43_2
import StacksProject_2024.Chap24.Definition_24_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe uC vC

namespace CategoryTheory.ModulesOnCategory

-- Semantic recall note: `lean_leansearch` surfaced the canonical owner predicates
-- `CategoryTheory.ObjectProperty.IsTriangulated` and
-- `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`; the actual Section `24.33`
-- specialization below was then verified against the existing source-facing Chapter 21 file
-- `Chap21/Lemma_21_43_2.lean` and the Chapter 24 owner recall `Chap24/Definition_24_33_1.lean`.

section

variable {C : Type uC} [Category.{vC} C]
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{uC})

local notation "Ring𝒜" => 𝒜 ⋙ forget₂ CommRingCat RingCat
local notation "DModA" => DerivedCategory (PresheafOfModules Ring𝒜)

variable [HasZeroObject DModA] [HasShift DModA ℤ] [Preadditive DModA]
variable [∀ n : ℤ, (shiftFunctor DModA n).Additive]
variable [Pretriangulated DModA]
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

/- Lemma 24.33.2: in the Section `24.33` differential-graded module situation, the subcategory
`QC(\mathcal A, d)` is obtained by specializing the existing Chapter `21` source-facing owner
`QC`; the four asserted closure properties are therefore direct recalls of its canonical owner
instances. -/

/- Lemma 24.33.2 (1): `QC(\mathcal A, d)` is strictly full in `D(\mathcal A, d)`. -/
#check qc_isClosedUnderIsomorphisms 𝒜 RGamma derivedRestrict comparison

/- Lemma 24.33.2 (2): `QC(\mathcal A, d)` is saturated in `D(\mathcal A, d)`. -/
#check qc_isStableUnderRetracts 𝒜 RGamma derivedRestrict comparison

/- Lemma 24.33.2 (3): `QC(\mathcal A, d)` is triangulated. -/
#check qc_isTriangulated 𝒜 RGamma derivedRestrict comparison

/- Lemma 24.33.2 (4): `QC(\mathcal A, d)` is preserved by arbitrary direct sums. -/
#check qc_isClosedUnderDirectSums 𝒜 RGamma derivedRestrict comparison

end

end CategoryTheory.ModulesOnCategory
