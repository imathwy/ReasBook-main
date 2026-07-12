import StacksProject_2024.Chap24.Definition_24_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe uC vC uD vD uD' vD'

namespace CategoryTheory.ModulesOnCategory

-- Semantic recall note: `lean_leansearch` recalled the comma-category cofilteredness owner
-- `CostructuredArrow` and the full-subcategory restriction owner `ObjectProperty.lift`; local
-- Section 24.33 precedent identifies `QC(\mathcal A, d)` with the existing Chapter 21/24 owner
-- `QC 𝒜 RGamma derivedRestrict comparison`.

section

variable {C : Type uC} [Category.{vC} C]
variable (C' : ObjectProperty C)
variable {D : Type uD} [Category.{vD} D]
variable {D' : Type uD'} [Category.{vD'} D']
variable (𝒜 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma :
    ∀ U : C,
      D ⥤ DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒜.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒜.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

variable
  (RGammaRes :
    ∀ U' : C'.FullSubcategory,
      D' ⥤ DerivedCategory (ModuleCat (((ObjectProperty.ι C').op ⋙ 𝒜).obj (op U'))))
variable
  (derivedRestrictRes :
    ∀ {U' V' : C'.FullSubcategory}, (U' ⟶ V') →
      DerivedCategory (ModuleCat (((ObjectProperty.ι C').op ⋙ 𝒜).obj (op V'))) ⥤
        DerivedCategory (ModuleCat (((ObjectProperty.ι C').op ⋙ 𝒜).obj (op U'))))
variable
  (comparisonRes :
    ∀ {U' V' : C'.FullSubcategory} (f' : U' ⟶ V'),
      RGammaRes V' ⋙ derivedRestrictRes f' ⟶ RGammaRes U')

/-- Lemma 24.34.1: let `\mathcal C, \mathcal O, \mathcal A` be as in Section `24.33`, and let
`\mathcal C' \subset \mathcal C` be a full subcategory such that for every
`U : \mathcal C` the category `U/\mathcal C'` of arrows `U \to U'` is cofiltered. If
`\mathcal A'` is the restriction of `\mathcal A` to `\mathcal C'`, formalized as
`(ObjectProperty.ι C').op ⋙ \mathcal A`, and if the restriction functor and the colimit
extension construction from the proof preserve the corresponding quasi-coherent objects and are
quasi-inverse on those full subcategories, then restriction induces an equivalence
`QC(\mathcal A, d) \to QC(\mathcal A', d)`. -/
@[stacks 0GZE]
theorem restrictionToCofilteredFullSubcategory_qc_isEquivalence
    (hcofiltered : ∀ U : C, IsCofiltered (CostructuredArrow (ObjectProperty.ι C') U))
    (restriction : D ⥤ D')
    (extension : D' ⥤ D)
    (hrestriction_mem :
      ∀ K : QC 𝒜 RGamma derivedRestrict comparison,
        isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes derivedRestrictRes
          comparisonRes
          ((ObjectProperty.ι (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison) ⋙
              restriction).obj K))
    (hextension_mem :
      ∀ K : QC ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes derivedRestrictRes comparisonRes,
        isQuasiCoherent 𝒜 RGamma derivedRestrict comparison
          ((ObjectProperty.ι
              (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
                derivedRestrictRes comparisonRes) ⋙
              extension).obj K))
    (unitIso :
      𝟭 (QC 𝒜 RGamma derivedRestrict comparison) ≅
        ObjectProperty.lift
            (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
              derivedRestrictRes comparisonRes)
            (ObjectProperty.ι (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison) ⋙
              restriction)
            hrestriction_mem ⋙
          ObjectProperty.lift (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison)
            (ObjectProperty.ι
                (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
                  derivedRestrictRes comparisonRes) ⋙
              extension)
            hextension_mem)
    (counitIso :
      ObjectProperty.lift (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison)
          (ObjectProperty.ι
              (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
                derivedRestrictRes comparisonRes) ⋙
            extension)
          hextension_mem ⋙
        ObjectProperty.lift
          (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
            derivedRestrictRes comparisonRes)
          (ObjectProperty.ι (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison) ⋙
            restriction)
          hrestriction_mem ≅
        𝟭 (QC ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes derivedRestrictRes comparisonRes)) :
    Functor.IsEquivalence
      (ObjectProperty.lift
        (isQuasiCoherent ((ObjectProperty.ι C').op ⋙ 𝒜) RGammaRes
          derivedRestrictRes comparisonRes)
        (ObjectProperty.ι (isQuasiCoherent 𝒜 RGamma derivedRestrict comparison) ⋙ restriction)
        hrestriction_mem) := sorry

end

end CategoryTheory.ModulesOnCategory
