import Mathlib
import StacksProject_2024.Chap13.Lemma_13_29_1
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap18.Lemma_18_28_8

open CategoryTheory CategoryTheory.Limits CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

local notation "ModCat" => SheafOfModules (ringSheaf J 𝒪)

/-- The object property on `Mod(\mathcal O)` saying that a module is a direct sum, equivalently a
categorical coproduct, of modules of the form `j_{U!}\mathcal O_U`. -/
def isCoproductOfLocalizedStructureModules : CategoryTheory.ObjectProperty ModCat :=
  fun ℱ ↦ ∃ (I : Type u) (U : I → C), Nonempty (ℱ ≅ ∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))

-- Proof sketch: this is immediate from the definition by packaging the displayed coproduct
-- presentation as a witness for the object property.
/-- A chosen coproduct presentation by modules `j_{U!}\mathcal O_U` gives the corresponding object
property. -/
theorem isCoproductOfLocalizedStructureModules_of_iso
    {ℱ : ModCat} {I : Type u} {U : I → C}
    (e : ℱ ≅ ∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :
    isCoproductOfLocalizedStructureModules 𝒪 ℱ := sorry

/-- The zero `\mathcal O`-module is the empty coproduct of localized structure modules. -/
instance isCoproductOfLocalizedStructureModules_containsZero :
    (isCoproductOfLocalizedStructureModules 𝒪).ContainsZero := sorry

/-- Finite coproducts of coproducts of localized structure modules are again coproducts of
localized structure modules. -/
instance isCoproductOfLocalizedStructureModules_isClosedUnderFiniteCoproducts :
    (isCoproductOfLocalizedStructureModules 𝒪).IsClosedUnderFiniteCoproducts := sorry

/-- Every `\mathcal O`-module admits an epimorphism from a coproduct of localized structure
modules. -/
instance isCoproductOfLocalizedStructureModules_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover
      (isCoproductOfLocalizedStructureModules 𝒪) := sorry

-- Proof sketch: use Lemma `18.28.8 (3)` to obtain objectwise epimorphic covers by coproducts of
-- `j_{U!}\mathcal O_U`, feed this object property into Lemma `13.29.1` to get the compatible
-- upper-truncation resolution tower, and then apply exactness of filtered colimits in `Mod(𝒪)`
-- to deduce that the canonical colimit map is a quasi-isomorphism.
/-- Lemma 21.17.10: every complex of `\mathcal O`-modules on a ringed site admits a compatible
upper-truncation resolution tower by bounded-above complexes whose terms and successive degreewise
cokernels are coproducts of modules `j_{U!}\mathcal O_U` such that the canonical morphism from
the sequential colimit of the tower to the original complex is a quasi-isomorphism. -/
theorem exists_upperTruncationResolutionTower_of_localizedStructureModuleCoproducts
    (𝒢 : CochainComplex ModCat ℤ) :
    ∃ T :
        CategoryTheory.UpperTruncationResolutionTower
          (isCoproductOfLocalizedStructureModules 𝒪) 𝒢,
      QuasiIso T.fromColimit := sorry

end

end SheafOfModules.RingedSite
