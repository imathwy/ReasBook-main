import Mathlib
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap31.Definition_31_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "MerModX" => ringedSiteModuleCategory JX (meromorphicFunctionSheaf X)

/-- The same-site `RingCat`-valued structure map underlying
`\mathcal O_X \to \mathcal K_X`. -/
private abbrev toMeromorphicFunctionRingSheafMap :
    ringSheaf JX X.𝒪 ⟶
      ((𝟭 (Opens X.toTopCat)).sheafPushforwardContinuous RingCat.{u} JX JX).obj
        (ringSheaf JX (meromorphicFunctionSheaf X)) :=
  ringedSiteStructureMap
    (C := Opens X.toTopCat)
    (J := JX)
    (𝒪 := X.𝒪)
    (𝒪' := meromorphicFunctionSheaf X)
    X.toMeromorphicFunctionSheafHom

-- Semantic recall: `Definition_31_23_1` already supplies the owner `X.meromorphicFunctionSheaf`
-- for `\mathcal K_X`, and `RingedSiteModuleCategoryBasic` supplies the same-site change-of-rings
-- functors used to form `\mathcal K_X(\mathcal F)` by extension of scalars.

/-- Extension of scalars along `\mathcal O_X \to \mathcal K_X`. -/
noncomputable abbrev meromorphicSectionSheafFunctor : ModX ⥤ MerModX :=
  SheafOfModules.pullback.{u} X.toMeromorphicFunctionRingSheafMap

/-- Definition 31.23.3 (1): for an `\mathcal O_X`-module sheaf `\mathcal F`, the sheaf
`\mathcal K_X(\mathcal F)` of `\mathcal K_X`-modules is obtained by extension of scalars along the
canonical map `\mathcal O_X \to \mathcal K_X`; equivalently, it is the sheafification of
`U \mapsto \mathcal S(U)^{-1}\mathcal F(U)` and the tensor product
`\mathcal F \otimes_{\mathcal O_X} \mathcal K_X`. -/
noncomputable abbrev meromorphicSectionSheaf (ℱ : ModX) : MerModX :=
  (X.meromorphicSectionSheafFunctor).obj ℱ

/-- The sheaf `X.meromorphicSectionSheaf ℱ` is defined by extension of scalars along
`\mathcal O_X \to \mathcal K_X`. -/
@[simp]
theorem meromorphicSectionSheaf_eq_pullback (ℱ : ModX) :
    X.meromorphicSectionSheaf ℱ =
      (SheafOfModules.pullback.{u} X.toMeromorphicFunctionRingSheafMap).obj ℱ := rfl

/-- Definition 31.23.3 (2): a meromorphic section of an `\mathcal O_X`-module sheaf
`\mathcal F` is a global section of `\mathcal K_X(\mathcal F)`. -/
abbrev meromorphicSections (ℱ : ModX) : Type _ :=
  (X.meromorphicSectionSheaf ℱ).sections

/-- Meromorphic sections of `ℱ` are the global sections of `X.meromorphicSectionSheaf ℱ`. -/
@[simp]
theorem meromorphicSections_eq_sections (ℱ : ModX) :
    X.meromorphicSections ℱ = (X.meromorphicSectionSheaf ℱ).sections := rfl

end AlgebraicGeometry.LocallyRingedSpace
