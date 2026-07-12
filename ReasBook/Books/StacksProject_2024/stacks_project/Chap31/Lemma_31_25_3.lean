import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap29.Definition_29_49_6
import StacksProject_2024.Chap31.Definition_31_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "KX" => X.meromorphicFunctionSheaf
local notation "toAdditiveSheaf" =>
  (SheafOfModules.toSheaf
    (SheafOfModules.RingedSite.ringSheaf JX KX))

-- Semantic recall: `lean_leansearch` and local Chapter 6 precedent fix
-- `CategoryTheory.constantSheaf` as the canonical constant-sheaf owner, while Chapter 31 already
-- uses `SheafOfModules.toSheaf` to pass from module sheaves to their underlying additive sheaves.

/-- Lemma 31.25.3 (1): if `X` is an integral scheme, then the sheaf of meromorphic functions
`\mathcal K_X` is isomorphic to the constant sheaf on `X` with value the function field
`R(X) = X.functionField`. -/
@[stacks 01X5]
theorem meromorphicFunctionSheafIsomorphicToConstantFunctionField :
    IsIsomorphic KX ((constantSheaf JX CommRingCat).obj X.functionField) := sorry

/-- Companion to Lemma 31.25.3 (1): on an integral scheme, the sheaf of meromorphic functions is
constant. -/
theorem meromorphicFunctionSheaf_isConstant :
    Sheaf.IsConstant JX KX := by
  classical
  exact Sheaf.isConstant_of_iso JX
    (Classical.choice meromorphicFunctionSheafIsomorphicToConstantFunctionField)

/-- Lemma 31.25.3 (2): if `X` is an integral scheme and `\mathcal F` is a quasi-coherent
`\mathcal O_X`-module, then the underlying additive sheaf of meromorphic sections
`\mathcal K_X(\mathcal F)` is isomorphic to the constant sheaf with value the generic stalk
`\mathcal F_\eta`, where `\eta = genericPoint X`. -/
@[stacks 01X5]
theorem meromorphicSectionUnderlyingSheafIsomorphicToConstantGenericStalk
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((toAdditiveSheaf).obj (X.meromorphicSectionSheaf ℱ))
      ((constantSheaf JX AddCommGrpCat).obj
        (AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ (genericPoint X)))) := sorry

/-- Companion to Lemma 31.25.3 (2): for a quasi-coherent `\mathcal O_X`-module on an integral
scheme, the underlying additive sheaf of meromorphic sections is constant. -/
theorem meromorphicSectionUnderlyingSheaf_isConstant
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Sheaf.IsConstant JX ((toAdditiveSheaf).obj (X.meromorphicSectionSheaf ℱ)) := by
  classical
  exact Sheaf.isConstant_of_iso JX
    (Classical.choice
      (meromorphicSectionUnderlyingSheafIsomorphicToConstantGenericStalk ℱ))

end AlgebraicGeometry.Scheme
