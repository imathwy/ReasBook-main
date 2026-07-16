import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Sections_on_open
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_extension_derived

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped TopCat

noncomputable section

universe u w

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier)
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]
variable [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]

local notation "ModX" => X.Modules
local notation "ModU" => openSubspaceModuleCategory X U
local notation "DModU" => moduleDerivedOnOpen X U
local notation "DExtU" => moduleExtensionByZeroFromOpenDerived X U
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "single0X" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "single0U" => DerivedCategory.singleFunctor ModU (0 : ℤ)

local instance : IsGrothendieckAbelian.{u} ModX := sheafModules_isGrothendieckAbelian X

/- Domain-style sampling for Lemma 20.53.1:
- primary domain: compactness of `j_! 𝒪_U[0]` in the derived category of `𝒪_X`-modules for the
  inclusion of an open subset `j : U ↪ X`;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `DerivedCategory.singleFunctor`,
  `SheafOfModules.unit`,
  `moduleCohomologyAtOpen`,
  `moduleCohomologyDegreeAtOpenFunctor`,
  `moduleExtensionByZeroFromOpen`;
- best owner abstraction:
  `source-facing`: compactness of the degree-zero object attached to the extension by zero of the
    structure module on the restricted ringed space `X.restrict U.isOpenEmbedding`;
  `core/canonical`: `CategoryTheory.IsCompactObject` applied to
    `((single0X).obj ((moduleExtensionByZeroFromOpen X U).obj
      ((moduleRestrictionToOpen X U).obj 𝒪X)))`;
  `bridge/view`: the Chapter 20 open-cohomology owners `moduleCohomologyAtOpen U` and
    `moduleCohomologyDegreeAtOpenFunctor U`.
-/

-- Semantic recall note: `lean_leansearch` did not surface a usable ambient owner for this open
-- immersion statement, so the file uses the verified Chapter 20 owners
-- `moduleCohomologyAtOpen U`, `moduleCohomologyDegreeAtOpenFunctor U`, and
-- `moduleExtensionByZeroFromOpen X U`.

/-- Public bridge owner for Lemma 20.53.1: the degree-`p` cohomology functor on the open subset
`U`, valued in `Γ(U, 𝒪_X)`-modules. -/
noncomputable abbrev moduleCohomologyDegreeAtOpenFunctor (p : ℕ) :
    ModX ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  let _ : (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).Additive :=
    moduleSectionsEvaluation_additive X U
  (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).rightDerived p

/-- Lemma 20.53.1: let `j : U ↪ X` be the inclusion of an open subset of a ringed space. If there
exists an integer `d` such that `H^p(U, ℱ) = 0` for all `p > d` and all `𝒪_X`-modules `ℱ`, and if
each functor `ℱ ↦ H^p(U, ℱ)` commutes with arbitrary direct sums, then the degree-zero object
attached to the extension by zero `j_! 𝒪_U` is a compact object of `D(𝒪_X)`. -/
@[stacks 0F5Z]
theorem structureModule_degreeZero_isCompactObject_of_finiteCohomologicalDimension
    (hvanish :
      ∃ d : ℤ,
        ∀ p : ℕ, d < p → ∀ ℱ : ModX,
          IsZero (moduleCohomologyAtOpen U ℱ p))
    (hcomm :
      ∀ (p : ℕ) (ι : Type w),
        PreservesColimitsOfShape (Discrete ι)
          (moduleCohomologyDegreeAtOpenFunctor U p)) :
    IsCompactObject
      ((single0X).obj
        ((moduleExtensionByZeroFromOpen X U).obj ((moduleRestrictionToOpen X U).obj 𝒪X))) := sorry

end

end AlgebraicGeometry.RingedSpace
