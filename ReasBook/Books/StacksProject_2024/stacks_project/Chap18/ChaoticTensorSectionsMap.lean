import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The canonical base-change map on sections of an `𝒪`-module over the chaotic site, from
`ℱ(V) ⊗[𝒪(V)] 𝒪(U)` to `ℱ(U)`. -/
noncomputable abbrev chaoticTensorSectionsMap
    (ℱ : ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) {U V : C} (f : U ⟶ V) :
    (ModuleCat.extendScalars ((𝒪.1.map f.op).hom)).obj (ℱ.1.obj (op V)) ⟶
      ℱ.1.obj (op U) :=
  ((ModuleCat.extendRestrictScalarsAdj ((𝒪.1.map f.op).hom)).homEquiv _ _).symm
    (ℱ.1.map f.op)

/-- The canonical sectionwise tensor map is adjoint to the restriction map of `ℱ`. -/
theorem chaoticTensorSectionsMap_def
    (ℱ : ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) {U V : C} (f : U ⟶ V) :
    chaoticTensorSectionsMap 𝒪 ℱ f =
      ((ModuleCat.extendRestrictScalarsAdj ((𝒪.1.map f.op).hom)).homEquiv _ _).symm
        (ℱ.1.map f.op) := rfl

end SheafOfModules
