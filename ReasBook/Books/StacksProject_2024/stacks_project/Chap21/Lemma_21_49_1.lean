import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap20.Definition_20_46_1
import StacksProject_2024.Chap21.Lemma_21_20_5_core

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

open RingedSite.Hom

variable (X : RingedSite.{u, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X.siteTopology.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

local notation "Mod" => SheafOfModules X.structureSheaf
local notation "ΓX" => globalSectionsRing X
local notation "ModΓX" => ModuleCat ΓX
local notation "ΓMod" => (moduleGlobalSectionsFunctor X : Mod ⥤ ModΓX)
local notation "FiniteProjectivesΓX" => finiteProjectiveModuleProperty ΓX

/- Domain-style sampling for Lemma 21.49.1:
- primary domain: sheaves of modules on a commutative ringed site, retracts of finite free
  modules, and finite projective modules over the ring of global sections;
- sampled owner declarations:
  `SheafOfModules.finiteFreeRetractModuleProperty`,
  `ObjectProperty.retractClosure`,
  `RingedSite.Hom.moduleGlobalSectionsFunctor`,
  `RingedSite.Hom.globalSectionsRing`,
  `FiniteProjectiveModuleCat`;
- best owner abstraction:
  `source-facing`: the module-valued global-sections functor
    `Γ(X, -) : Mod(𝒪_X) ⥤ Mod(Γ(X, 𝒪_X))`, restricted to
    the full subcategory of finite-free retracts;
  `core/canonical`: the retract owner
    `SheafOfModules.finiteFreeRetractModuleProperty` on `SheafOfModules X.structureSheaf`, the
    global-sections ring `RingedSite.Hom.globalSectionsRing X`, the module-valued owner
    `RingedSite.Hom.moduleGlobalSectionsFunctor X`, and the module property
    `finiteProjectiveModuleProperty`;
  `bridge/view`: the lifted functor into `FiniteProjectiveModuleCat (globalSectionsRing X)`.
- primitive data: the ringed site `X` and the global sections ring
  `Γ(X, 𝒪_X)`;
- derived API: the finite-projective membership companion, the restricted global-sections functor,
  and the equivalence statement.
-/

/-- Helper for Lemma 21.49.1: global sections of a finite-free-retract `𝒪_X`-module form a finite
projective module over `Γ(X, 𝒪_X)`. -/
private theorem moduleGlobalSections_mem_finiteProjectiveModuleProperty
    (ℱ : (SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf).FullSubcategory) :
    FiniteProjectivesΓX
      (((SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf).ι ⋙ ΓMod).obj ℱ) :=
  sorry

/-- Helper for Lemma 21.49.1: the restricted global-sections functor from finite-free-retract
`𝒪_X`-modules lands in finite projective `Γ(X, 𝒪_X)`-modules. -/
private def finiteFreeRetractGlobalSectionsFunctor :
    (SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf).FullSubcategory ⥤
      FiniteProjectiveModuleCat ΓX :=
  ObjectProperty.lift FiniteProjectivesΓX
    ((SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf).ι ⋙ ΓMod)
    (moduleGlobalSections_mem_finiteProjectiveModuleProperty X)

/-- Lemma 21.49.1: global sections induce an equivalence from finite-free-retract `𝒪_X`-modules
on the ringed site `X` to finite projective modules over `Γ(X, 𝒪_X)`. -/
@[stacks 0FPX]
theorem finiteFreeRetractModules_equiv_finiteProjectiveModules :
    Functor.IsEquivalence (finiteFreeRetractGlobalSectionsFunctor X) := sorry

end

end SheafOfModules.RingedSite
