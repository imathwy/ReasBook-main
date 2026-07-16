import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_3
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_7

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "JY" => Opens.grothendieckTopology Y.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "ModY" => ringedSiteModuleCategory JY Y.𝒪

private abbrev pullbackModule (f : X ⟶ Y) : ModY ⥤ ModX :=
  RingedSpace.Hom.pullback f.toShHom

-- Semantic recall: `lean_leansearch` surfaced only the generic sheaf/module pullback owners.
-- Chapter 31 already fixes the source-facing owners `meromorphicSections` and
-- `Hom.pullbacksMeromorphicFunctionsDefined`, while Chapter 6 fixes the ambient module pullback
-- owner `RingedSpace.Hom.pullback` along `f.toShHom`; `pullbackModule` records this in the same
-- module-category spelling as Definition 31.23.7. Definition 31.23.7 then supplies the
-- source-facing regularity predicate used below.

/-- Lemma 31.23.8 (1): if `f : X ⟶ Y` is a morphism of locally ringed spaces for which pullbacks
of meromorphic functions are defined in the sense of Definition 31.23.4, then every
`\mathcal O_Y`-module sheaf `\mathcal F` admits the canonical pullback map
`f^* : \Gamma(Y, \mathcal K_Y(\mathcal F)) \to \Gamma(X, \mathcal K_X(f^*\mathcal F))`. The
parameters `regularSectionsX` and `regularSectionsY` are the chosen regular-meromorphic-function
subsheaves from Definition 31.23.4. -/
@[stacks 02OY]
theorem exists_pullbackMeromorphicSections
    (regularSectionsX : ∀ U : Opens X, Set (X.presheaf.obj (op U)))
    (regularSectionsY : ∀ V : Opens Y, Set (Y.presheaf.obj (op V)))
    (f : X ⟶ Y)
    (hf : Hom.pullbacksMeromorphicFunctionsDefined f regularSectionsX regularSectionsY)
    (ℱ : ModY) :
    ∃ pullbackMap : Y.meromorphicSections ℱ →
        X.meromorphicSections ((pullbackModule f).obj ℱ), True := sorry

/-- Lemma 31.23.8 (2): under the same pullback hypothesis on meromorphic functions, if
`\mathcal L` is an invertible `\mathcal O_Y`-module and `s` is a regular meromorphic section of
`\mathcal L`, then `f^*s` is a regular meromorphic section of `f^*\mathcal L`. The parameters
`regularSectionsX` and `regularSectionsY` are the chosen regular-meromorphic-function subsheaves
from Definition 31.23.4. -/
@[stacks 02OY]
theorem exists_pullbackMeromorphicSections_preservesRegular
    (regularSectionsX : ∀ U : Opens X, Set (X.presheaf.obj (op U)))
    (regularSectionsY : ∀ V : Opens Y, Set (Y.presheaf.obj (op V)))
    [MonoidalCategory ModX]
    [MonoidalCategory ModY]
    [MonoidalCategory
      (ringedSiteModuleCategory
        (Opens.grothendieckTopology X.toTopCat) (X.meromorphicFunctionSheaf))]
    [MonoidalCategory
      (ringedSiteModuleCategory
        (Opens.grothendieckTopology Y.toTopCat) (Y.meromorphicFunctionSheaf))]
    (f : X ⟶ Y)
    (hf : Hom.pullbacksMeromorphicFunctionsDefined f regularSectionsX regularSectionsY)
    (ℒ : ModY)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight ((pullbackModule f).obj ℒ))] :
    ∃ pullbackMap : Y.meromorphicSections ℒ →
        X.meromorphicSections ((pullbackModule f).obj ℒ),
      ∀ s : Y.meromorphicSections ℒ,
        Y.IsRegularMeromorphicSection ℒ s →
          X.IsRegularMeromorphicSection ((pullbackModule f).obj ℒ)
            (pullbackMap s) := sorry

end AlgebraicGeometry.LocallyRingedSpace
