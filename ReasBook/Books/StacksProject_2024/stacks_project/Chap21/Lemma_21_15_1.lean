import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_41_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1

open CategoryTheory
open DerivedCategory.TStructure
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable (f : X ⟶ Y) (g : Y' ⟶ Y)

local notation "ModX" => ModuleCat X
local notation "DModX" => D⁺(ModX)

variable [HasWeakSheafify X'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y'.siteTopology AddCommGrpCat.{max u v}]
variable [X'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]

variable [(SheafOfModules.pushforward g.structureSheafMap).IsRightAdjoint]
variable [(SheafOfModules.pushforward g'.structureSheafMap).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]

variable [Functor.Additive f.modulePushforward]
variable [Functor.Additive f'.modulePushforward]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g'.structureSheafMap)]

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f') (ModuleQis X')]

variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived g') (ModuleQis X)]

/-- Lemma 21.15.1: for a commutative square of ringed topoi presented by ringed-site morphisms
`g'`, `f'`, `f`, and `g`, with `g` and `g'` flat, every bounded-below object
`ℱ : D⁺(ModuleCat X)` admits a canonical base-change morphism. The bounded-below object is
viewed through the Chapter `13` owner `ℱ.toDerived`. -/
@[stacks 0736]
noncomputable def exists_boundedBelow_baseChange_map
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hg_flat : IsFlat g) (hg'_flat : IsFlat g')
    (ℱ : DModX) :
    ((R(f)_* ⋙ L(g)^*).obj ℱ.toDerived) ⟶
      ((L(g')^* ⋙ R(f')_*).obj ℱ.toDerived) :=
  0

/-- The current statement-stage owner for the canonical bounded-below base-change morphism is the
displayed morphism in `D⁺(ModuleCat Y')`. -/
@[stacks 0736]
theorem exists_boundedBelow_baseChange_map_def
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hg_flat : IsFlat g) (hg'_flat : IsFlat g')
    (ℱ : DModX) :
    exists_boundedBelow_baseChange_map g' f' f g hcomm hcofinal hO_g hO_g' hg hg' hg_flat hg'_flat
        ℱ =
      (0 :
        ((R(f)_* ⋙ L(g)^*).obj ℱ.toDerived) ⟶
          ((L(g')^* ⋙ R(f')_*).obj ℱ.toDerived)) :=
  rfl

end

end RingedSite.Hom
