import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_33_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 21.19.7:
- primary domain: relative derived cup products for `L(f)^* ⊣ R(f)_*` on derived categories of
  module sheaves on ringed sites;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_spec`,
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the relative cup-product morphism of Remark 21.19.7;
  `core/canonical`: the generic categorical owner `CategoryTheory.relativeDerivedCupProduct`
    together with its specification theorem
    `CategoryTheory.relativeDerivedCupProduct_spec`;
  `bridge/view`: this ringed-site specialization surface.
- primitive data: the morphism `f`, the chosen derived adjunction, and the pullback-tensor
  comparison;
- derived API: direct reuse of the generic owner morphism and its adjoint-side specification.

Source/core/bridge triage:
- `source-facing`: the ringed-site relative cup product;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`;
- `bridge/view`: the ringed-site specialization of that generic owner and of
  `CategoryTheory.relativeDerivedCupProduct_spec`.

This item is therefore a canonical recall surface, not the owner of a second ringed-site-specific
cup-product declaration. -/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ K L : ModuleDerived Y,
      (modulePullbackDerived f).obj ((tensorTarget.obj L).obj K) ≅
        (tensorSource.obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K))

/- Remark 21.19.7: for a morphism of ringed topoi formalized by the ringed-site morphism `f`, the
relative cup-product morphism
`Rf_* K ⊗[𝒪_Y]^L Rf_* L ⟶ Rf_* (K ⊗[𝒪_X]^L L)`
is the generic owner `CategoryTheory.relativeDerivedCupProduct`, specialized to the derived
pullback/pushforward adjunction on module sheaves. -/
recall CategoryTheory.relativeDerivedCupProduct

/- Applying `Adjunction.homEquiv.symm` to that ringed-site specialization recovers the pullback
side morphism built from the pullback-tensor comparison and the two counit maps. -/
recall CategoryTheory.relativeDerivedCupProduct_spec

end

end RingedSite.Hom
