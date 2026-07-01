import Mathlib
import stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y Z : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)

variable [f.modulePushforward.Additive]
variable [g.modulePushforward.Additive]
variable [(RingedSite.Hom.comp f g).modulePushforward.Additive]

variable [f.modulePullback.Additive]
variable [g.modulePullback.Additive]
variable [(RingedSite.Hom.comp f g).modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (RingedSite.Hom.comp f g)) (ModuleQis X)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp f g)) (ModuleQis Z)]

/-- Lemma 21.19.2: for composable morphisms of ringed topoi, formalized here by ringed-site
morphisms `f` and `g`, the derived pushforward of the composite morphism is canonically
isomorphic to the composite `Rg_* ∘ Rf_*`. In the statement-stage formalization this comparison
isomorphism is built from the chosen pullback comparison `Lg^* ⋙ Lf^* ≅ L(g \circ f)^*` and the
chosen derived adjunctions. -/
noncomputable abbrev modulePushforwardDerived_compIso
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f ≅
        modulePullbackDerived (RingedSite.Hom.comp f g))
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_g : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adj_comp :
      modulePullbackDerived (RingedSite.Hom.comp f g) ⊣
        modulePushforwardDerived (RingedSite.Hom.comp f g)) :
    modulePushforwardDerived f ⋙ modulePushforwardDerived g ≅
      modulePushforwardDerived (RingedSite.Hom.comp f g) :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull)
    adj_comp

-- Proof sketch: unfold `modulePushforwardDerived_compIso` and apply the standard counit formula
-- `Adjunction.rightAdjointUniq_hom_counit` for the uniqueness isomorphism of right adjoints.
/-- The comparison isomorphism from iterated derived pushforward to the derived pushforward of the
composite is characterized by compatibility with the counits of the chosen adjunctions. -/
theorem modulePushforwardDerived_compIso_hom_counit
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f ≅
        modulePullbackDerived (RingedSite.Hom.comp f g))
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_g : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adj_comp :
      modulePullbackDerived (RingedSite.Hom.comp f g) ⊣
        modulePushforwardDerived (RingedSite.Hom.comp f g)) :
    Functor.whiskerRight
        (modulePushforwardDerived_compIso f g hpull adj_f adj_g adj_comp).hom
        (modulePullbackDerived (RingedSite.Hom.comp f g)) ≫
      adj_comp.counit =
        (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull).counit := sorry

end

end RingedSite.Hom
