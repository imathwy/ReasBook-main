import Mathlib
import stacks_project.Chap13.Lemma_13_16_1
import stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {B' B C' C D' D : RingedSite.{u, v}}
variable (k : RingedSite.Hom B' B) (f' : RingedSite.Hom B' C')
variable (f : RingedSite.Hom B C) (l : RingedSite.Hom C' C)
variable (g' : RingedSite.Hom C' D') (g : RingedSite.Hom C D)
variable (m : RingedSite.Hom D' D)

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev UnboundedModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev UnboundedModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (UnboundedModuleCat X)

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves on `X`. -/
abbrev UnboundedModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (UnboundedModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev unboundedModulePushforward {X Y : RingedSite.{u, v}} (φ : RingedSite.Hom X Y) :
    UnboundedModuleCat X ⥤ UnboundedModuleCat Y :=
  SheafOfModules.pushforward φ.structureSheafMap

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev unboundedModulePushforwardToDerived {X Y : RingedSite.{u, v}} (φ : RingedSite.Hom X Y)
    [(unboundedModulePushforward φ).Additive] :=
  mapHomotopyCategoryToDerived (unboundedModulePushforward φ)

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev unboundedModulePullbackToDerived {X Y : RingedSite.{u, v}} (φ : RingedSite.Hom X Y)
    [φ.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived φ.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev unboundedModulePushforwardDerived {X Y : RingedSite.{u, v}}
    (φ : RingedSite.Hom X Y) [(unboundedModulePushforward φ).Additive]
    [Functor.HasRightDerivedFunctor
      (unboundedModulePushforwardToDerived φ) (UnboundedModuleQis X)] :
    UnboundedModuleDerived X ⥤ UnboundedModuleDerived Y :=
  Functor.totalRightDerived (unboundedModulePushforwardToDerived φ)
    (DerivedCategory.Qh :
      HomotopyCategory (UnboundedModuleCat X) (up ℤ) ⥤
        DerivedCategory (UnboundedModuleCat X))
    (UnboundedModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev unboundedModulePullbackDerived {X Y : RingedSite.{u, v}}
    (φ : RingedSite.Hom X Y) [φ.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor
      (unboundedModulePullbackToDerived φ) (UnboundedModuleQis Y)] :
    UnboundedModuleDerived Y ⥤ UnboundedModuleDerived X :=
  Functor.totalLeftDerived (unboundedModulePullbackToDerived φ)
    (DerivedCategory.Qh :
      HomotopyCategory (UnboundedModuleCat Y) (up ℤ) ⥤
        DerivedCategory (UnboundedModuleCat Y))
    (UnboundedModuleQis Y)

variable [(unboundedModulePushforward f).Additive]
variable [(unboundedModulePushforward f').Additive]
variable [(unboundedModulePushforward g).Additive]
variable [(unboundedModulePushforward g').Additive]
variable [(unboundedModulePushforward (RingedSite.Hom.comp f g)).Additive]
variable [(unboundedModulePushforward (RingedSite.Hom.comp f' g')).Additive]

variable [f.modulePullback.Additive]
variable [f'.modulePullback.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]
variable [k.modulePullback.Additive]
variable [l.modulePullback.Additive]
variable [m.modulePullback.Additive]
variable [(RingedSite.Hom.comp f g).modulePullback.Additive]
variable [(RingedSite.Hom.comp f' g').modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived f) (UnboundedModuleQis B)]
variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived f') (UnboundedModuleQis B')]
variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived g) (UnboundedModuleQis C)]
variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived g') (UnboundedModuleQis C')]
variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived (RingedSite.Hom.comp f g)) (UnboundedModuleQis B)]
variable [Functor.HasRightDerivedFunctor
  (unboundedModulePushforwardToDerived (RingedSite.Hom.comp f' g')) (UnboundedModuleQis B')]

variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived f) (UnboundedModuleQis C)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived f') (UnboundedModuleQis C')]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived g) (UnboundedModuleQis D)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived g') (UnboundedModuleQis D')]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived k) (UnboundedModuleQis B)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived l) (UnboundedModuleQis C)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived m) (UnboundedModuleQis D)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived (RingedSite.Hom.comp f g)) (UnboundedModuleQis D)]
variable [Functor.HasLeftDerivedFunctor
  (unboundedModulePullbackToDerived (RingedSite.Hom.comp f' g')) (UnboundedModuleQis D')]

/-- A morphism is an unbounded derived base-change map when, after transposing across the chosen
adjunction on the left vertical arrow, it becomes the pullback of the counit for the right
vertical arrow through the chosen commutativity isomorphism of pullback functors. -/
def IsUnboundedBaseChangeComparison
    {X' X Y' Y : RingedSite.{u, v}}
    (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [(unboundedModulePushforward f).Additive]
    [(unboundedModulePushforward f').Additive]
    [f.modulePullback.Additive]
    [f'.modulePullback.Additive]
    [g.modulePullback.Additive]
    [g'.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor
      (unboundedModulePushforwardToDerived f) (UnboundedModuleQis X)]
    [Functor.HasRightDerivedFunctor
      (unboundedModulePushforwardToDerived f') (UnboundedModuleQis X')]
    [Functor.HasLeftDerivedFunctor
      (unboundedModulePullbackToDerived g) (UnboundedModuleQis Y)]
    [Functor.HasLeftDerivedFunctor
      (unboundedModulePullbackToDerived g') (UnboundedModuleQis X)]
    [Functor.HasLeftDerivedFunctor
      (unboundedModulePullbackToDerived f) (UnboundedModuleQis Y)]
    [Functor.HasLeftDerivedFunctor
      (unboundedModulePullbackToDerived f') (UnboundedModuleQis Y')]
    (hpull :
      unboundedModulePullbackDerived g ⋙ unboundedModulePullbackDerived f' ≅
        unboundedModulePullbackDerived f ⋙ unboundedModulePullbackDerived g')
    (adj_f : unboundedModulePullbackDerived f ⊣ unboundedModulePushforwardDerived f)
    (adj_f' : unboundedModulePullbackDerived f' ⊣ unboundedModulePushforwardDerived f')
    (K : UnboundedModuleDerived X)
    (η :
      ((unboundedModulePullbackDerived g).obj ((unboundedModulePushforwardDerived f).obj K)) ⟶
        ((unboundedModulePushforwardDerived f').obj
          ((unboundedModulePullbackDerived g').obj K))) : Prop :=
  ((adj_f'.homEquiv
      ((unboundedModulePullbackDerived g).obj ((unboundedModulePushforwardDerived f).obj K))
      ((unboundedModulePullbackDerived g').obj K)).symm η) =
    (hpull.app ((unboundedModulePushforwardDerived f).obj K)).hom ≫
      (unboundedModulePullbackDerived g').map (adj_f.counit.app K)

/-- The composite of the base-change morphisms for two vertically composable squares of ringed
topoi. -/
noncomputable def composedUnboundedBaseChangeMap
    (K : UnboundedModuleDerived B)
    (η_top :
      ((unboundedModulePullbackDerived l).obj ((unboundedModulePushforwardDerived f).obj K)) ⟶
        ((unboundedModulePushforwardDerived f').obj ((unboundedModulePullbackDerived k).obj K)))
    (η_bottom :
      ((unboundedModulePullbackDerived m).obj
          ((unboundedModulePushforwardDerived g).obj ((unboundedModulePushforwardDerived f).obj K))) ⟶
        ((unboundedModulePushforwardDerived g').obj
          ((unboundedModulePullbackDerived l).obj ((unboundedModulePushforwardDerived f).obj K)))) :
    ((unboundedModulePullbackDerived m).obj
        ((unboundedModulePushforwardDerived g).obj ((unboundedModulePushforwardDerived f).obj K))) ⟶
      ((unboundedModulePushforwardDerived g').obj
        ((unboundedModulePushforwardDerived f').obj ((unboundedModulePullbackDerived k).obj K))) :=
  η_bottom ≫ (unboundedModulePushforwardDerived g').map η_top

-- Proof sketch: transpose the claimed outer morphism across the chosen adjunction for
-- `L(g' ∘ f')^* ⊣ R(g' ∘ f')_*`. The transpose reduces, via the comparison isomorphisms for
-- composite derived pushforwards and the hypotheses that `η_top` and `η_bottom` satisfy the
-- square-wise adjunction formulas, to the pullback along `Lk^*` of the counit for
-- `L(g ∘ f)^* ⊣ R(g ∘ f)_*`.
/-- Remark 21.19.4: for a composable pair of commutative squares of ringed topoi, if `η_top` and
`η_bottom` are the base-change morphisms for the top and bottom squares, then after identifying
the composite derived pushforwards with the derived pushforwards of the composite morphisms, their
composition is the base-change morphism for the outer rectangle. -/
theorem composed_unbounded_baseChangeMap_isBaseChange
    (hpull_top :
      unboundedModulePullbackDerived l ⋙ unboundedModulePullbackDerived f' ≅
        unboundedModulePullbackDerived f ⋙ unboundedModulePullbackDerived k)
    (hpull_bottom :
      unboundedModulePullbackDerived m ⋙ unboundedModulePullbackDerived g' ≅
        unboundedModulePullbackDerived g ⋙ unboundedModulePullbackDerived l)
    (hpull_outer :
      unboundedModulePullbackDerived m ⋙
          unboundedModulePullbackDerived (RingedSite.Hom.comp f' g') ≅
        unboundedModulePullbackDerived (RingedSite.Hom.comp f g) ⋙
          unboundedModulePullbackDerived k)
    (adj_f : unboundedModulePullbackDerived f ⊣ unboundedModulePushforwardDerived f)
    (adj_f' : unboundedModulePullbackDerived f' ⊣ unboundedModulePushforwardDerived f')
    (adj_g : unboundedModulePullbackDerived g ⊣ unboundedModulePushforwardDerived g)
    (adj_g' : unboundedModulePullbackDerived g' ⊣ unboundedModulePushforwardDerived g')
    (adj_outer :
      unboundedModulePullbackDerived (RingedSite.Hom.comp f g) ⊣
        unboundedModulePushforwardDerived (RingedSite.Hom.comp f g))
    (adj_outer' :
      unboundedModulePullbackDerived (RingedSite.Hom.comp f' g') ⊣
        unboundedModulePushforwardDerived (RingedSite.Hom.comp f' g'))
    (hpush_right :
      unboundedModulePushforwardDerived f ⋙ unboundedModulePushforwardDerived g ≅
        unboundedModulePushforwardDerived (RingedSite.Hom.comp f g))
    (hpush_left :
      unboundedModulePushforwardDerived f' ⋙ unboundedModulePushforwardDerived g' ≅
        unboundedModulePushforwardDerived (RingedSite.Hom.comp f' g'))
    (K : UnboundedModuleDerived B)
    (η_top :
      ((unboundedModulePullbackDerived l).obj ((unboundedModulePushforwardDerived f).obj K)) ⟶
        ((unboundedModulePushforwardDerived f').obj ((unboundedModulePullbackDerived k).obj K)))
    (η_bottom :
      ((unboundedModulePullbackDerived m).obj
          ((unboundedModulePushforwardDerived g).obj
            ((unboundedModulePushforwardDerived f).obj K))) ⟶
        ((unboundedModulePushforwardDerived g').obj
          ((unboundedModulePullbackDerived l).obj ((unboundedModulePushforwardDerived f).obj K))))
    (hη_top : IsUnboundedBaseChangeComparison k f' f l hpull_top adj_f adj_f' K η_top)
    (hη_bottom :
      IsUnboundedBaseChangeComparison l g' g m hpull_bottom adj_g adj_g'
        ((unboundedModulePushforwardDerived f).obj K) η_bottom) :
    IsUnboundedBaseChangeComparison
      k (RingedSite.Hom.comp f' g') (RingedSite.Hom.comp f g) m
      hpull_outer adj_outer adj_outer' K
      ((unboundedModulePullbackDerived m).map (hpush_right.app K).inv ≫
        composedUnboundedBaseChangeMap k f' f l g' g m K η_top η_bottom ≫
        (hpush_left.app ((unboundedModulePullbackDerived k).obj K)).hom) := sorry

end

end RingedSite.Hom
