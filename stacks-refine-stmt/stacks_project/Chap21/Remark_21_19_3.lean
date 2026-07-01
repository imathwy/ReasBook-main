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

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory (ModuleCat X))
    (ModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ DerivedCategory (ModuleCat Y))
    (ModuleQis Y)

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [f'.modulePullback.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if, after
transposing along the derived adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback along `Lg'^*` of
the counit `Lf^* Rf_* K ⟶ K`, transported across the canonical commutativity isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
def IsUnboundedBaseChangeMap
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (K : ModuleDerived X)
    (η :
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)) ⟶
        ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K))) : Prop :=
  ((adj_f'.homEquiv
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K))
      ((modulePullbackDerived g').obj K)).symm η) =
    (hpull.app ((modulePushforwardDerived f).obj K)).hom ≫
      (modulePullbackDerived g').map (adj_f.counit.app K)

-- Proof sketch: use the commutativity isomorphism `hpull` to identify
-- `L(f')^* Lg^* Rf_* K` with `L(g')^* Lf^* Rf_* K`, then compose with the pullback by `Lg'^*` of
-- the counit of the derived adjunction `Lf^* ⊣ Rf_*`. Finally, transpose this morphism across
-- the derived adjunction `L(f')^* ⊣ R(f')_*`.
/-- Remark 21.19.3: for a square of ringed topoi formalized here by morphisms of ringed sites,
once the unbounded derived pullbacks satisfy the canonical commutativity isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` and the adjunctions `Lf^* ⊣ Rf_*` and
`L(f')^* ⊣ R(f')_*` have been chosen, every object `K` of `D(\mathcal O_{\mathcal C})`
admits the canonical base-change morphism
`Lg^* Rf_* K ⟶ R(f')_* L(g')^* K`, characterized by the usual adjunction formula. -/
theorem exists_unbounded_baseChangeMap
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (K : ModuleDerived X) :
    ∃ η :
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)) ⟶
        ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K)),
      IsUnboundedBaseChangeMap g' f' f g hpull adj_f adj_f' K η := sorry

end

end RingedSite.Hom
