import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_19_1 (from Chap21) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

/-- Lemma 21.19.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`,
the unbounded derived pullback `Lf^*` is left adjoint to the unbounded derived pushforward
`Rf_*`. -/
abbrev modulePullbackDerived_pushforward_adjunction : Prop :=
  Nonempty (modulePullbackDerived f ⊣ modulePushforwardDerived f)

-- Proof sketch: start from the underived adjunction `f^* ⊣ f_*` on module sheaves from
-- Lemma `18.13.2`. Lemma `21.18.2` supplies the total left derived functor `Lf^*`, and the
-- construction of `Rf_*` gives the total right derived functor. Then apply the generic derived
-- adjunction result of Lemma `13.30.3`, and evaluate the resulting adjunction at `(𝒢, ℱ)`.
/-- The Hom-set formulation of the derived pullback-pushforward adjunction. -/
theorem modulePullbackDerived_pushforward_homEquiv
    (h : modulePullbackDerived_pushforward_adjunction f)
    (ℱ : ModuleDerived X) (𝒢 : ModuleDerived Y) :
    Nonempty
      (((modulePullbackDerived f).obj 𝒢 ⟶ ℱ) ≃
        (𝒢 ⟶ (modulePushforwardDerived f).obj ℱ)) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_19_2 (from Chap21) -/
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

/-! ### Remark_21_19_3 (from Chap21) -/
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

/-! ### Remark_21_19_4 (from Chap21) -/
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

/-! ### Remark_21_19_5 (from Chap21) -/
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

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if, after
transposing along the derived adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback along `Lg'^*` of
the counit `Lf^* Rf_* K ⟶ K`, transported across the canonical commutativity isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
def IsUnboundedBaseChangeMap
    {X' X Y' Y : RingedSite.{u, v}}
    (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [f.modulePushforward.Additive]
    [f'.modulePushforward.Additive]
    [f.modulePullback.Additive]
    [f'.modulePullback.Additive]
    [g.modulePullback.Additive]
    [g'.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
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

section

variable {X2 X1 X0 Y2 Y1 Y0 : RingedSite.{u, v}}
variable (g1 : RingedSite.Hom X2 X1) (g0 : RingedSite.Hom X1 X0)
variable (f2 : RingedSite.Hom X2 Y2) (f1 : RingedSite.Hom X1 Y1) (f0 : RingedSite.Hom X0 Y0)
variable (h1 : RingedSite.Hom Y2 Y1) (h0 : RingedSite.Hom Y1 Y0)

variable [f0.modulePushforward.Additive]
variable [f1.modulePushforward.Additive]
variable [f2.modulePushforward.Additive]

variable [f0.modulePullback.Additive]
variable [f1.modulePullback.Additive]
variable [f2.modulePullback.Additive]
variable [g0.modulePullback.Additive]
variable [g1.modulePullback.Additive]
variable [h0.modulePullback.Additive]
variable [h1.modulePullback.Additive]
variable [(RingedSite.Hom.comp g1 g0).modulePullback.Additive]
variable [(RingedSite.Hom.comp h1 h0).modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f0) (ModuleQis X0)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f1) (ModuleQis X1)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f2) (ModuleQis X2)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f2) (ModuleQis Y2)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g0) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g1) (ModuleQis X1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp g1 g0)) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp h1 h0)) (ModuleQis Y0)]

/-- The pullback commutativity isomorphisms for two horizontally composable squares combine to the
pullback commutativity isomorphism for the outer rectangle. -/
noncomputable def horizontalCompositePullbackIso
    (hpull0 :
      modulePullbackDerived h0 ⋙ modulePullbackDerived f1 ≅
        modulePullbackDerived f0 ⋙ modulePullbackDerived g0)
    (hpull1 :
      modulePullbackDerived h1 ⋙ modulePullbackDerived f2 ≅
        modulePullbackDerived f1 ⋙ modulePullbackDerived g1)
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1) :
    modulePullbackDerived (RingedSite.Hom.comp h1 h0) ⋙ modulePullbackDerived f2 ≅
      modulePullbackDerived f0 ⋙ modulePullbackDerived (RingedSite.Hom.comp g1 g0) :=
  Functor.isoWhiskerRight hcomp (modulePullbackDerived f2) ≪≫
    Functor.associator (modulePullbackDerived h0) (modulePullbackDerived h1)
      (modulePullbackDerived f2) ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived h0) hpull1 ≪≫
    (Functor.associator (modulePullbackDerived h0) (modulePullbackDerived f1)
      (modulePullbackDerived g1)).symm ≪≫
    Functor.isoWhiskerRight hpull0 (modulePullbackDerived g1) ≪≫
    Functor.associator (modulePullbackDerived f0) (modulePullbackDerived g0)
      (modulePullbackDerived g1) ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived f0) gcomp.symm

/-- The composite of the two base-change morphisms associated to adjacent squares, rewritten as a
morphism from the outer pullback of `Rf0_*` to the outer pushforward of the iterated pullback. -/
noncomputable def horizontalCompositeUnboundedBaseChangeMap
    (K : ModuleDerived X0)
    (η0 :
      ((modulePullbackDerived h0).obj ((modulePushforwardDerived f0).obj K)) ⟶
        ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K)))
    (η1 :
      ((modulePullbackDerived h1).obj
          ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K))) ⟶
        ((modulePushforwardDerived f2).obj
          ((modulePullbackDerived g1).obj ((modulePullbackDerived g0).obj K))))
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1) :
    ((modulePullbackDerived (RingedSite.Hom.comp h1 h0)).obj
        ((modulePushforwardDerived f0).obj K)) ⟶
      ((modulePushforwardDerived f2).obj
        ((modulePullbackDerived (RingedSite.Hom.comp g1 g0)).obj K)) :=
  (hcomp.app ((modulePushforwardDerived f0).obj K)).hom ≫
    (modulePullbackDerived h1).map η0 ≫
    η1 ≫
    (modulePushforwardDerived f2).map ((gcomp.symm.app K).hom)

-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the composite morphism along the adjunction
-- `L(f2)^* ⊣ R(f2)_*`. The hypotheses `hη0` and `hη1` identify the two intermediate pieces with
-- the counits for the right and left squares, and the resulting composite is exactly the mate for
-- the outer rectangle.
/-- Remark 21.19.5: for two horizontally composable squares of ringed topoi, the composition of
the base-change maps from Remark `21.19.3` is the base-change map for the outer rectangle. -/
theorem horizontalComposite_isUnboundedBaseChangeMap
    (hpull0 :
      modulePullbackDerived h0 ⋙ modulePullbackDerived f1 ≅
        modulePullbackDerived f0 ⋙ modulePullbackDerived g0)
    (hpull1 :
      modulePullbackDerived h1 ⋙ modulePullbackDerived f2 ≅
        modulePullbackDerived f1 ⋙ modulePullbackDerived g1)
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1)
    (adj_f0 : modulePullbackDerived f0 ⊣ modulePushforwardDerived f0)
    (adj_f1 : modulePullbackDerived f1 ⊣ modulePushforwardDerived f1)
    (adj_f2 : modulePullbackDerived f2 ⊣ modulePushforwardDerived f2)
    (K : ModuleDerived X0)
    (η0 :
      ((modulePullbackDerived h0).obj ((modulePushforwardDerived f0).obj K)) ⟶
        ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K)))
    (η1 :
      ((modulePullbackDerived h1).obj
          ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K))) ⟶
        ((modulePushforwardDerived f2).obj
          ((modulePullbackDerived g1).obj ((modulePullbackDerived g0).obj K))))
    (hη0 : IsUnboundedBaseChangeMap g0 f1 f0 h0 hpull0 adj_f0 adj_f1 K η0)
    (hη1 :
      IsUnboundedBaseChangeMap g1 f2 f1 h1 hpull1 adj_f1 adj_f2
        ((modulePullbackDerived g0).obj K) η1) :
    IsUnboundedBaseChangeMap
      (RingedSite.Hom.comp g1 g0)
      f2
      f0
      (RingedSite.Hom.comp h1 h0)
      (horizontalCompositePullbackIso g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp)
      adj_f0
      adj_f2
      K
      (horizontalCompositeUnboundedBaseChangeMap
        g1 g0 f2 f1 f0 h1 h0 K η0 η1 hcomp gcomp) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_19_6 (from Chap21) -/
/- Lemma 21.19.6: for a morphism of ringed topoi and a complex `\mathcal K^\bullet`, the square
in `D(\mathcal O_\mathcal C)` built from the comparison `Lf^* \to f^*` on complexes, the
comparison `f_* \to Rf_*` on complexes, the underived counit
`f^* f_* \mathcal K^\bullet \to \mathcal K^\bullet`, and the derived counit
`Lf^* Rf_* \mathcal K^\bullet \to \mathcal K^\bullet` commutes. In canonical mathlib form this is
the generic derived-adjunction counit compatibility
`CategoryTheory.Adjunction.derivedε_fac_app`. -/
recall CategoryTheory.Adjunction.derivedε_fac_app

/-! ### Remark_21_19_7 (from Chap21) -/
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
    [(modulePushforward f).Additive] :=
  mapHomotopyCategoryToDerived (modulePushforward f)

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [(modulePushforward f).Additive]
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

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [(modulePushforward f).Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

/- The chosen pullback-tensor comparison for `Lf^*`, expressing compatibility of the derived
pullback with the derived tensor products on the source and target. -/
variable
  (pullbackTensorComparison :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
        ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))

/-- The morphism adjoint to the relative cup-product map, obtained from the pullback-tensor
comparison together with the counit `Lf^* Rf_* ⟶ \mathrm{id}` on each tensor factor. -/
noncomputable def relativeCupProductAdjointMap
    (K L : ModuleDerived X) :
    ((modulePullbackDerived f).obj
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      ((tensorSource.obj L).obj K) :=
  (pullbackTensorComparison
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)).hom ≫
    ((tensorSource.map (adj.counit.app L)).app
      ((modulePullbackDerived f).obj ((modulePushforwardDerived f).obj K))) ≫
    ((tensorSource.obj L).map (adj.counit.app K))

/-- Remark 21.19.7: for a morphism of ringed topoi formalized by the ringed-site morphism `f`,
the relative cup-product morphism
`Rf_* K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* L ⟶
  Rf_* (K \otimes_{\mathcal O_X}^{\mathbf L} L)`
is the mate, under the derived adjunction `Lf^* ⊣ Rf_*`, of the pullback-tensor comparison
followed by the tensor of the counit maps `Lf^* Rf_* K ⟶ K` and `Lf^* Rf_* L ⟶ L`. -/
noncomputable def relativeCupProductMap
    (K L : ModuleDerived X) :
    ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
      ((modulePushforwardDerived f).obj K)) ⟶
      (modulePushforwardDerived f).obj ((tensorSource.obj L).obj K) :=
  (adj.homEquiv
      ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
        ((modulePushforwardDerived f).obj K))
      ((tensorSource.obj L).obj K))
    (relativeCupProductAdjointMap
      f tensorSource tensorTarget adj pullbackTensorComparison K L)

-- Proof sketch: unfold `relativeCupProductMap`; it is defined by applying `adj.homEquiv` to
-- `relativeCupProductAdjointMap`, so applying the inverse adjunction bijection recovers exactly
-- that composite.
/-- The relative cup-product morphism is adjoint to the map obtained from tensor compatibility of
`Lf^*` with derived tensor products and the counit `Lf^* Rf_* ⟶ \mathrm{id}`. -/
theorem relativeCupProductMap_spec
    (K L : ModuleDerived X) :
    ((adj.homEquiv
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))
        ((tensorSource.obj L).obj K)).symm
      (relativeCupProductMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L)) =
      relativeCupProductAdjointMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_19_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.19.8 in the abelian-sheaf/derived-category domain:
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `ObjectProperty.lift`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`;
- best owner abstraction: the Chapter 13 owner
  `derivedCategoryCohomologyInProperty` together with its full-subcategory owner
  `DerivedCategoryWithCohomologyIn`;
- primitive data: the source-facing torsion object property on `Sheaf J AddCommGrpCat`;
- derived API: the full subcategory of torsion sheaves, its exact inclusion into all abelian
  sheaves, and the lifted derived comparison functor into `DerivedCategoryWithCohomologyIn`;
- source/core/bridge triage:
  `source-facing`: `torsionAbelianSheafProperty` and the torsion derived comparison equivalence;
  `core/canonical`: `derivedCategoryCohomologyInProperty`, `DerivedCategoryWithCohomologyIn`, and
    `weakSerreSubcategory_inclusion_exact`;
  `bridge/view`: the comparison functor built from `Functor.mapDerivedCategory` and
    `ObjectProperty.lift`.

Accordingly, the local duplicate definitions of
`derivedCategoryCohomologyInProperty` and `DerivedCategoryWithCohomologyIn` are removed in favor
of the chapter-level owners. -/

/-- The object property on `Ab(\mathcal C)` consisting of torsion abelian sheaves, i.e. sheaves
whose section groups over every object of the site are torsion abelian groups. -/
abbrev torsionAbelianSheafProperty (J : GrothendieckTopology C) :
    ObjectProperty (Sheaf J AddCommGrpCat.{max u v}) :=
  fun F ↦ ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U))

local notation "TorsionProperty" => torsionAbelianSheafProperty J
local notation "TorsionSheaf" => TorsionProperty.FullSubcategory

-- Proof sketch: unfold `torsionAbelianSheafProperty`; the displayed equivalence is definitional.
/-- Membership in `torsionAbelianSheafProperty J` means that every section group of the sheaf is
torsion. -/
theorem mem_torsionAbelianSheafProperty_iff
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    TorsionProperty F ↔
      ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U)) :=
  Iff.rfl

/-- Torsion abelian sheaves form a LinearRepresentations_Serre_1977 subcategory of `Ab(\mathcal C)`. -/
instance torsionAbelianSheafProperty_isSerreClass :
    TorsionProperty.IsSerreClass := sorry

/-- Torsion abelian sheaves are closed under finite products. -/
instance torsionAbelianSheafProperty_isClosedUnderFiniteProducts :
    TorsionProperty.IsClosedUnderFiniteProducts := sorry

/-- Torsion abelian sheaves are closed under finite coproducts. -/
instance torsionAbelianSheafProperty_isClosedUnderFiniteCoproducts :
    TorsionProperty.IsClosedUnderFiniteCoproducts := sorry

/-- The inclusion of torsion abelian sheaves preserves finite limits. -/
instance torsionAbelianSheafInclusion_preservesFiniteLimits :
    PreservesFiniteLimits TorsionProperty.ι :=
  (exactFunctor_iff TorsionProperty.ι).1
    (weakSerreSubcategory_inclusion_exact TorsionProperty : _)
    |>.1

/-- The inclusion of torsion abelian sheaves preserves finite colimits. -/
instance torsionAbelianSheafInclusion_preservesFiniteColimits :
    PreservesFiniteColimits TorsionProperty.ι :=
  (exactFunctor_iff TorsionProperty.ι).1
    (weakSerreSubcategory_inclusion_exact TorsionProperty : _)
    |>.2

-- Proof sketch: the inclusion `TorsionSheaf ⥤ AbSheaf` is exact, so the induced functor on
-- derived categories commutes with cohomology. Since every object of `TorsionSheaf` is torsion,
-- every cohomology sheaf of the image again lies in `TorsionProperty`.
/-- The derived image of a complex of torsion abelian sheaves has torsion cohomology sheaves. -/
theorem torsionAbelianSheafDerivedComparisonFunctor_obj_mem
    (K : DerivedCategory TorsionSheaf) :
    derivedCategoryCohomologyInProperty TorsionProperty
      ((Functor.mapDerivedCategory TorsionProperty.ι).obj K) := sorry

/-- The canonical functor `D(\mathcal A) \to D_\mathcal A(\mathcal C)` induced by the inclusion of
torsion abelian sheaves into all abelian sheaves on the site. -/
abbrev torsionAbelianSheafDerivedComparisonFunctor :
    DerivedCategory TorsionSheaf ⥤
      DerivedCategoryWithCohomologyIn TorsionProperty :=
  ObjectProperty.lift
    (derivedCategoryCohomologyInProperty TorsionProperty)
    (Functor.mapDerivedCategory TorsionProperty.ι)
    torsionAbelianSheafDerivedComparisonFunctor_obj_mem

-- Proof sketch: represent derived objects by K-injective complexes of injective abelian sheaves.
-- Injective abelian sheaves are divisible, so the termwise torsion subsheaf of such a complex is
-- again K-injective and computes the right derived functor of torsion. This gives a right adjoint
-- to the inclusion `D(\mathcal A) ⥤ D_\mathcal A(\mathcal C)`, and the unit and counit are
-- isomorphisms because torsion complexes are unchanged by torsion and a complex with torsion
-- cohomology is quasi-isomorphic to the torsion subcomplex of an injective representative.
/-- Lemma 21.19.8: if `\mathcal A ⊂ \operatorname{Ab}(\mathcal C)` is the LinearRepresentations_Serre_1977 subcategory of
torsion abelian sheaves on a site `\mathcal C`, then the canonical functor
`D(\mathcal A) \to D_\mathcal A(\mathcal C)` is an equivalence. -/
theorem torsionAbelianSheafDerivedComparisonFunctor_isEquivalence :
    Functor.IsEquivalence torsionAbelianSheafDerivedComparisonFunctor := sorry

end

end CategoryTheory.Sheaf
