import Mathlib
import stacks_project.Chap21.«21_50_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [MonoidalCategory (ModuleDerived X')]
variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y')]
variable [MonoidalCategory (ModuleDerived Y)]

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

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is a base-change map when its transpose along
`L(f')^* ⊣ R(f')_*` is the pullback of the counit `Lf^* Rf_* K ⟶ K`, transported through the
commutativity isomorphism `L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
private def IsProjectionFormulaBaseChangeMap
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

/-- A chosen comparison between derived pullback by `g` and derived tensor product on
`D(\mathcal O_{\mathcal D})`. -/
private abbrev ProjectionFormulaBaseChangeTensorComparisonY :=
  ∀ (K L : ModuleDerived Y),
    ((modulePullbackDerived g).obj (((curriedTensor (ModuleDerived Y)).obj L).obj K)) ≅
      (((curriedTensor (ModuleDerived Y')).obj ((modulePullbackDerived g).obj L)).obj
        ((modulePullbackDerived g).obj K))

/-- A chosen comparison between derived pullback by `g'` and derived tensor product on
`D(\mathcal O_{\mathcal C})`. -/
private abbrev ProjectionFormulaBaseChangeTensorComparisonX :=
  ∀ (K L : ModuleDerived X),
    ((modulePullbackDerived g').obj (((curriedTensor (ModuleDerived X)).obj L).obj K)) ≅
      (((curriedTensor (ModuleDerived X')).obj ((modulePullbackDerived g').obj L)).obj
        ((modulePullbackDerived g').obj K))

/-- A chosen comparison between derived pullback by `f'` and derived tensor product on
`D(\mathcal O_{\mathcal D'})`. -/
private abbrev ProjectionFormulaBaseChangeTensorComparisonY' :=
  ∀ (K L : ModuleDerived Y'),
    ((modulePullbackDerived f').obj (((curriedTensor (ModuleDerived Y')).obj L).obj K)) ≅
      (((curriedTensor (ModuleDerived X')).obj ((modulePullbackDerived f').obj L)).obj
        ((modulePullbackDerived f').obj K))

/-- The left vertical morphism in the projection-formula/base-change compatibility square, given
by the pullback-tensor comparison for `g`. -/
private abbrev projectionFormulaBaseChangeLeftMap
    (tensorComparison_g : ProjectionFormulaBaseChangeTensorComparisonY g) (E : ModuleDerived X)
    (K : ModuleDerived Y) :
    ((modulePullbackDerived g).obj
        (((curriedTensor (ModuleDerived Y)).obj K).obj ((modulePushforwardDerived f).obj E))) ⟶
      (((curriedTensor (ModuleDerived Y')).obj ((modulePullbackDerived g).obj K)).obj
        ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj E))) :=
  (tensorComparison_g ((modulePushforwardDerived f).obj E) K).hom

/-- The lower horizontal morphism in the projection-formula/base-change compatibility square:
first tensor with the base-change map for `E`, then apply the projection-formula morphism for
`f'`. -/
private abbrev projectionFormulaBaseChangeBottomMap
    (E : ModuleDerived X) (K : ModuleDerived Y)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (tensorComparison_f' : ProjectionFormulaBaseChangeTensorComparisonY' f')
    (baseChangeE :
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj E)) ⟶
        ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj E)))
    :
    (((curriedTensor (ModuleDerived Y')).obj ((modulePullbackDerived g).obj K)).obj
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj E))) ⟶
      (modulePushforwardDerived f').obj
        (((curriedTensor (ModuleDerived X')).obj
            ((modulePullbackDerived f').obj ((modulePullbackDerived g).obj K))).obj
          ((modulePullbackDerived g').obj E)) :=
  (((curriedTensor (ModuleDerived Y')).obj ((modulePullbackDerived g).obj K)).map baseChangeE) ≫
    _root_.CategoryTheory.projectionFormulaMorphism
      (modulePullbackDerived f')
      (modulePushforwardDerived f')
      adj_f'
      (fun A B ↦ tensorComparison_f' B A)
      ((modulePullbackDerived g').obj E)
      ((modulePullbackDerived g).obj K)

/-- The right vertical morphism in the projection-formula/base-change compatibility square: apply
base change to `E \otimes^{\mathbf L} Lf^* K`, then compare `L(g')^*(E \otimes^{\mathbf L} Lf^*K)`
with `L(g')^*E \otimes^{\mathbf L} L(f')^* Lg^* K`. -/
private abbrev projectionFormulaBaseChangeRightMap
    (E : ModuleDerived X) (K : ModuleDerived Y)
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g')
    (tensorComparison_g' : ProjectionFormulaBaseChangeTensorComparisonX g')
    (baseChangeTensor :
      ((modulePullbackDerived g).obj
          ((modulePushforwardDerived f).obj
            (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E))) ⟶
        ((modulePushforwardDerived f').obj
          ((modulePullbackDerived g').obj
            (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E))))
    :
    ((modulePullbackDerived g).obj
        ((modulePushforwardDerived f).obj
          (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E))) ⟶
      (modulePushforwardDerived f').obj
        (((curriedTensor (ModuleDerived X')).obj
            ((modulePullbackDerived f').obj ((modulePullbackDerived g).obj K))).obj
          ((modulePullbackDerived g').obj E)) :=
  baseChangeTensor ≫
    (modulePushforwardDerived f').map
      ((tensorComparison_g' E ((modulePullbackDerived f).obj K)).hom ≫
        (((curriedTensor (ModuleDerived X')).map (hpull.app K).symm.hom).app
          ((modulePullbackDerived g').obj E)))

-- Proof sketch: paste the top projection-formula map with the base-change map for
-- `E ⊗^{\mathbf L} Lf^* K`, then rewrite the right-hand side using the pullback-tensor comparison
-- for `g'` and the commutativity isomorphism `L(f')^*Lg^* ≅ L(g')^*Lf^*`. On the other side,
-- first rewrite `Lg^*(Rf_*E ⊗^{\mathbf L} K)` by the pullback-tensor comparison for `g`, then
-- tensor the base-change map for `E` with `Lg^*K`, and finally apply the projection-formula map
-- for `f'`. The omitted textbook verification is exactly that these two composites agree.
/-- Remark 21.50.2: the projection-formula morphism of `21.50.0.1` is compatible with the
base-change morphism of Remark `21.19.3`. For a commutative square of ringed topoi, after choosing
derived pullback-tensor comparison isomorphisms for `g`, `g'`, and `f'`, the outer square whose
top edge is `Lg^*` applied to the projection-formula morphism for `f`, whose left edge is the
pullback-tensor comparison for `g`, whose lower edge is the tensor of the base-change morphism for
`E` with `Lg^*K` followed by the projection-formula morphism for `f'`, and whose right edge is the
base-change morphism for `E ⊗^{\mathbf L} Lf^*K` followed by the canonical comparison
`L(g')^*(E ⊗^{\mathbf L} Lf^*K) ⟶ L(g')^*E ⊗^{\mathbf L} L(f')^*Lg^*K`, commutes. -/
theorem projectionFormulaMorphism_baseChange_commSq
    (tensorComparison_f :
      ∀ (K L : ModuleDerived Y),
        ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj L).obj K)) ≅
          (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj L)).obj
            ((modulePullbackDerived f).obj K)))
    (tensorComparison_f' : ProjectionFormulaBaseChangeTensorComparisonY' f')
    (tensorComparison_g : ProjectionFormulaBaseChangeTensorComparisonY g)
    (tensorComparison_g' : ProjectionFormulaBaseChangeTensorComparisonX g')
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (E : ModuleDerived X) (K : ModuleDerived Y)
    (baseChangeE :
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj E)) ⟶
        ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj E)))
    (hbaseChangeE :
      IsProjectionFormulaBaseChangeMap g' f' f g hpull adj_f adj_f' E baseChangeE)
    (baseChangeTensor :
      ((modulePullbackDerived g).obj
          ((modulePushforwardDerived f).obj
            (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E))) ⟶
        ((modulePushforwardDerived f').obj
          ((modulePullbackDerived g').obj
            (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E))))
    (hbaseChangeTensor :
      IsProjectionFormulaBaseChangeMap
        g'
        f'
        f
        g
        hpull
        adj_f
        adj_f'
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj K)).obj E)
        baseChangeTensor) :
    CommSq
      ((modulePullbackDerived g).map
        (_root_.CategoryTheory.projectionFormulaMorphism
          (modulePullbackDerived f)
          (modulePushforwardDerived f)
          adj_f
          (fun A B ↦ tensorComparison_f B A)
          E
          K))
      (f.projectionFormulaBaseChangeLeftMap g tensorComparison_g E K)
      (g'.projectionFormulaBaseChangeRightMap f' f g E K hpull
        tensorComparison_g' baseChangeTensor)
      (g'.projectionFormulaBaseChangeBottomMap f' f g E K adj_f'
        tensorComparison_f' baseChangeE) := sorry

end

end RingedSite.Hom
