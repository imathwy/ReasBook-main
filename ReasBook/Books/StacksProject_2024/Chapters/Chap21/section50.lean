import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_50_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u v

namespace RingedSite

/- Domain-style sampling for Lemma 21.50.1:
- primary domain: projection-formula morphisms in monoidal derived categories of module sheaves on
  ringed sites;
- sampled declarations:
  `RingedSite.Hom.localizedRestriction`,
  `RingedSite.Hom.ModuleDerived`,
  `CategoryTheory.projectionFormulaMorphism`,
  `SheafOfModules.RingedSite.DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the general ringed-site perfectness owner
    `RingedSite.DerivedCategory.IsPerfect` and the resulting `IsIso` statement for the canonical
    projection-formula morphism;
  `core/canonical`: `CategoryTheory.projectionFormulaMorphism` together with the ringed-site
    derived category `RingedSite.Hom.ModuleDerived`;
  `bridge/view`: the Chapter 21 commutative-ringed-site owner
    `SheafOfModules.RingedSite.DerivedCategory.IsPerfect`, which matches the same mathematical
    notion under stronger commutativity hypotheses but does not cover arbitrary `RingCat`-valued
    ringed sites;
- primitive data: the local strictly perfect model criterion for a representative complex and the
  resulting derived perfectness predicate on `RingedSite.Hom.ModuleDerived`;
- derived API: the perfectness owner `RingedSite.DerivedCategory.IsPerfect` and the theorem
  `projectionFormulaMorphism_isIso_of_isPerfect`. -/

section Perfectness

variable {X : RingedSite.{u, v}}

private abbrev ModuleComplex (X : RingedSite.{u, v}) :=
  CochainComplex (RingedSite.Hom.ModuleCat X) ℤ

private def isStrictlyPerfectComplex
    {Z : RingedSite.{u, v}} (E : ModuleComplex Z) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i)
        (SheafOfModules.free.{max u v} I : RingedSite.Hom.ModuleCat Z))

variable [∀ U : X, (RingedSite.Hom.localizedRestriction X U).PreservesZeroMorphisms]

private abbrev localizedRestrictionComplex (U : X) :
    ModuleComplex X ⥤ ModuleComplex (X.localization U) :=
  show ModuleComplex X ⥤ ModuleComplex (X.localization U) from
    (RingedSite.Hom.localizedRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

private def isPerfectComplex
    (E : ModuleComplex X) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : ModuleComplex (X.localization I.Y),
      ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
        isStrictlyPerfectComplex E' ∧ QuasiIso α

namespace DerivedCategory

/-- An object of `D(\mathcal O_X)` on a ringed site is perfect if it is represented by a complex
whose localizations are quasi-isomorphic to strictly perfect complexes. -/
def IsPerfect (K : RingedSite.Hom.ModuleDerived X) : Prop :=
  ∃ E : ModuleComplex X,
    ∃ α : DerivedCategory.Q.obj E ⟶ K,
      isPerfectComplex E ∧ IsIso α

end DerivedCategory

end Perfectness

end RingedSite

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [∀ U : Y, (localizedRestriction Y U).PreservesZeroMorphisms]
variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj L).obj K)) ≅
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))

-- Proof sketch: the statement is local on the target ringed topos, so for a perfect object `K`
-- one works on a cover where `K` is represented by a strictly perfect complex. The projection
-- formula is immediate for finite free summands and stable under finite direct sums, summands, and
-- stupid truncations, reducing to the case `K = \mathcal O_{\mathcal D}[n]`.
/-- Lemma 21.50.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`, if
`K` is a perfect object of `D(\mathcal O_\mathcal D)`, then the canonical projection-formula
morphism
`K \otimes_{\mathcal O_\mathcal D}^{\mathbf L} Rf_* E ⟶
  Rf_*(Lf^* K \otimes_{\mathcal O_\mathcal C}^{\mathbf L} E)`
is an isomorphism in `D(\mathcal O_\mathcal D)`. -/
theorem projectionFormulaMorphism_isIso_of_isPerfect
    (E : ModuleDerived X) (K : ModuleDerived Y)
    (hK : DerivedCategory.IsPerfect K) :
    IsIso
      (projectionFormulaMorphism
        (modulePullbackDerived f)
        (modulePushforwardDerived f)
        adj
        (fun A B ↦ pullbackTensorComparison B A)
        E
        K) := sorry

end

end RingedSite.Hom

/-! ### Remark_21_50_2 (from Chap21) -/
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
