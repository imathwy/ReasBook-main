import StacksProject_2024.Chap20.«20_54_2_1»
import StacksProject_2024.Chap21.Remark_21_35_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

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

/- Domain-style sampling for 21.50.0.1:
- primary domain: projection-formula morphisms in monoidal derived categories attached to ringed
  sites;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.projectionFormulaMorphism`,
  `RingedSite.Hom.relativeCupProductMap`,
  `RingedSite.Hom.modulePullbackDerived`;
- best owner abstraction:
  `source-facing`: the ringed-site projection-formula morphism for `f`;
  `core/canonical`: `CategoryTheory.projectionFormulaMorphism`;
  `bridge/view`: the explicit unit-then-cup formula below;
- primitive data: `modulePullbackDerived f`, `modulePushforwardDerived f`, `adj`, and
  `pullbackTensorComparison`;
- derived API: the explicit composite formula for the canonical owner in the ringed-site setting. -/

/- 21.50.0.1 recalls the generic projection-formula morphism in the ringed-site setting. -/
#check
  (_root_.CategoryTheory.projectionFormulaMorphism
    (modulePullbackDerived f)
    (modulePushforwardDerived f)
    adj
    (fun A B ↦ pullbackTensorComparison B A))

-- Proof sketch: unfold `projectionFormulaMorphism`; it is defined as the tensor-with-unit map
-- `K ⊗ Rf_* E ⟶ Rf_* Lf^* K ⊗ Rf_* E` followed by the relative cup product for the pair
-- `(E, Lf^* K)`.
/-- The canonical projection-formula morphism
`K ⊗_{\mathcal O_Y}^{\mathbf L} Rf_* E ⟶
  Rf_*(Lf^* K ⊗_{\mathcal O_X}^{\mathbf L} E)`
is the composite of tensoring the adjunction unit `K ⟶ Rf_* Lf^* K` with `Rf_* E` and then
applying the relative derived cup product. -/
theorem projectionFormulaMorphism_def
    (E : ModuleDerived X)
    (K : ModuleDerived Y) :
    _root_.CategoryTheory.projectionFormulaMorphism
        (modulePullbackDerived f)
        (modulePushforwardDerived f)
        adj
        (fun A B ↦ pullbackTensorComparison B A)
        E
        K =
      ((adj.unit.app K) ⊗ₘ 𝟙 ((modulePushforwardDerived f).obj E)) ≫
        _root_.CategoryTheory.relativeDerivedCupProduct
          (modulePullbackDerived f)
          (modulePushforwardDerived f)
          adj
          (curriedTensor (ModuleDerived X))
          (curriedTensor (ModuleDerived Y))
          pullbackTensorComparison
          E
          ((modulePullbackDerived f).obj K) := rfl

end

end RingedSite.Hom
