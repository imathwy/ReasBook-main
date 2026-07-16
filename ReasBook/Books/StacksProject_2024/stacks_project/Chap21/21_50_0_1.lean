import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.«20_54_2_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for 21.50.0.1:
- primary domain: projection-formula morphisms in monoidal derived categories attached to ringed
  sites;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.projectionFormulaMorphism`,
  `RingedSite.Hom.modulePullbackDerived`;
- best owner abstraction:
  `source-facing`: the ringed-site projection-formula morphism for `f`;
  `core/canonical`: `projectionFormulaMorphism`;
  `bridge/view`: the explicit unit-then-cup formula below;
- primitive data: `L(f)^*`, `R(f)_*`, `adj`, and
  `pullbackTensorComparison`;
- derived API: the explicit composite formula for the canonical owner in the ringed-site setting. -/

/- Source/core/bridge triage:
- `source-facing`: the ringed-site projection-formula morphism of `21.50.0.1`;
- `core/canonical`: `projectionFormulaMorphism`;
- `bridge/view`: the definitional formula `projectionFormulaMorphism_def` for the
  ringed-site specialization.

This item introduces no new owner-level mathematics beyond that canonical declaration, so the
refined file should recall the owner directly rather than keep a local alias or shell definition.
-/

/- 21.50.0.1 is a pure recall item: in the ringed-site setting, the projection-formula morphism is
the generic owner `projectionFormulaMorphism`. -/
recall projectionFormulaMorphism

/- Companion recall: the ringed-site specialization unfolds by the generic formula
`projectionFormulaMorphism_def`. -/
recall projectionFormulaMorphism_def

namespace RingedSite.Hom

section

universe u v

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable (adj : L(f)^* ⊣ R(f)_*)
variable
  (modulePullbackDerivedTensorIso :
    ∀ L : DModY,
      (tensoringRight DModY).obj L ⋙ L(f)^* ≅
        L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))

/- Source-facing specialization: for a morphism of ringed sites `f`, the textbook projection-formula
map `K ⊗ R(f)_* E ⟶ R(f)_*(L(f)^* K ⊗ E)` is the generic categorical owner specialized to
`L(f)^*`, `R(f)_*`, the chosen adjunction `adj`, and the pullback-side tensor
comparison. -/
#check projectionFormulaMorphism (L(f)^*) (R(f)_*) adj
  (fun A B ↦ (modulePullbackDerivedTensorIso B).app A)

/- Companion source-facing specialization: the ringed-site projection-formula morphism unfolds by
tensoring the adjunction unit with `R(f)_* E` and then applying the relative cup product. -/
#check projectionFormulaMorphism_def (L(f)^*) (R(f)_*) adj
  (fun A B ↦ (modulePullbackDerivedTensorIso B).app A)

end

end RingedSite.Hom
