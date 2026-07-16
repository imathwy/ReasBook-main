import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf
open scoped RingedSite.Hom RingedSiteDerived RingedSiteDerivedSections

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]
variable [Functor.Additive f.modulePushforward]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived Y) (ModuleQis Y)]

local notation "Mod(" X ")" => ModuleCat X
local notation "single0" => DerivedCategory.singleFunctor (Mod(X)) (0 : ℤ)

/-
Domain-style sampling for Remark 21.14.4:
- primary domain: derived global-sections comparison for direct image of sheaves of modules on a
  ringed site;
- sampled owner declarations:
  `modulePushforwardDerived_globalSectionsComparison_isIso`,
  `modulePushforwardDerived`,
  `moduleGlobalSectionsDerived`;
- best owner abstraction:
  the source-facing content is already owned by
  the `IsIso` statement for the canonical derived comparison from Lemma `21.20.5`, and the
  degree-zero statement for a module sheaf `ℱ` is only its specialization to `ℱ[0]`;
- primitive data:
  a morphism of ringed sites `f : X ⟶ Y` and a module sheaf `ℱ` on `X`;
- derived API:
  the canonical comparison isomorphism and its degree-zero component.

Source/core/bridge triage:
- `source-facing`: the Leray comparison `RΓ(𝒟, -) ∘ Rf_* ≅ RΓ(𝒞, -)` and its specialization to
  `ℱ[0]`;
- `core/canonical`: `modulePushforwardDerived_globalSectionsComparison_isIso`,
  `modulePushforwardDerived`, and `moduleGlobalSectionsDerived`;
- `bridge/view`: passing from a module sheaf `ℱ` to the derived object `ℱ[0]`.
-/

/- Remark 21.14.4: the source-facing comparison
`RΓ(𝒟, -) ∘ Rf_* ≅ RΓ(𝒞, -)` is already the canonical derived comparison of Lemma `21.20.5`,
and its isomorphism statement is the instance
`modulePushforwardDerived_globalSectionsComparison_isIso`. -/
recall modulePushforwardDerived_globalSectionsComparison_isIso

variable (ℱ : Mod(X))

/- Remark 21.14.4, degree-zero specialization: for a module sheaf `ℱ`, the comparison
`RΓ(𝒟, Rf_*(ℱ[0])) ≅ RΓ(𝒞, ℱ[0])` is exactly the specialization of
`modulePushforwardDerived_globalSectionsComparison_app_isIso` at `ℱ[0]`; no separate owner is
needed. -/
#check modulePushforwardDerived_globalSectionsComparison_app_isIso f ((single0).obj ℱ)

end

end RingedSite.Hom

end
