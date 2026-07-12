import Mathlib
import StacksProject_2024.Chap10.Lemma_10_133_2
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

noncomputable section

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.34.2:
- primary domain: differential operators between sheaves of modules on a ringed site, obtained by
  evaluating morphisms on sections;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`,
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_app`,
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the algebraic composition theorem
  `LinearMap.isDifferentialOperatorOfOrder_comp`; the ringed-site statement is its objectwise
  bridge;
- primitive data: a morphism of ring sheaves `φ : O₁ ⟶ O₂`, two composable morphisms after
  restriction of scalars along `φ` between `O₂`-module sheaves, and the
  order bounds on their objectwise section maps;
- derived API: this site-level closure theorem, used downstream by the principal-parts functor.

Source/core/bridge triage:
- `source-facing`: Lemma 18.34.2, closure of ringed-site differential operators under composition;
- `core/canonical`: `LinearMap.isDifferentialOperatorOfOrder_comp`;
- `bridge/view`: evaluation at `X : Cᵒᵖ`, via
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_app`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

-- Proof sketch: evaluate at each object of the site and apply the usual composition result for
-- objectwise differential operators, whose orders add under composition.
omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 18.34.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `O₂`-modules is a differential operator of order `k + k'`. -/
@[stacks 09CS]
theorem isDifferentialOperatorOfOrder_comp
    (φ : O₁ ⟶ O₂)
    {E F G : ringedSiteModuleCategory J O₂}
    {k k' : ℕ}
    {D : (restrictionAlong φ).obj E ⟶ (restrictionAlong φ).obj F}
    {D' : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k)
    (hD' : IsDifferentialOperatorOfOrder φ D' k') :
    IsDifferentialOperatorOfOrder φ (D ≫ D') (k + k') := by
  intro X
  simpa using LinearMap.isDifferentialOperatorOfOrder_comp
    (isDifferentialOperatorOfOrder_app φ D hD X)
    (isDifferentialOperatorOfOrder_app φ D' hD' X)

end SheafOfModules.RingedSite
