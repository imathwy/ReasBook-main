import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap18.Lemma_18_28_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Definition 18.34.1:
- primary domain: differential operators between sheaves of modules on a ringed site;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the site-level owner
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`, obtained by evaluating a
  same-site restricted-scalar sheaf morphism objectwise and reusing the linear-map owner on
  sections;
- primitive data: a morphism of sheaves of commutative rings `φ : O₁ ⟶ O₂`, two `O₂`-module
  sheaves `F`, `G`, and an `O₁`-linear morphism between their restrictions of scalars along
  `restrictionAlong φ`;
- derived API: the objectwise evaluation lemma.

Source/core/bridge triage:
- `source-facing`: Definition 18.34.1, relative differential operators of order `k` on a site;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation at `X : Cᵒᵖ`, which turns a sheaf morphism after restriction of
  scalars into the corresponding `O₁(X)`-linear map between section modules over `O₂(X)`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}
variable {F G : ringedSiteModuleCategory J O₂}

/-- The `O₁(X)`-linear map on sections induced by a morphism after restriction of scalars. -/
abbrev appLinearMap
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (X : Cᵒᵖ) :=
  (D.val.app X).hom

/-- The objectwise order-`k` differential-operator condition on sections over `X`. -/
def appIsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (X : Cᵒᵖ) (k : ℕ) : Prop :=
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  let _ : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  let _ : Module (O₁.obj.obj X) (G.val.obj X) :=
    Module.compHom (G.val.obj X) (φ.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X)
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (F.val.obj X) := inferInstance
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G.val.obj X) := inferInstance
  let Dₓ : F.val.obj X →ₗ[O₁.obj.obj X] G.val.obj X := appLinearMap φ D X
  Dₓ.IsDifferentialOperatorOfOrder (O₂.obj.obj X) k

/-- Definition 18.34.1: an `O₁`-linear morphism between the restrictions of scalars of two
`O₂`-module sheaves is a differential operator of order `k` relative to `φ : O₁ ⟶ O₂` when each
objectwise map on sections is an order-`k` differential operator over the ring map
`O₁(X) → O₂(X)`. -/
def IsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) :
    ℕ → Prop
  | k =>
      ∀ X : Cᵒᵖ, appIsDifferentialOperatorOfOrder φ D X k

-- Proof sketch: this is the defining objectwise clause for
-- `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`.
omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Objectwise characterization of sheaf differential operators of order `k`. -/
theorem isDifferentialOperatorOfOrder_app
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    appIsDifferentialOperatorOfOrder φ D X k :=
  hD X

end SheafOfModules.RingedSite
