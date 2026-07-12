import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.Chap10.Definition_10_133_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Definition 18.34.1:
- primary domain: differential operators between sheaves of modules on a ringed site;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.restrictScalars`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.restrictionAlong`;
- best owner abstraction: the site-level owner
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`, obtained by evaluating a
  same-site restriction-of-scalars morphism objectwise inside the canonical owner
  `ringedSiteModuleCategory J` and reusing the thin bridge `restrictionAlong φ`
  together with the linear-map owner on sections;
- primitive data: a morphism of sheaves of commutative rings `φ : O₁ ⟶ O₂`, two `O₂`-module
  sheaves `F`, `G` in `ringedSiteModuleCategory J O₂`, and an `O₁`-linear morphism
  between their restrictions of scalars `(restrictionAlong φ).obj F ⟶
  (restrictionAlong φ).obj G`;
- derived API: the objectwise evaluation theorem on sections.

Source/core/bridge triage:
- `source-facing`: Definition 18.34.1, relative differential operators of order `k` on a site;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation at `X : Cᵒᵖ`, which turns a sheaf morphism after restriction of
  scalars into the corresponding section map
  `((D.val.app X).hom)` with its canonical restricted `O₁(X)`-linear structure and ambient
  `O₂(X)`-action.

Primitive-vs-derived split:
- primitive data here is only the site-level owner predicate
  `IsDifferentialOperatorOfOrder`;
- the sectionwise reading is derived API and should remain theorem-shaped rather than a second
  public owner definition. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

/-- Helper for Definition 18.34.1: restriction of scalars along `φ` does not change the
underlying `O₂(X)`-section action, so the restricted section module inherits the canonical
distributive scalar action by `O₂(X)`. -/
instance sectionDistribSMul
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (X : Cᵒᵖ) :
    DistribSMul (O₂.obj.obj X) ↑(((restrictionAlong φ).obj F).val.obj X) :=
  inferInstanceAs (DistribSMul (O₂.obj.obj X) ↑(F.val.obj X))

/-- Helper for Definition 18.34.1: on restricted sections, the ambient `O₂(X)`-action commutes
with the `O₁(X)`-action induced by `φ`. -/
instance sectionSmulCommClass
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (X : Cᵒᵖ) :
    SMulCommClass (O₂.obj.obj X) ((ringSheaf J O₁).obj.obj X)
      ↑(((restrictionAlong φ).obj F).val.obj X) :=
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  let _ : Module (O₁.obj.obj X) ↑(F.val.obj X) := Module.compHom (F.val.obj X) (φ.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) ↑(F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  inferInstanceAs (SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) ↑(F.val.obj X))

/-- Definition 18.34.1: an `O₁`-linear morphism between the restrictions of scalars of two
`O₂`-module sheaves is a differential operator of order `k` relative to `φ : O₁ ⟶ O₂` when each
objectwise map on sections is an order-`k` differential operator over the ring map
`O₁(X) → O₂(X)`. -/
def IsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂)
    {F G : Mod(O₂)}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (k : ℕ) : Prop :=
  ∀ X : Cᵒᵖ,
    @LinearMap.IsDifferentialOperatorOfOrder
      ((ringSheaf J O₁).obj.obj X)
      ↑(((restrictionAlong φ).obj F).val.obj X)
      ↑(((restrictionAlong φ).obj G).val.obj X)
      _ _ _ _ _
      ((D.val.app X).hom)
      (O₂.obj.obj X)
      (sectionDistribSMul φ F X)
      (sectionDistribSMul φ G X)
      (sectionSmulCommClass φ F X)
      (sectionSmulCommClass φ G X)
      k

/-- Objectwise characterization of sheaf differential operators of order `k`. -/
theorem isDifferentialOperatorOfOrder_app
    (φ : O₁ ⟶ O₂)
    {F G : Mod(O₂)}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    @LinearMap.IsDifferentialOperatorOfOrder
      ((ringSheaf J O₁).obj.obj X)
      ↑(((restrictionAlong φ).obj F).val.obj X)
      ↑(((restrictionAlong φ).obj G).val.obj X)
      _ _ _ _ _
      ((D.val.app X).hom)
      (O₂.obj.obj X)
      (sectionDistribSMul φ F X)
      (sectionDistribSMul φ G X)
      (sectionSmulCommClass φ F X)
      (sectionSmulCommClass φ G X)
      k := by
  -- Proof comment: the sheaf-level predicate is defined objectwise, so evaluation is immediate.
  exact hD X

end SheafOfModules.RingedSite
