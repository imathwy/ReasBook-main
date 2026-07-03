import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)}

/-
Domain-style sampling for Definition 17.29.1:
- primary domain: differential operators between sheaves of modules after restriction of scalars
  along a morphism of sheaves of commutative rings;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.restrictScalars`,
  `ringSheafMap`,
  `LinearMap.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the opens-site owner in `TopCat.Sheaf`, obtained by evaluating a
  restricted-scalar sheaf morphism on each open set and reusing the linear-map owner;
- primitive data: a morphism
  `D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
    (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢`;
- derived API: the order-zero sectionwise linearity criterion.

Source/core/bridge triage:
- `source-facing`: Definition 17.29.1, relative differential operators on a topological space;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation of `D` on each open set `U`, yielding the sectionwise linear map
  `appLinearMap φ D U` and predicate `appIsDifferentialOperatorOfOrder φ D U k`.
-/

/-- The `\mathcal O_1(U)`-linear map on sections induced by `D`. -/
abbrev appLinearMap
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    (U : (Opens X)ᵒᵖ) :=
  (D.val.app U).hom

/-- The objectwise order-`k` differential-operator condition on sections over `U`. -/
def appIsDifferentialOperatorOfOrder
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    (U : (Opens X)ᵒᵖ) (k : ℕ) : Prop :=
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap φ).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap φ).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) := inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) := inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U := appLinearMap φ D U
  DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) k

/-- Definition 17.29.1: an `\mathcal O_1`-linear morphism between the restrictions of scalars of
two `\mathcal O_2`-module sheaves is a differential operator of order `k` when each objectwise
map on sections is an order-`k` differential operator over
`\mathcal O_1(U) → \mathcal O_2(U)`. -/
def IsDifferentialOperatorOfOrder
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢) : ℕ → Prop
  | k => ∀ U : (Opens X)ᵒᵖ, appIsDifferentialOperatorOfOrder φ D U k

/-- Objectwise characterization of opens-site differential operators of order `k`. -/
theorem isDifferentialOperatorOfOrder_app
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (U : (Opens X)ᵒᵖ) :
    appIsDifferentialOperatorOfOrder φ D U k :=
  hD U

end

end TopCat.Sheaf
