import Mathlib
import stacks_project.Chap10.Lemma_10_133_2
import stacks_project.Chap17.Definition_17_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable {ℱ 𝒢 ℋ : SheafOfModules (ringSheaf 𝒪₂)}

/- Domain-style sampling for Lemma 17.29.2:
- primary domain: differential operators between sheaves of modules relative to a morphism of ring
  sheaves;
- sampled owner declarations:
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.appIsDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.appLinearMap`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`;
- best owner abstraction: the opens-site owner
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`, obtained by evaluating on opens and reusing the
  algebraic composition theorem;
- primitive data: a morphism
  `D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
    (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢`;
- derived API: closure of that owner under composition.

Source/core/bridge triage:
- `core/canonical`: `LinearMap.isDifferentialOperatorOfOrder_comp`;
- `source-facing`: the opens-site owner
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- `bridge/view`: the opens-site specialization along `ringSheafMap varphi`.

This file should therefore reuse the algebraic composition theorem on each open set rather than
import a later same-site wrapper. -/

-- Proof sketch: evaluate both morphisms on an open set and apply the algebraic composition theorem
-- for differential operators over `𝒪₁(U) → 𝒪₂(U)`.
/-- Lemma 17.29.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `\mathcal O_2`-modules is a differential operator of order `k + k'`. -/
theorem isDifferentialOperatorOfOrder_comp (varphi : 𝒪₁ ⟶ 𝒪₂)
    {k k' : ℕ}
    {D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢}
    {D' : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢 ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℋ}
    (hD : IsDifferentialOperatorOfOrder varphi D k)
    (hD' : IsDifferentialOperatorOfOrder varphi D' k') :
    IsDifferentialOperatorOfOrder varphi (D ≫ D') (k + k') := by
  intro U
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (ℋ.val.obj U) :=
    Module.compHom (ℋ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℋ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℋ.val.obj U)
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℋ.val.obj U) :=
    inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U :=
    appLinearMap varphi D U
  let D'U : 𝒢.val.obj U →ₗ[𝒪₁.obj.obj U] ℋ.val.obj U :=
    appLinearMap varphi D' U
  simpa [appIsDifferentialOperatorOfOrder] using
    LinearMap.isDifferentialOperatorOfOrder_comp (D := DU) (D' := D'U) (hD U) (hD' U)

end
