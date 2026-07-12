import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe uE vE uO vO

section

variable {DE : Type uE} {DO : Type uO}
variable [Category.{vE} DE] [Category.{vO} DO]
variable [HasShift DE ℤ] [HasShift DO ℤ]
variable (derivedTensorWithK : DE ⥤ DO) [derivedTensorWithK.CommShift ℤ]
variable (M N : DE) (n : ℤ)

/- Source/core/bridge triage:
- source-facing: the map on `Ext^n`, represented in this chapter by `Hom(M, N[n])`;
- core/canonical: `ShiftedHom.map`;
- bridge/view: spelling that canonical map as an ordinary morphism into the shifted target.
-/

/-
Lemma 22.35.4: the functor `- \otimes_E^{\mathbf L} K^\bullet : D(E,d) ⥤ D(𝒪)` of
Lemma `22.35.3` induces, for every `M`, `N`, and `n`, the canonical maps on Ext groups. In the
current Chapter `22` API, degree-`n` Ext is represented by morphisms `M ⟶ N[n]`, so this source
map is exactly the specialization of the canonical owner `ShiftedHom.map`.
-/
recall ShiftedHom.map

/-- Source-facing normal form for the canonical Ext map induced by the derived tensor functor. -/
@[stacks 0CS6]
theorem derivedTensorWithK_extMap_apply
    (f : M ⟶ (shiftFunctor DE n).obj N) :
    ShiftedHom.map f derivedTensorWithK =
      derivedTensorWithK.map f ≫ (derivedTensorWithK.commShiftIso n).hom.app N :=
  rfl

set_option linter.hashCommand false in
#check
  (fun f : M ⟶ (shiftFunctor DE n).obj N ↦ ShiftedHom.map f derivedTensorWithK :
    (M ⟶ (shiftFunctor DE n).obj N) →
      (derivedTensorWithK.obj M ⟶ (shiftFunctor DO n).obj (derivedTensorWithK.obj N)))

end
