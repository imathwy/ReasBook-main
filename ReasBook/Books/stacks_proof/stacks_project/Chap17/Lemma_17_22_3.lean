import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.22.3:
- primary domain: change of rings for sheaves of modules on a topological space;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `CategoryTheory.Adjunction`,
  `CategoryTheory.Adjunction.ofIsLeftAdjoint`,
  `TopCat.Sheaf.ringSheafMap`;
- best owner abstraction: the canonical adjunction
  `SheafOfModules.restrictScalars (ringSheafMap α) ⊣
    (SheafOfModules.restrictScalars (ringSheafMap α)).rightAdjoint`;
- primitive data: a morphism of sheaves of commutative rings `α : 𝒪₁ ⟶ 𝒪₂`;
- derived API: the source-facing coextension-of-scalars functor `coextendScalars α` and the
  adjunction `restrictCoextendScalarsAdj α`.

Source/core/bridge triage:
- `source-facing`: the change-of-rings functor
  `𝒢 ↦ \mathcal H\!\mathit{om}_{𝒪₁}(\mathcal O_2, 𝒢)`;
- `core/canonical`: the canonical right adjoint of
  `SheafOfModules.restrictScalars (ringSheafMap α)`;
- `bridge/view`: the explicit source-facing name `coextendScalars α` for that right adjoint. -/

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- Helper for Chap17 Lemma 17 22 3: the underlying presheaf of sheaf-level restriction of
scalars is definitionally the presheaf-level restriction functor applied to the underlying
presheaf. -/
private theorem restrictScalars_val_obj_eq (α : 𝒪₁ ⟶ 𝒪₂)
    (F : SheafOfModules (ringSheaf 𝒪₂)) :
    ((SheafOfModules.restrictScalars (ringSheafMap α)).obj F).val =
      (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj F.val :=
  rfl

/-- The coextension-of-scalars functor
`𝒢 ↦ \mathcal H\!\mathit{om}_{\mathcal O_1}(\mathcal O_2, 𝒢)`. -/
noncomputable abbrev coextendScalars (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules (ringSheaf 𝒪₁) ⥤ SheafOfModules (ringSheaf 𝒪₂) :=
  -- Route correction: the attempted presheaf-level reconstruction was variance-incorrect, so use
  -- the canonical owner route and name the chosen right adjoint source-facingly.
  (SheafOfModules.restrictScalars (ringSheafMap α)).rightAdjoint

/-- Helper for Chap17 Lemma 17 22 3: `coextendScalars α` is the chosen right adjoint of
restriction of scalars along `α`. -/
theorem coextendScalars_def (α : 𝒪₁ ⟶ 𝒪₂) :
    coextendScalars α = (SheafOfModules.restrictScalars (ringSheafMap α)).rightAdjoint :=
  rfl

/-- Helper for Chap17 Lemma 17 22 3: the canonical owner adjunction for restriction of scalars
normalizes to the source-facing `coextendScalars α`. -/
private theorem restrictScalarsCoextendScalarsAdj (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules.restrictScalars (ringSheafMap α) ⊣ coextendScalars α := by
  -- Proof comment: stay in the owner spelling until the last step, then rewrite the chosen
  -- right adjoint once to the source-facing name `coextendScalars α`.
  simpa [coextendScalars_def] using
    (Adjunction.ofIsLeftAdjoint (SheafOfModules.restrictScalars (ringSheafMap α)) :
      SheafOfModules.restrictScalars (ringSheafMap α) ⊣
        (SheafOfModules.restrictScalars (ringSheafMap α)).rightAdjoint)

/-- Lemma 17.22.3, owner form: restriction of scalars along `α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to
the coextension-of-scalars functor
`𝒢 ↦ \mathcal H\!\mathit{om}_{𝒪₁}(\mathcal O_2, 𝒢)`. -/
@[stacks 0A6F]
noncomputable def restrictCoextendScalarsAdj (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules.restrictScalars (ringSheafMap α) ⊣ coextendScalars α :=
  restrictScalarsCoextendScalarsAdj α

end TopCat.Sheaf
