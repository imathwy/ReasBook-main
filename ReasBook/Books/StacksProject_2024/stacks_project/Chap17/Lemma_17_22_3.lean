import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_3

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

/-- The coextension-of-scalars functor
`𝒢 ↦ \mathcal H\!\mathit{om}_{\mathcal O_1}(\mathcal O_2, 𝒢)`. -/
noncomputable abbrev coextendScalars (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules (ringSheaf 𝒪₁) ⥤ SheafOfModules (ringSheaf 𝒪₂) :=
  -- Route correction: in this toolchain `SheafOfModules.restrictScalars` has no registered
  -- sheaf-level right adjoint, so the source-facing coextension functor must be constructed
  -- explicitly from the local-Hom sheaf rather than via `.rightAdjoint`.
  -- TODO: replace this placeholder by the concrete sheaf `U ↦ Hom_{𝒪₁|U}(𝒪₂|U, 𝒢|U)`.
  sorry

/-- Lemma 17.22.3, owner form: restriction of scalars along `α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to
the coextension-of-scalars functor
`𝒢 ↦ \mathcal H\!\mathit{om}_{𝒪₁}(\mathcal O_2, 𝒢)`. -/
noncomputable def restrictCoextendScalarsAdj (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules.restrictScalars (ringSheafMap α) ⊣ coextendScalars α :=
  -- Route correction: the planned owner proof fails because no instance
  -- `(SheafOfModules.restrictScalars (ringSheafMap α)).IsLeftAdjoint` is available here.
  -- TODO: once `coextendScalars α` is defined concretely, build the adjunction from the
  -- local module-level bijection `ModuleCat.restrictCoextendScalarsAdj` on each slice site.
  sorry

end TopCat.Sheaf
