import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_13_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 18.26.2:
- primary domain: inverse image of sheaves of modules on a ringed site, together with the
  canonical tensor-product comparison for pullback;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `RingedSite.Hom.(^*)`,
  `CategoryTheory.Functor.Monoidal.μIso`,
  the canonical monoidal tensor on `SheafOfModules X.structureSheaf` and
  `SheafOfModules Y.structureSheaf`;
- best owner abstraction: the source-facing owner is the pullback functor `f^*` on module sheaves
  over the structure sheaves of `Y` and `X`, together with the canonical tensor on those module
  categories; the generic monoidal comparison `Functor.Monoidal.μIso` should remain only the core
  implementation of that source-facing tensor comparison;
- primitive data: a morphism of ringed sites `f : X ⟶ Y`, module sheaves `ℱ`, `𝒢`, and the
  monoidal structures on the source and target module categories together with the monoidal
  structure on `f^*`;
- derived API: the canonical comparison morphism and isomorphism
  `f^*(ℱ ⊗ 𝒢) ⟶ f^*ℱ ⊗ f^*𝒢` and
  `f^*(ℱ ⊗ 𝒢) ≅ f^*ℱ ⊗ f^*𝒢`.

Source/core/bridge triage:
- `source-facing`: the pullback-tensor comparison for sheaves of modules on a ringed site;
- `core/canonical`: `Functor.Monoidal.μIso` specialized to the pullback owner `f^*`;
- `bridge/view`: the scoped notation `f^*` from the chapter owner and the ambient tensor notation
  coming from the monoidal structures on the module categories. -/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [Functor.Monoidal (f^*)]

local notation "ModY" => SheafOfModules Y.structureSheaf

/-- Lemma 18.26.2: for a morphism of ringed sites `f : X ⟶ Y`, pullback on sheaves of modules
preserves the canonical tensor product up to the canonical comparison isomorphism. -/
noncomputable abbrev pullbackTensorIso (ℱ 𝒢 : ModY) :
    (f^*).obj (ℱ ⊗ 𝒢) ≅ ((f^*).obj ℱ ⊗ (f^*).obj 𝒢) :=
  (Functor.Monoidal.μIso (f^*) ℱ 𝒢).symm

/-- The canonical pullback-tensor comparison morphism for a morphism of ringed sites. -/
noncomputable abbrev pullbackTensorComparison (ℱ 𝒢 : ModY) :
    (f^*).obj (ℱ ⊗ 𝒢) ⟶ ((f^*).obj ℱ ⊗ (f^*).obj 𝒢) :=
  (pullbackTensorIso f ℱ 𝒢).hom

end RingedSite.Hom
