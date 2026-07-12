import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local notation "TopOpenY" => (⊤ : Opens Y.carrier)

/- Domain-style sampling for Remark `20.13.2`.
- primary domain: global sections of sheaves of `𝒪_X`-modules on ringed spaces and their
  behavior under direct image, viewed in the target section ring by restriction of scalars;
- sampled owner declarations:
  `moduleSectionsRestrictionFunctor`,
  `moduleGlobalSectionsFunctor`,
  `RingedSpace.Hom.pushforward`,
  `globalSectionsRing`;
- best owner abstraction: the source-facing remark is the top-open specialization of the
  sections-on-open/pushforward comparison, with the
  `Γ(Y, 𝒪_Y)`-module structure carried by `moduleSectionsRestrictionFunctor`;
- primitive data: the ringed-space morphism `f : X ⟶ Y` and the module sheaf `ℱ : Modules X`;
- derived API: the single source-facing module-level specialization below;
- source/core/bridge triage:
  `source-facing`: the global-sections comparison for `f_*` as a statement in
    `ModuleCat (globalSectionsRing Y)`;
  `core/canonical`: `globalSectionsRing`, `moduleGlobalSectionsFunctor`,
    `RingedSpace.Hom.pushforward`, and `moduleSectionsRestrictionFunctor`;
  `bridge/view`: specializing the sections-on-open comparison to `V = ⊤` and evaluating at `ℱ`.

This remark adds no new owner-level data beyond those existing declarations, so it should keep only
the top-open specialization instead of a parallel additive-group wrapper.
-/

/-- Remark 20.13.2: for `f : X ⟶ Y`, global sections of `f_* ℱ` are exactly the global
sections of `ℱ` viewed as a `Γ(Y, 𝒪_Y)`-module by restriction of scalars along
`Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
@[stacks 01F0]
theorem pushforward_globalSections_eq_restrictedGlobalSections
    (f : X ⟶ Y) (ℱ : Modules X) :
    (moduleSectionsRestrictionFunctor f TopOpenY).obj
        ((moduleGlobalSectionsFunctor X).obj ℱ) =
      (moduleGlobalSectionsFunctor Y).obj ((f _*).obj ℱ) := rfl

end AlgebraicGeometry.RingedSpace
