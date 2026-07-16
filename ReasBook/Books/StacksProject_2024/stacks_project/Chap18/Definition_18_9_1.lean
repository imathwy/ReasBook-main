import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.Definition_6_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

/- Domain-style sampling for Definition 18.9.1:
- primary domain: presheaves of modules over a ring-valued presheaf on a category;
- sampled owner abstractions:
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `PresheafOfModules.map_smul`,
  `PMod`;
- primitive data versus derived API: `PresheafOfModules` already owns the objectwise module data
  and semilinear restriction maps as primitive fields, while the underlying presheaf of abelian
  groups and the morphism type are derived API.
- Source/core/bridge triage:
  - `source-facing`: the Stacks category `PMod(𝒪)` of presheaves of `𝒪`-modules on `C`;
  - `core/canonical`: `PresheafOfModules 𝒪`;
  - `bridge/view`: the existing project notation `PMod(𝒪)` from Definition `6.6.1`.

This file should therefore reuse the existing canonical owner and source-facing notation rather
than keep a parallel local presentation of the same category.
-/

/- Definition 18.9.1: for a category `C` and a presheaf of rings `𝒪` on `C`, the category
`PMod(𝒪)` of presheaves of `𝒪`-modules is the canonical mathlib owner `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing bridge: the same category is written `PMod(𝒪)`. -/
#check PMod(𝒪)
