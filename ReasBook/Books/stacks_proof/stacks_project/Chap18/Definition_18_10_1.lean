import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap06.Definition_6_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{u})

/- Domain-style sampling for Definition 18.10.1:
- primary domain: sheaves of modules over a ring-valued sheaf on a site;
- sampled owner abstractions:
  `SheafOfModules`,
  `SheafOfModules.forget`,
  `SheafOfModules.toSheaf`,
  `Mod`;
- source-facing layer: the Stacks notation `Mod(𝒪)` for the category of sheaves of `𝒪`-modules
  on the site `(C, J)`;
- core/canonical owner: `SheafOfModules 𝒪`;
- bridge/view layer: the notation `Mod(𝒪)` from Definition 6.10.1 on top of the canonical owner;
- primitive data versus derived API: `SheafOfModules` already owns the module-valued sheaf data,
  while the underlying presheaf-of-modules and underlying sheaf of abelian groups are derived by
  the canonical functors `SheafOfModules.forget` and `SheafOfModules.toSheaf`.

This item is therefore a bridge/view recall, not a new owner: it should expose the existing
canonical owner and source-facing notation directly, without a parallel local wrapper.
-/

/- Definition 18.10.1: for a site `C` and a sheaf of rings `𝒪` on `C`, the category
of sheaves of `𝒪`-modules is the canonical mathlib owner `SheafOfModules 𝒪`. On the
source-facing surface, Stacks writes the same category as `Mod(𝒪)`. -/
recall SheafOfModules

/- Source-facing bridge: the same category is written `Mod(𝒪)`. -/
#check Mod(𝒪)

variable (ℱ 𝒢 : Mod(𝒪))

/- Companion recall: morphisms of sheaves of `𝒪`-modules are morphisms in `Mod(𝒪)`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: the underlying presheaf of `𝒪`-modules of a sheaf of `𝒪`-modules is
obtained by the canonical forgetful functor `SheafOfModules.forget 𝒪`. -/
#check (SheafOfModules.forget 𝒪)

/- Companion recall: the underlying sheaf of abelian groups of a sheaf of `𝒪`-modules is
obtained by the canonical functor `SheafOfModules.toSheaf 𝒪`. -/
#check (SheafOfModules.toSheaf 𝒪)
