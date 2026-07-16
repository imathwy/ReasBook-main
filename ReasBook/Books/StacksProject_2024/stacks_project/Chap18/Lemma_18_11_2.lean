import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_9_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{u}]
variable [J.WEqualsLocallyBijective RingCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

/- Domain-style sampling for Lemma 18.11.2:
- primary domain: sheafification of presheaves of modules over a presheaf of rings on a site;
- sampled owner declarations:
  `CategoryTheory.toSheafify`,
  `PresheafOfModules.sheafification`,
  `PresheafOfModules.sheafificationAdjunction`,
  `ExactFunctor.of`;
- best owner abstraction: the bundled exact functor
  `ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪))`;
- primitive data: the ring-presheaf unit `toSheafify J 𝒪`;
- derived API: the source-facing exactness statement for the sheafification functor
  `PMod(𝒪) ⥤ Mod(𝒪^\#)`.

Source/core/bridge triage:
- `source-facing`: exactness of the sheafification functor on modules;
- `core/canonical`: `PresheafOfModules.sheafification (toSheafify J 𝒪)` and its bundled exact
  owner `ExactFunctor.of ...`;
- `bridge/view`: any unbundled exactness theorem here would only repackage
  `(ExactFunctor.of ...).property`.

This item is therefore a bridge/view recall: the file should expose the canonical bundled owner
directly, without introducing a parallel local theorem or alias. -/

/- Owner ingredients: the sheafified ring is `(presheafToSheaf J RingCat).obj 𝒪`, the comparison
map from the original ring presheaf is `toSheafify J 𝒪`, and module sheafification is the owner
functor `PresheafOfModules.sheafification (toSheafify J 𝒪)`. -/
recall CategoryTheory.toSheafify
recall PresheafOfModules.sheafification

/- Lemma 18.11.2: for a presheaf of rings `𝒪` on a site `(C, J)`, the sheafification functor
`PMod(𝒪) ⥤ Mod(𝒪^\#)` is exact; canonically, this is the bundled exact functor
`ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪))`. -/
#check
  (ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪)) :
    PMod(𝒪) ⥤ₑ Mod((presheafToSheaf J RingCat.{u}).obj 𝒪))

end
