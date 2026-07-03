import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Definition_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.PreservesSheafification AddCommGrpCat.free]
variable (𝒢 : Cᵒᵖ ⥤ Type v)

/- Domain-style sampling for Definition 18.5.1:
- primary domain: sheafification on a site and postcomposition by the free abelian group functor;
- sampled owner declarations:
  `ℤ_ 𝒢`,
  `AddCommGrpCat.free`,
  `Sheaf.composeAndSheafify`,
  `presheafToSheafCompComposeAndSheafifyIso`,
  `sheafifyComposeIso`;
- best owner abstraction: the sheaf-level owner `Sheaf.composeAndSheafify J AddCommGrpCat.free`;
- primitive data: the site `(C, J)`, a set-valued presheaf `𝒢`, and the chapter owner
  `ℤ_ 𝒢 := 𝒢 ⋙ AddCommGrpCat.free`;
- derived API: the source-facing owner `freeAbelianSheaf J 𝒢`, written `(ℤ_ 𝒢)^#[J]`, and its
  canonical comparison to the owner-level construction.

Source/core/bridge triage:
- `source-facing`: the free abelian sheaf `(ℤ_ 𝒢)^#`;
- `core/canonical`: `Sheaf.composeAndSheafify J AddCommGrpCat.free`;
- `bridge/view`: `presheafToSheafCompComposeAndSheafifyIso`, with
  `sheafifyComposeIso` as its objectwise specialization. -/

/-- The free abelian sheaf `(ℤ_ 𝒢)^#` on a set-valued presheaf `𝒢`. -/
abbrev freeAbelianSheaf : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (ℤ_ 𝒢)

namespace FreeAbelianSheaf

/- Textbook notation for the free abelian sheaf `(ℤ_ 𝒢)^#`. Since the site is not inferable from
the presheaf `𝒢`, we keep it explicit in the notation `(ℤ_ 𝒢)^#[J]`. -/
scoped notation:max "(ℤ_ " G ")^#[" J "]" =>
  CategoryTheory.freeAbelianSheaf J G

end FreeAbelianSheaf

open scoped FreeAbelianSheaf

/- Definition 18.5.1: the free abelian sheaf `(ℤ_ 𝒢)^#` is obtained by sheafifying the free
abelian presheaf `ℤ_ 𝒢`. -/
#check ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{v})

/- Companion recall: the sheaf-level owner is `Sheaf.composeAndSheafify`. -/
recall CategoryTheory.Sheaf.composeAndSheafify

#check (Sheaf.composeAndSheafify J AddCommGrpCat.free :
  Sheaf J (Type v) ⥤ Sheaf J AddCommGrpCat.{v})

/- Companion bridge: the owner-level free-abelian-sheaf construction on `𝒢^#` identifies
canonically with the source-facing object `(ℤ_ 𝒢)^#`. -/
#check ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app 𝒢 :
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ((presheafToSheaf J (Type v)).obj 𝒢) ≅
    (ℤ_ 𝒢)^#[J])

end

end CategoryTheory
