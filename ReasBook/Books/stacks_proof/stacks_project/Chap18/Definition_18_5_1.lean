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

/- Domain-style sampling for Definition 18.5.1:
- primary domain: sheafification on a site and postcomposition by the free abelian group functor;
- sampled owner declarations:
  `presheafToSheaf`,
  `ℤ_ 𝒢`,
  `Sheaf.composeAndSheafify`,
  `presheafToSheafCompComposeAndSheafifyIso`,
  `sheafifyComposeIso`;
- best owner abstraction for the source-facing definition: the additive sheafification owner
  `(presheafToSheaf J AddCommGrpCat.{v}).obj`, applied to the free abelian presheaf `ℤ_ 𝒢`;
- primitive data: the site `(C, J)`, the set-valued presheaf `𝒢`, and the chapter owner
  `ℤ_ 𝒢 := 𝒢 ⋙ AddCommGrpCat.free`;
- derived API: the notation `(ℤ_ 𝒢)^#[J]` for that sheafification, and under the stronger
  preservation hypothesis the comparison with the sheaf-level bridge owner
  `Sheaf.composeAndSheafify J AddCommGrpCat.free`.

Source/core/bridge triage:
- `source-facing`: the free abelian sheaf `(ℤ_ 𝒢)^#`;
- `core/canonical`: `(presheafToSheaf J AddCommGrpCat.{v}).obj (ℤ_ 𝒢)`;
- `bridge/view`: under `[J.PreservesSheafification AddCommGrpCat.free]`, the owner
  `Sheaf.composeAndSheafify J AddCommGrpCat.free` and the comparison
  `presheafToSheafCompComposeAndSheafifyIso`, with `sheafifyComposeIso` as its
  underlying-presheaf specialization. -/

section SourceFacing

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable (𝒢 : Cᵒᵖ ⥤ Type v)

namespace FreeAbelianSheaf

/- Textbook notation for the free abelian sheaf `(ℤ_ 𝒢)^#`. Since the site is not inferable from
the presheaf `𝒢`, we keep it explicit in the notation `(ℤ_ 𝒢)^#[J]` and attach it directly to the
canonical sheafification owner `(presheafToSheaf J AddCommGrpCat.{v}).obj (ℤ_ 𝒢)`. -/
set_option quotPrecheck false in
scoped notation:max "(ℤ_ " G ")^#[" J "]" =>
  Functor.obj (CategoryTheory.presheafToSheaf J AddCommGrpCat) (ℤ_ G)

end FreeAbelianSheaf

open scoped FreeAbelianSheaf

/- Definition 18.5.1: the free abelian sheaf `(ℤ_ 𝒢)^#` is obtained by sheafifying the free
abelian presheaf `ℤ_ 𝒢`. -/
#check ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{v})

end SourceFacing

open scoped FreeAbelianSheaf

section BridgeOwner

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/- Companion recall: the sheaf-level bridge owner is `Sheaf.composeAndSheafify`. -/
recall CategoryTheory.Sheaf.composeAndSheafify

#check (Sheaf.composeAndSheafify J AddCommGrpCat.free :
  Sheaf J (Type v) ⥤ Sheaf J AddCommGrpCat.{v})

end BridgeOwner

section BridgeComparison

variable [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.PreservesSheafification AddCommGrpCat.free]
variable (𝒢 : Cᵒᵖ ⥤ Type v)

/- Companion bridge: under the sheafification-preservation hypothesis, the owner-level
free-abelian-sheaf construction on `𝒢^#` identifies canonically with the source-facing object
`(ℤ_ 𝒢)^#`. -/
#check CategoryTheory.presheafToSheafCompComposeAndSheafifyIso

#check ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app 𝒢 :
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ((presheafToSheaf J (Type v)).obj 𝒢) ≅
    ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{v}))

end BridgeComparison

end

end CategoryTheory
