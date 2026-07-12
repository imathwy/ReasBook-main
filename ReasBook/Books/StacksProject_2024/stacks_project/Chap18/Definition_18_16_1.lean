import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open Functor.sheafPullbackConstruction

/- Domain-style sampling for Definition 18.16.1:
- primary domain: lower shriek on abelian presheaves and abelian sheaves along a functor of
  sites, with continuity only for comparison to the chosen sheaf-level owner;
- sampled owner declarations:
  `Functor.lan`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lower shriek `g_{p!}` on abelian presheaves, together with the
    induced sheaf-level lower shriek given by sheafifying the presheaf lower shriek;
  `core/canonical`: the presheaf owner `u.op.lan` and, under continuity, the chosen sheaf owner
    `u.sheafPullback AddCommGrpCat J K`;
  `bridge/view`: the pointwise colimit formula
    `u.op.leftKanExtensionObjIsoColimit`, and, under continuity, the identification of the
    source-level sheaf construction
    `Functor.sheafPullbackConstruction.sheafPullback` with the canonical owner by
    `Functor.sheafPullbackConstruction.sheafPullbackIso`.

Primitive data are the functor `u`, the existence of left Kan extensions along `u.op`, and weak
sheafification on the target site; continuity is only primitive for the comparison with the chosen
sheaf-owner `u.sheafPullback`. The lower shriek owners and their pointwise/construction-level
descriptions are derived API already owned upstream, so this file should recall those owners
directly rather than keep parallel local `abelian...` wrappers.
-/

section PresheafLevel

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]

/- Definition 18.16.1, presheaf level: the abelian lower shriek is the canonical left Kan
extension along `u.op`, namely `u.op.lan`. -/
#check (u.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})

end

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseLeftKanExtension F]
variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Dᵒᵖ)

/- Companion bridge: the value of the presheaf lower shriek at `V` is the colimit over the
costructured-arrow category of arrows `V ⟶ u(U)`. -/
#check (u.op.leftKanExtensionObjIsoColimit F V :
  (u.op.leftKanExtension F).obj V ≅ colimit (CostructuredArrow.proj u.op V ⋙ F))

end

end PresheafLevel

section SheafLevel

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Definition 18.16.1, sheaf level: the source-facing lower shriek is obtained by applying the
presheaf lower shriek to the underlying presheaf and then sheafifying. -/
#check (sheafPullback u AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

end

section

variable [u.IsContinuous J K]
variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Companion bridge: under continuity, the canonical chosen sheaf owner for the abelian lower
shriek is `u.sheafPullback AddCommGrpCat J K`. -/
#check (u.sheafPullback AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

/- Companion bridge: the source-level construction by applying the presheaf lower shriek to the
underlying presheaf and then sheafifying is
`sheafPullback u AddCommGrpCat J K`. -/
#check (sheafPullback u AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

/- Companion bridge: the canonical owner and the source-level construction are canonically
isomorphic. -/
#check (sheafPullbackIso u AddCommGrpCat.{w} J K :
  u.sheafPullback AddCommGrpCat.{w} J K ≅
    sheafPullback u AddCommGrpCat.{w} J K)

end

end SheafLevel

end CategoryTheory
