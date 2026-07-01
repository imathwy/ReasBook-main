import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

section

variable [∀ ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension ℱ]
variable (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (𝒢 : Dᵒᵖ ⥤ AddCommGrpCat.{w})

/- Domain-style sampling for Lemma 18.16.2:
- primary domain: adjunctions defining lower shriek / inverse-image for presheaves and sheaves of
  abelian groups on sites;
- sampled owner declarations:
  `CategoryTheory.Functor.lanAdjunction`,
  `CategoryTheory.Functor.sheafAdjunctionContinuous`,
  `Definition_18_16_1`'s canonical lower-shriek owners `u.op.lan` and
  `u.sheafPullback AddCommGrpCat J K`,
  `Lemma_18_13_2`'s direct recall of the same adjunction pattern for module sheaves;
- best owner abstractions: `CategoryTheory.Functor.lanAdjunction` for the presheaf-level lower
  shriek and `CategoryTheory.Functor.sheafAdjunctionContinuous` for the sheaf-level lower shriek;
- primitive data: the site functor `u`, continuity for the sheaf clause, and the standard
  Kan-extension / sheafification existence hypotheses;
- derived API: the Hom-set bijections obtained from these owner adjunctions via `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the textbook Hom-set equivalences for lower shriek versus inverse image on
  abelian presheaves and abelian sheaves;
- `core/canonical`: the owner adjunctions
  `u.op.lanAdjunction AddCommGrpCat` and
  `u.sheafAdjunctionContinuous AddCommGrpCat J K`;
- `bridge/view`: the specializations of `.homEquiv` at concrete objects `ℱ` and `𝒢`.

This item is therefore a canonical-recall item: it should recall the owner adjunctions directly
and keep the Hom-set equivalences only as thin companions. -/

/- Lemma 18.16.2 (1), owner form: the presheaf-level lower shriek on abelian presheaves is the
adjunction `u.op.lan ⊣ (Functor.whiskeringLeft _ _ _).obj u.op`. -/
recall CategoryTheory.Functor.lanAdjunction

/- Lemma 18.16.2 (1): for abelian-group-valued presheaves, the lower shriek `g_{p!}` is the
left Kan extension `u.op.lan`, left adjoint to pullback `u^p`; equivalently, there is a
canonical bifunctorial hom-set equivalence
`Mor((u.op.lan).obj ℱ, 𝒢) ≃ Mor(ℱ, u^p 𝒢)`. -/
#check
  (((u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv ℱ 𝒢) :
    ((u.op.lan).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ u.op ⋙ 𝒢))

variable [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable (ℱ : Sheaf J AddCommGrpCat.{w}) (𝒢 : Sheaf K AddCommGrpCat.{w})

/- Lemma 18.16.2 (2), owner form: the sheaf-level lower shriek on abelian sheaves is the
adjunction `u.sheafPullback AddCommGrpCat J K ⊣
u.sheafPushforwardContinuous AddCommGrpCat J K`. -/
recall CategoryTheory.Functor.sheafAdjunctionContinuous

/- Lemma 18.16.2 (2): for abelian sheaves, the lower shriek `g_!`, implemented by
`u.sheafPullback AddCommGrpCat J K`, is left adjoint to the inverse-image functor
`u.sheafPushforwardContinuous AddCommGrpCat J K`; equivalently, there is a canonical
bifunctorial hom-set equivalence
`Mor((u.sheafPullback AddCommGrpCat J K).obj ℱ, 𝒢) ≃
  Mor(ℱ, (u.sheafPushforwardContinuous AddCommGrpCat J K).obj 𝒢)`. -/
#check
  (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv ℱ 𝒢) :
    ((u.sheafPullback AddCommGrpCat.{w} J K).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj 𝒢))

end

end CategoryTheory
