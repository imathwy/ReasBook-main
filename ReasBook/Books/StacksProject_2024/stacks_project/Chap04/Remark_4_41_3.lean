import Mathlib
import StacksProject_2024.stacks_project.Chap04.Example_4_37_1
import StacksProject_2024.stacks_project.Chap04.Definition_4_36_2
import StacksProject_2024.stacks_project.Chap04.Lemma_4_36_3
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_9
import StacksProject_2024.stacks_project.Chap04.Lemma_4_41_2_2_Yoneda_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u vX vY vZ uX uY uZ

namespace CategoryTheory

open BasedCategory
open Functor
open Opposite
open Pseudofunctor
open Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v₁} C]
variable {S : Type (max u v₁ v₂)} [Category.{max (max u v₁) v₂} S]

/- Domain-style sampling for Remark 4.41.3:
- primary domain: the `2`-Yoneda split model for a category fibred in groupoids over a fixed base.
- inspected owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsMor.ofBasedFunctor`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedCategory.ofFunctor`,
  `Pseudofunctor.CoGrothendieck.forget`,
  `Pseudofunctor.CoGrothendieck.groupoidPresheafProjection_isFibredInGroupoids`.
- best owner abstraction: the split model is the bundled object
  `twoYonedaSplitModel p : FibredInGroupoidsOver C`, and the comparison to the original fibred
  category should be exposed by the owner morphism
  `twoYonedaSplitModel p ⟶ FibredInGroupoidsOver.ofFunctor p`, with equivalence expressed by
  `FibredInGroupoidsMor.IsEquivalenceOverBase`.
- primitive data: the groupoid-valued presheaf `twoYonedaGroupoidPresheaf p` and its
  co-Grothendieck projection.
- derived API: the bundled split model and the canonical owner morphism to
  `FibredInGroupoidsOver.ofFunctor p`.

Source/core/bridge triage:
- `source-facing`: the split model `S'` and the comparison functor `G : S' ⥤ S` from the remark.
- `core/canonical`: `FibredInGroupoidsOver C`, its owner homs `X ⟶ Y`, and
  `FibredInGroupoidsMor.IsEquivalenceOverBase`.
- `bridge/view`: the explicit co-Grothendieck presentation and the evaluation-at-identity formula
  for the underlying functor over `C`.
-/

private abbrev twoYonedaSliceChange {U V : C} (f : U ⟶ V) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor (Over.forget V) :=
  { toFunctor := Over.map f
    w := Over.mapForget_eq f }

private def precomposeBasedFunctor
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (φ : X ⥤ᵇ Y) :
    (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) where
  obj F := BasedFunctor.comp φ F
  map τ := BasedCategory.whiskerLeft φ τ
  map_id := by
    intro F
    ext a
    simp [BasedCategory.whiskerLeft]
  map_comp := by
    intro F G H τ σ
    ext a
    simp [BasedCategory.whiskerLeft]

private noncomputable instance
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    IsGroupoid (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) where
  all_isIso := by
    intro F G τ
    letI : ∀ a : Over U, IsIso (τ.toNatTrans.app a) := fun a ↦ by
      letI : p.IsHomLift (𝟙 ((Over.forget U).obj a)) (τ.toNatTrans.app a) := τ.isHomLift' a
      haveI :
          IsIso
            (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a)) :=
        IsFibredInGroupoids.hom_isIso ((Over.forget U).obj a)
          (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a))
      haveI : IsIso (τ.toNatTrans.app a) := by
        simpa using
          (inferInstance :
            IsIso
              (Fiber.fiberInclusion.map
                (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a))))
      infer_instance
    let τ' : F.toFunctor ⟶ G.toFunctor := τ.toNatTrans
    have hτ : IsIso τ' := NatIso.isIso_of_isIso_app τ'
    letI := hτ
    exact BasedNatIso.isIso_of_toNatTrans_isIso τ

private noncomputable instance (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    Groupoid (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :=
  Groupoid.ofIsGroupoid

private noncomputable abbrev twoYonedaGroupoidPresheafValue
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :=
  Grpd.of (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p)

private abbrev twoYonedaGroupoidPresheafMap
    (p : S ⥤ C) [IsFibredInGroupoids p] {U V : C} (f : U ⟶ V) :
    twoYonedaGroupoidPresheafValue p V ⥤
      twoYonedaGroupoidPresheafValue p U :=
  show twoYonedaGroupoidPresheafValue p V ⥤ twoYonedaGroupoidPresheafValue p U from
    precomposeBasedFunctor (twoYonedaSliceChange f)

-- Proof sketch: `Over.map (𝟙 U)` is naturally isomorphic to the identity on `C/U`, so
-- precomposition with it is naturally isomorphic to the identity on the over-base functor
-- category.
private theorem twoYonedaGroupoidPresheafMap_id
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : Cᵒᵖ) :
    twoYonedaGroupoidPresheafMap p (𝟙 (unop U)) = 𝟭 _ := sorry

-- Proof sketch: `Over.map` is functorial in the base morphism, so precomposition with
-- `Over.map ((f ≫ g).unop)` agrees with successive precomposition by `Over.map g.unop` and then
-- `Over.map f.unop`.
private theorem twoYonedaGroupoidPresheafMap_comp
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    twoYonedaGroupoidPresheafMap p ((f ≫ g).unop) =
      twoYonedaGroupoidPresheafMap p f.unop ⋙
        twoYonedaGroupoidPresheafMap p g.unop := sorry

/-- The contravariant groupoid-valued functor `U ↦ Mor_{Cat/C}(C/U, S)` attached to a category
fibred in groupoids `p : S ⥤ C`. -/
noncomputable def twoYonedaGroupoidPresheaf
    (p : S ⥤ C) [IsFibredInGroupoids p] : Cᵒᵖ ⥤ Grpd where
  obj U := twoYonedaGroupoidPresheafValue p (unop U)
  map f := twoYonedaGroupoidPresheafMap p f.unop
  map_id := twoYonedaGroupoidPresheafMap_id p
  map_comp := fun f g ↦ twoYonedaGroupoidPresheafMap_comp p f g

private noncomputable abbrev twoYonedaCatPresheaf
    (p : S ⥤ C) [IsFibredInGroupoids p] :=
  twoYonedaGroupoidPresheaf p ⋙ Grpd.forgetToCat

private noncomputable abbrev twoYonedaSplitCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :=
  CoGrothendieck ((twoYonedaCatPresheaf p).toPseudofunctor')

private noncomputable abbrev twoYonedaSplitProjection
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p ⥤ C :=
  CoGrothendieck.forget ((twoYonedaCatPresheaf p).toPseudofunctor')

private noncomputable instance twoYonedaSplitProjection_instIsFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    IsFibredInGroupoids (twoYonedaSplitProjection p) := by
  simpa [twoYonedaSplitProjection, twoYonedaCatPresheaf] using
    groupoidPresheafProjection_isFibredInGroupoids (twoYonedaGroupoidPresheaf p)

private noncomputable abbrev twoYonedaSplitToOriginalObj
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p → S :=
  fun X ↦
      ((X.2 : BasedCategory.ofFunctor (Over.forget X.1) ⥤ᵇ BasedCategory.ofFunctor p)).obj
        (Over.mk (𝟙 X.1))

private noncomputable abbrev twoYonedaSplitToOriginalMap
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p}
    (φ : X ⟶ Y) :
    twoYonedaSplitToOriginalObj p X ⟶ twoYonedaSplitToOriginalObj p Y :=
  ((φ.2 :
      (X.2 : BasedCategory.ofFunctor (Over.forget X.1) ⥤ᵇ BasedCategory.ofFunctor p) ⟶
        (twoYonedaGroupoidPresheafMap p φ.1).obj
          (Y.2 : BasedCategory.ofFunctor (Over.forget Y.1) ⥤ᵇ BasedCategory.ofFunctor p)).app
      (Over.mk (𝟙 X.1))) ≫
    ((Y.2 : BasedCategory.ofFunctor (Over.forget Y.1) ⥤ᵇ BasedCategory.ofFunctor p).map
      (Over.homMk φ.1))

private theorem twoYonedaSplitToOriginalUnderlying_map_id
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∀ X : twoYonedaSplitCategory p,
      twoYonedaSplitToOriginalMap p (𝟙 X) =
        𝟙 (twoYonedaSplitToOriginalObj p X) := sorry

private theorem twoYonedaSplitToOriginalUnderlying_map_comp
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∀ {X Y Z : twoYonedaSplitCategory p}
      (φ : X ⟶ Y) (ψ : Y ⟶ Z),
      twoYonedaSplitToOriginalMap p (φ ≫ ψ) =
        twoYonedaSplitToOriginalMap p φ ≫ twoYonedaSplitToOriginalMap p ψ := sorry

private noncomputable def twoYonedaSplitToOriginalUnderlying
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p ⥤ S where
  obj := twoYonedaSplitToOriginalObj p
  map φ := twoYonedaSplitToOriginalMap p φ
  map_id := twoYonedaSplitToOriginalUnderlying_map_id p
  map_comp := fun φ ψ ↦ twoYonedaSplitToOriginalUnderlying_map_comp p φ ψ

private theorem twoYonedaSplitToOriginalUnderlying_w
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitToOriginalUnderlying p ⋙ p = twoYonedaSplitProjection p := sorry

/-- The split fibred-in-groupoids model over `C` attached to the `2`-Yoneda groupoid presheaf. -/
noncomputable def twoYonedaSplitModel
    (p : S ⥤ C) [IsFibredInGroupoids p] : FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.ofFunctor (twoYonedaSplitProjection p)

private noncomputable instance twoYonedaSplitProjection_instIsSplitFibredCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    Functor.IsSplitFibredCategory (twoYonedaSplitProjection p) := by
  change Functor.IsSplitFibredCategory
    (CoGrothendieck.forget ((twoYonedaCatPresheaf p).toPseudofunctor'))
  refine ⟨⟨twoYonedaCatPresheaf p, BasedFunctor.id _, BasedFunctor.id _, ?_⟩⟩
  exact ⟨rfl, rfl⟩

noncomputable instance twoYonedaSplitModel_instIsSplitFibredCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    Functor.IsSplitFibredCategory ((twoYonedaSplitModel p).p) := by
  change Functor.IsSplitFibredCategory (twoYonedaSplitProjection p)
  infer_instance

/-- The canonical functor over `C` from the split `2`-Yoneda model to the original category
fibred in groupoids. It sends `(U, x)` to `x(𝟙 U)`. -/
noncomputable def twoYonedaSplitToOriginal
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredInGroupoidsMor (twoYonedaSplitModel p) (FibredInGroupoidsOver.ofFunctor p) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := twoYonedaSplitToOriginalUnderlying p
      w := twoYonedaSplitToOriginalUnderlying_w p }

-- Proof sketch: apply Example 4.37.1 to `twoYonedaGroupoidPresheaf p` to obtain a split fibred
-- category over `C`. For each `U`, Lemma 4.41.2 identifies the fiber of this split model with
-- `p.Fiber U`, and Lemma 4.35.9 upgrades these fiberwise equivalences to an equivalence over `C`.
/-- Remark 4.41.3: the `2`-Yoneda construction
`U ↦ Mor_{Cat/C}(C/U, S)`, formalized as `twoYonedaGroupoidPresheaf p`, gives an alternative
split model for a category fibred in groupoids `p : S ⥤ C`. The canonical comparison functor
`twoYonedaSplitToOriginal p : twoYonedaSplitModel p ⟶ FibredInGroupoidsOver.ofFunctor p`,
sending `(U, x)` to `x(𝟙 U)`, is an equivalence over `C`. -/
theorem twoYoneda_groupoidPresheaf_split_model_over_base
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (twoYonedaSplitToOriginal p).IsEquivalenceOverBase := sorry

end CategoryTheory
