import Mathlib
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_31_12 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type v} [Category.{v} C] [IsGroupoid C]
variable {S : Type v} [Category.{v} S] [IsGroupoid S]

variable (G₁ G₂ : C ⥤ S)

local notation "DiagonalPullback" =>
  CategoricalPullback (G₁.prod' G₂) (Functor.diag S)
local notation "IteratedPullback" =>
  CategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)

/- Domain-style sampling for Lemma 4.31.12:
- primary domain: bicategorical `2`-fibre products in `Cat`, expressed through the categorical
  pullback models attached to `(G₁.prod' G₂)` and `Functor.diag S`, together with the canonical
  iterated pullback owner of the induced cospan `π₁ G₁ G₂, π₂ G₁ G₂`;
- sampled owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CatCommSqOver.toBicategoricalSquare`,
  `symmetricTwoFibreProductComparison`;
-- best owner abstraction: the source-facing square is still
  `BicategoricalTwoCommutativeSquare (G₁.prod' G₂).toCatHom (Functor.diag S).toCatHom`, with the
  `2`-fibre product condition expressed by `Bicategory.IsFinal`, but the target owner for the
  iterated pullback is the Stacks nested model
  `IteratedPullback = CategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂))
    (Functor.diag C)`;
-- `CategoricalPullback` is the canonical owner abstraction, and `IteratedPullback` is exactly the
  textbook nested model `(C ×[S] C) ×[C × C] C`.  It is not the self-pullback
  `(π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`, which would have the wrong object set.

Primitive-vs-derived split:
- primitive data: the canonical diagonal square
  `Q : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback`,
  the induced square over `G₁` and `G₂`, and later an arbitrary source square
  `P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C'`;
-- derived API: the induced functor `DiagonalPullback ⥤ G₁ ⊡ G₂`, the resulting square over
  `Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)` and `Functor.diag C`, and the
  comparison/equivalence statements landing in the owner `IteratedPullback`. -/

/- Source/core/bridge triage for Lemma 4.31.12:
- `source-facing`: the displayed square over `(G₁.prod' G₂)` and `Δ_S`, viewed as a
  bicategorical square in `Cat`;
- `core/canonical`: `Bicategory.IsFinal` of that bicategorical square, with target owner
  `IteratedPullback`;
- `bridge/view`: `CatCommSqOver.toFunctorToCategoricalPullback`, together with Remark `4.31.5`
  identifying the textbook nested model `(C ×[S] C) ×[C × C] C` with `IteratedPullback`. -/

private abbrev diagonalSourceSquare :
    CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback :=
  (toCatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback).obj (𝟭 _)

private abbrev diagonalFirstPullbackSquare :
    CatCommSqOver G₁ G₂ DiagonalPullback :=
  let Q := diagonalSourceSquare G₁ G₂
  { fst := Q.fst
    snd := Q.fst
    iso :=
      (Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight Q.iso (fst S S) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
          Functor.rightUnitor _) ≪≫
        (Functor.isoWhiskerLeft _ (Functor.prod'CompSnd G₁ G₂).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight Q.iso (snd S S) ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Functor.prod'CompSnd (𝟭 S) (𝟭 S)) ≪≫
            Functor.rightUnitor _).symm }

private abbrev diagonalFirstPullbackComparison :
    DiagonalPullback ⥤ G₁ ⊡ G₂ :=
  (toFunctorToCategoricalPullback G₁ G₂ DiagonalPullback).obj
    (diagonalFirstPullbackSquare G₁ G₂)

/-- Helper for Lemma 4.31.12: the first projection of the intermediate comparison functor is the
original `C`-leg of the diagonal pullback square. -/
private theorem diagonal_first_comparison_fst_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙ π₁ G₁ G₂).map f ≫
        𝟙 ((diagonalSourceSquare G₁ G₂).fst.obj Y) =
      𝟙 ((diagonalSourceSquare G₁ G₂).fst.obj X) ≫
        ((diagonalSourceSquare G₁ G₂).fst.map f) := by
  -- Both sides are definitionally the same morphism on the shared first component.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare]

/-- Helper for Lemma 4.31.12: after projecting to the first factor, the intermediate comparison
is the identity on the original `C`-leg. -/
private abbrev diagonal_first_comparison_fst_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙ π₁ G₁ G₂ ≅ (diagonalSourceSquare G₁ G₂).fst :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_first_comparison_fst_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the second projection of the intermediate comparison functor is also
the original `C`-leg of the diagonal pullback square. -/
private theorem diagonal_first_comparison_snd_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙ π₂ G₁ G₂).map f ≫
        𝟙 ((diagonalSourceSquare G₁ G₂).fst.obj Y) =
      𝟙 ((diagonalSourceSquare G₁ G₂).fst.obj X) ≫
        ((diagonalSourceSquare G₁ G₂).fst.map f) := by
  -- The second leg was chosen to be the same functor, so the projected morphisms agree.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare]

/-- Helper for Lemma 4.31.12: after projecting to the second factor, the intermediate comparison
again recovers the original `C`-leg. -/
private abbrev diagonal_first_comparison_snd_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙ π₂ G₁ G₂ ≅ (diagonalSourceSquare G₁ G₂).fst :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_first_comparison_snd_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the first component of the diagonal pullback square identifies
`G₁` of the first leg with the `S`-leg. -/
private abbrev diagonal_source_first_component_iso :
    (diagonalSourceSquare G₁ G₂).fst ⋙ G₁ ≅ (diagonalSourceSquare G₁ G₂).snd :=
  let Q := diagonalSourceSquare G₁ G₂
  Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Q.iso (fst S S) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
    Functor.rightUnitor _

/-- Helper for Lemma 4.31.12: the comparison from the diagonal model to the iterated model is
natural after evaluating both product components. -/
private theorem diagonal_iterated_pullback_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙
          Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map f ≫
        𝟙 (((diagonalSourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj Y) =
      𝟙 (((diagonalSourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj X) ≫
        ((diagonalSourceSquare G₁ G₂).fst ⋙ Functor.diag C).map f := by
  -- Both functors are objectwise the same diagonal `(c, c)`; only the packaging differs.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare]

/-- Helper for Lemma 4.31.12: the diagonal model carries a canonical square over the outer
iterated-pullback cospan. -/
private abbrev diagonal_iterated_pullback_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙
        Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂) ≅
      (diagonalSourceSquare G₁ G₂).fst ⋙ Functor.diag C :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_iterated_pullback_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

private abbrev diagonalIteratedPullbackSquare :
    CatCommSqOver (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) DiagonalPullback where
  fst := diagonalFirstPullbackComparison G₁ G₂
  snd := (diagonalSourceSquare G₁ G₂).fst
  iso := diagonal_iterated_pullback_iso G₁ G₂

/-- The canonical comparison functor from the diagonal pullback model
`C ×[(S × S)] S` of Lemma 4.31.12 to the canonical iterated `2`-fibre-product owner
`IteratedPullback = (C ×[S] C) ×[C × C] C`. -/
abbrev categorical_pullback_diagonal_model_comparison :
    DiagonalPullback ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)
    DiagonalPullback).obj
    (diagonalIteratedPullbackSquare G₁ G₂)

/-- Helper for Lemma 4.31.12: the first projection of the iterated pullback identifies the inner
left object with the outer object. -/
private abbrev iterated_pullback_first_projection_iso :
    π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ≅
      π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (fst C C).mapIso X.iso)
    (fun {_ _} f ↦ by simpa using congrArg _root_.Prod.fst f.w)

/-- Helper for Lemma 4.31.12: the second projection of the iterated pullback identifies the inner
right object with the outer object. -/
private abbrev iterated_pullback_second_projection_iso :
    π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₂ G₁ G₂ ≅
      π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (snd C C).mapIso X.iso)
    (fun {_ _} f ↦ by simpa using congrArg _root_.Prod.snd f.w)

/-- Helper for Lemma 4.31.12: the inverse square uses the first outer projection to transport
`G₁(C₃)` back to `G₁(C₁)`. -/
private abbrev iterated_pullback_first_component_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₁ ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁ :=
  Functor.isoWhiskerRight (iterated_pullback_first_projection_iso (G₁ := G₁) (G₂ := G₂)).symm G₁

/-- Helper for Lemma 4.31.12: the inverse square uses the second outer projection together with
the inner pullback isomorphism to transport `G₂(C₃)` back to `G₁(C₁)`. -/
private abbrev iterated_pullback_second_component_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₂ ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁ :=
  Functor.isoWhiskerRight (iterated_pullback_second_projection_iso (G₁ := G₁) (G₂ := G₂)).symm
      G₂ ≪≫
    Functor.isoWhiskerLeft
      (π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C))
      (CatCommSq.iso (π₁ G₁ G₂) (π₂ G₁ G₂) G₁ G₂).symm

/-- Helper for Lemma 4.31.12: the inverse square from the iterated pullback model back to the
diagonal model is natural componentwise. -/
private theorem iterated_pullback_to_diagonal_iso_naturality
    {X Y : IteratedPullback} (f : X ⟶ Y) :
    (π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙
          G₁.prod' G₂).map f ≫
        (Iso.prod
          ((iterated_pullback_first_component_iso G₁ G₂).app Y)
          ((iterated_pullback_second_component_iso G₁ G₂).app Y)).hom =
      (Iso.prod
          ((iterated_pullback_first_component_iso G₁ G₂).app X)
          ((iterated_pullback_second_component_iso G₁ G₂).app X)).hom ≫
        ((π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁) ⋙
            Functor.diag S).map f := by
  -- Route correction: after evaluating the product components, the two identities are exactly the
  -- inverse naturality equations for the outer and inner pullback structure morphisms.
  ext
  · -- The first coordinate is just the first inverse outer transport, mapped through `G₁`.
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ G₁.map t) (congrArg _root_.Prod.fst f.w')
  · -- The second coordinate combines the second inverse outer transport with the inverse
    -- naturality of the inner pullback structural isomorphism.
    have houter :
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 =
          G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (fun t ↦ G₂.map t) (congrArg _root_.Prod.snd f.w')
    have hinner :
        G₂.map f.fst.snd ≫ Y.fst.iso.inv =
          X.fst.iso.inv ≫ G₁.map f.fst.fst := by
      simpa [Category.assoc] using congrArg _root_.Prod.snd f.fst.w'
    have houter' :
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 ≫ Y.fst.iso.inv =
          (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ Y.fst.iso.inv) houter
    have hinner' :
        (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv =
          G₂.map X.iso.inv.2 ≫ X.fst.iso.inv ≫ G₁.map f.fst.fst := by
      simpa [Category.assoc] using congrArg (fun t ↦ G₂.map X.iso.inv.2 ≫ t) hinner
    simpa [iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso,
      Category.assoc] using
      (calc
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 ≫ Y.fst.iso.inv
            = (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv := houter'
        _ = G₂.map X.iso.inv.2 ≫ X.fst.iso.inv ≫ G₁.map f.fst.fst := hinner')

/-- Helper for Lemma 4.31.12: the iterated pullback carries the textbook inverse square back to
the diagonal pullback model. -/
private abbrev iterated_pullback_to_diagonal_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₁.prod' G₂ ≅
      (π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁) ⋙
        Functor.diag S :=
  NatIso.ofComponents
    (fun X ↦
      Iso.prod
        ((iterated_pullback_first_component_iso G₁ G₂).app X)
        ((iterated_pullback_second_component_iso G₁ G₂).app X))
    (fun {_ _} f ↦ iterated_pullback_to_diagonal_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the explicit inverse functor obtained from the iterated pullback
square. -/
private abbrev iterated_pullback_to_diagonal :
    IteratedPullback ⥤ DiagonalPullback :=
  (toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) IteratedPullback).obj
    { fst := π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)
      snd := π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁
      iso := iterated_pullback_to_diagonal_iso G₁ G₂ }

/-- Helper for Lemma 4.31.12: the unit only changes the `S`-component by the first projection of
the diagonal source square. -/
private abbrev diagonal_model_unit_second_component_obj_iso (X : DiagonalPullback) :
    X.snd ≅
      ((categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
            iterated_pullback_to_diagonal G₁ G₂).obj X).snd := by
  -- Route correction: package the unit objectwise so the nontrivial part is just the existing
  -- first-component identification from the diagonal source square.
  simpa [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare,
    iterated_pullback_to_diagonal] using
    ((diagonal_source_first_component_iso G₁ G₂).app X).symm

/-- Helper for Lemma 4.31.12: objectwise, the nontrivial unit component is the inverse of the
first coordinate of the diagonal pullback structure isomorphism. -/
private theorem diagonal_model_unit_second_component_obj_iso_hom (X : DiagonalPullback) :
    (diagonal_model_unit_second_component_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom = X.iso.inv.1 := by
  simp [diagonal_model_unit_second_component_obj_iso,
    categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: after comparing to the iterated model and back, the resulting
diagonal structural map is the original one with the first coordinate normalized to the identity. -/
private theorem diagonal_model_unit_target_iso_hom (X : DiagonalPullback) :
    ((categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
          iterated_pullback_to_diagonal G₁ G₂).obj X).iso.hom =
      (𝟙 (G₁.obj X.fst), X.iso.hom.2 ≫ X.iso.inv.1) := by
  simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso,
    Category.assoc]

/-- Helper for Lemma 4.31.12: the unit of the explicit model equivalence. -/
private abbrev iterated_pullback_to_diagonal_unitIso :
    𝟭 DiagonalPullback ≅
      categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
        iterated_pullback_to_diagonal G₁ G₂ := by
  -- Route correction: build the unit objectwise, with the `C`-component definitionally fixed.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso (.refl _) (diagonal_model_unit_second_component_obj_iso
      (G₁ := G₁) (G₂ := G₂) X) ?_
    -- The pullback compatibility is exactly the diagonal square identity after unfolding.
    rw [diagonal_model_unit_second_component_obj_iso_hom (G₁ := G₁) (G₂ := G₂) X,
      diagonal_model_unit_target_iso_hom (G₁ := G₁) (G₂ := G₂) X]
    ext
    · symm
      have hfst :
          ((diagonal_source_first_component_iso G₁ G₂).app X).hom ≫
              ((diagonal_source_first_component_iso G₁ G₂).app X).inv =
            𝟙 (G₁.obj X.fst) := by
        exact ((diagonal_source_first_component_iso G₁ G₂).app X).hom_inv_id
      simpa [diagonal_source_first_component_iso, Category.assoc] using hfst
    · simp
  · intro X Y f
    -- Naturality is componentwise: the first projection is definitional, and the second is the
    -- naturality of `diagonal_source_first_component_iso`.
    apply CategoricalPullback.hom_ext
    · change f.fst ≫ 𝟙 Y.fst = 𝟙 X.fst ≫ f.fst
      simp
    · simpa [diagonal_model_unit_second_component_obj_iso_hom] using
        congrArg _root_.Prod.fst f.w'

/-- Helper for Lemma 4.31.12: after returning to the diagonal model and comparing back, the inner
pullback structural map is the original one transported along the second outer projection. -/
private theorem iterated_pullback_counit_inner_target_iso_hom (X : IteratedPullback) :
    ((iterated_pullback_to_diagonal G₁ G₂ ⋙
          categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).fst.iso.hom =
      G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ G₂.map X.iso.hom.2 := by
  simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: objectwise, the inverse second outer projection is literally the
second inverse component of the outer pullback isomorphism. -/
private theorem iterated_pullback_second_projection_iso_symm_hom (X : IteratedPullback) :
    ((iterated_pullback_second_projection_iso G₁ G₂).app X).symm.hom = X.iso.inv.2 := by
  change ((Prod.snd C C).mapIso X.iso).inv = X.iso.inv.2
  rfl

/-- Helper for Lemma 4.31.12: the inner component of the counit is compatible with the inner
pullback structure. -/
private abbrev iterated_pullback_counit_inner_obj_iso (X : IteratedPullback) :
    ((iterated_pullback_to_diagonal G₁ G₂ ⋙
          categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).fst ≅ X.fst := by
  -- The inner pullback is recovered from the two outer projections back to the original `C ×[S] C`
  -- object.
  refine CategoricalPullback.mkIso
      (((iterated_pullback_first_projection_iso G₁ G₂).app X).symm)
      (((iterated_pullback_second_projection_iso G₁ G₂).app X).symm) ?_
  -- After unfolding the composite, this is the original inner pullback relation on `X.fst`.
  rw [iterated_pullback_counit_inner_target_iso_hom (G₁ := G₁) (G₂ := G₂) X]
  rw [iterated_pullback_second_projection_iso_symm_hom (G₁ := G₁) (G₂ := G₂) X]
  calc
    G₁.map X.iso.inv.1 ≫ X.fst.iso.hom
        = G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ 𝟙 (G₂.obj X.fst.snd) := by simp
    _ = G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫
          G₂.map (X.iso.hom.2 ≫ X.iso.inv.2) := by
      have h₂ : 𝟙 (G₂.obj X.fst.snd) = G₂.map (X.iso.hom.2 ≫ X.iso.inv.2) := by
        symm
        have hsnd : X.iso.hom.2 ≫ X.iso.inv.2 = 𝟙 (X.fst.snd) := by
          exact congrArg _root_.Prod.snd X.iso.hom_inv_id
        simpa [Functor.map_id, ← Functor.map_comp] using
          congrArg (fun t ↦ G₂.map t) hsnd
      simpa [Category.assoc] using congrArg (fun t ↦ G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ t) h₂
    _ = (G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ G₂.map X.iso.hom.2) ≫ G₂.map X.iso.inv.2 := by
      simp [Category.assoc]

/-- Helper for Lemma 4.31.12: the first component of the inner counit is the inverse first outer
projection. -/
private theorem iterated_pullback_counit_inner_obj_iso_fst_hom (X : IteratedPullback) :
    (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom.fst = X.iso.inv.1 := by
  simp [iterated_pullback_counit_inner_obj_iso, iterated_pullback_first_projection_iso]

/-- Helper for Lemma 4.31.12: the second component of the inner counit is the inverse second outer
projection. -/
private theorem iterated_pullback_counit_inner_obj_iso_snd_hom (X : IteratedPullback) :
    (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom.snd = X.iso.inv.2 := by
  simp [iterated_pullback_counit_inner_obj_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: the inner pullback component of the counit. -/
private abbrev iterated_pullback_counit_inner_iso :
    iterated_pullback_to_diagonal G₁ G₂ ⋙ categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
        π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) := by
  -- Package the recovered inner pullback objectwise before assembling the full counit.
  refine NatIso.ofComponents
      (fun X ↦ iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X) ?_
  intro X Y f
  -- Naturality is exactly the inverse naturality of the outer structural isomorphism.
  apply CategoricalPullback.hom_ext
  · simpa [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
      diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
      diagonalSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
      iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso] using
    congrArg _root_.Prod.fst f.w'
  · simpa [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
      diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
      diagonalSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
      iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso] using
    congrArg _root_.Prod.snd f.w'

/-- Helper for Lemma 4.31.12: the outer component of the counit is definitional. -/
private theorem iterated_pullback_to_diagonal_counit_outer_coherence (X : IteratedPullback) :
    (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map
        (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom ≫
      X.iso.hom =
        ((iterated_pullback_to_diagonal G₁ G₂ ⋙
              categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).iso.hom ≫
          (Functor.diag C).map (𝟙 X.snd) := by
  -- The outer component is fixed, so only the inner pullback object needs to be compared.
  simp [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
    diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
    diagonalSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: the counit of the explicit model equivalence. -/
private abbrev iterated_pullback_to_diagonal_counitIso :
    iterated_pullback_to_diagonal G₁ G₂ ⋙ categorical_pullback_diagonal_model_comparison G₁ G₂ ≅
      𝟭 IteratedPullback := by
  -- The counit is again best packaged objectwise: recover the inner pullback and keep the outer
  -- `C`-object fixed.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso
      (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X)
      (.refl _) ?_
    simpa using iterated_pullback_to_diagonal_counit_outer_coherence (G₁ := G₁) (G₂ := G₂) X
  · intro X Y f
    -- Naturality is componentwise: use the inner counit naturality and the definitional outer
    -- identity separately.
    apply CategoricalPullback.hom_ext
    · exact (iterated_pullback_counit_inner_iso (G₁ := G₁) (G₂ := G₂)).hom.naturality f
    · simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
        diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalSourceSquare,
        iterated_pullback_to_diagonal]

-- Proof sketch: this is the omitted construction in the Stacks proof. The diagonal pullback model
-- `C ×[(S × S)] S` maps canonically to the iterated `2`-fibre-product owner
-- `(C ×[S] C) ×[C × C] C`.
/-- The model-comparison functor of Lemma 4.31.12 is an equivalence. -/
noncomputable instance categorical_pullback_diagonal_model_comparison_isEquivalence :
    (categorical_pullback_diagonal_model_comparison G₁ G₂).IsEquivalence := by
  -- The inverse functor and the objectwise unit/counit are now explicit, so the equivalence
  -- packaging is immediate once the quasi-inverse data is named explicitly.
  let G := iterated_pullback_to_diagonal G₁ G₂
  let η := iterated_pullback_to_diagonal_unitIso (G₁ := G₁) (G₂ := G₂)
  let ε := iterated_pullback_to_diagonal_counitIso (G₁ := G₁) (G₂ := G₂)
  exact Functor.IsEquivalence.mk' G η ε

variable {C' : Type v} [Category.{v} C'] [IsGroupoid C']
variable (P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C')

/-- The comparison functor from a `2`-commutative square over `(G₁.prod' G₂)` and `Δ_S`
to the canonical iterated `2`-fibre product of Lemma 4.31.12. -/
abbrev categorical_pullback_diagonal_comparison
    : C' ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) C').obj P ⋙
    categorical_pullback_diagonal_model_comparison G₁ G₂

/-- The canonical comparison functor attached to a `2`-fibre product square over
`(G₁.prod' G₂)` and `Δ_S`, expressed through the chapter's owner predicate
`Bicategory.IsFinal`, is an equivalence. -/
noncomputable instance
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_comparison G₁ G₂ P).IsEquivalence := by
  -- The generic comparison to the diagonal pullback model is already an equivalence by
  -- Lemma 4.31.11, and the model-comparison proved above is another equivalence.
  let _ :
      ((toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) C').obj P).IsEquivalence := by
    simpa using (toFunctorToCategoricalPullback_isEquivalence_of_isFinal (Q := P))
  let _ : (categorical_pullback_diagonal_model_comparison G₁ G₂).IsEquivalence := by infer_instance
  infer_instance

/-- Lemma 4.31.12: if
`\mathcal{C}' \to \mathcal{S} \leftarrow \mathcal{C}`
is a `2`-fibre product square for `(G₁.prod' G₂)` and `Δ_S`, then there is a canonical
equivalence to the owner-level iterated `2`-fibre product
`C' ≌ (C ×[S] C) ×[C × C] C`. -/
noncomputable def categorical_pullback_diagonal_square_equivalence
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    C' ≌ IteratedPullback :=
  (categorical_pullback_diagonal_comparison G₁ G₂ P).asEquivalence

/-- The forward functor of `categorical_pullback_diagonal_square_equivalence` is the canonical
comparison functor to the iterated `2`-fibre product owner. -/
-- Proof sketch: unfold `categorical_pullback_diagonal_square_equivalence`; it is defined by
-- `Functor.asEquivalence` on `categorical_pullback_diagonal_comparison G₁ G₂ P`, so the forward
-- functor is exactly that comparison functor.
theorem categorical_pullback_diagonal_square_equivalence_functor
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_square_equivalence G₁ G₂ P).functor =
      categorical_pullback_diagonal_comparison G₁ G₂ P := by
  -- Unfolding `Functor.asEquivalence` shows that the forward functor is definitionally the
  -- comparison functor.
  rfl

end

end CategoryTheory.Limits

/-! ### Lemma_4_31_13 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C₀ : Type u₁} [Category.{v₁} C₀]
variable {D₀ : Type u₂} [Category.{v₂} D₀]

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]

/-- Helper for Lemma 4.31.13: the canonical comparison from `A ×[C] B` to the ordinary pullback
of `A ×[D] B ⥤ C ×[D] C ← C` is an equivalence. -/
private theorem two_fibre_product_diagonal_comparison_isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    ((toFunctorToCategoricalPullback
        (two_fibre_product_right_vertical F G H) (Δₚ H) (F ⊡ G)).obj
      (two_fibre_product_diagonal_square_over F G H)).IsEquivalence := by
  -- Route correction: package the explicit inverse directly, rather than rebuilding a fully
  -- faithful/essentially surjective argument through repeated transport.
  let G' := twoFibreProductDiagonalInverse F G H
  let η := twoFibreProductDiagonalUnitIso F G H
  let ε := twoFibreProductDiagonalCounitIso F G H
  exact Functor.IsEquivalence.mk' G' η ε

/-- Helper for Lemma 4.31.13: evaluating the commutativity of a square morphism in `Cat` gives
the expected objectwise compatibility between the two legs and the square isomorphisms. -/
private theorem square_hom_comm_app
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {S₀ : Type (max u v)} [Category.{v} S₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R S₀)
    (Q : CatCommSqOver L R T₀)
    (u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare)
    (x : S₀) :
    L.map (u.left.toNatTrans.app x) ≫ S.iso.hom.app x =
      Q.iso.hom.app (u.hom.toFunctor.obj x) ≫ R.map (u.right.toNatTrans.app x) := by
  -- Convert the bicategorical square equation to an equality of ordinary natural transformations
  -- in `Cat`, then evaluate at `x`.
  have h := congrArg Cat.Hom₂.toNatTrans u.comm
  have hx := congrArg (fun τ ↦ τ.app x) h
  have hleft :
      (Functor.whiskerRight u.left.toNatTrans L ≫ S.iso.hom).app x =
        L.map (u.left.toNatTrans.app x) ≫ S.iso.hom.app x := by
    rfl
  have hright :
      ((u.hom.toFunctor.associator Q.fst L).hom ≫
            u.hom.toFunctor.whiskerLeft Q.iso.hom ≫
              (u.hom.toFunctor.associator Q.snd R).inv ≫
                Functor.whiskerRight u.right.toNatTrans R).app x =
        Q.iso.hom.app (u.hom.toFunctor.obj x) ≫ R.map (u.right.toNatTrans.app x) := by
    repeat rw [NatTrans.comp_app]
    simp
  exact hleft.symm.trans (hx.trans hright)

/-- Helper for Lemma 4.31.13: whiskering a fixed square `Q` by a functor `J` gives the source
square over the same cospan with apex the source of `J`. -/
private abbrev comparison_whisker_source_square
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    CatCommSqOver L R Y₀ :=
  { fst := J ⋙ Q.fst
    snd := J ⋙ Q.snd
    iso := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J Q.iso ≪≫
      (Functor.associator _ _ _).symm }

/-- Helper for Lemma 4.31.13: the whiskered square construction is functorial in the apex
functor. -/
private theorem comparison_whisker_source_square_map_w
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    {J K : Y₀ ⥤ T₀}
    (η : J ⟶ K) :
    Functor.whiskerRight (Functor.whiskerRight η Q.fst) L ≫
        (comparison_whisker_source_square Q K).iso.hom =
      (comparison_whisker_source_square Q J).iso.hom ≫
        Functor.whiskerRight (Functor.whiskerRight η Q.snd) R := by
  -- Naturality of `Q.iso` is exactly the compatibility condition after expanding the whiskering.
  ext x
  simpa [comparison_whisker_source_square, Category.assoc] using
    Q.iso.hom.naturality (η.app x)

/-- Helper for Lemma 4.31.13: the whiskered source squares form a functor out of the apex
functor category. -/
private abbrev comparison_whisker_source_square_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    (Y₀ ⥤ T₀) ⥤ CatCommSqOver L R Y₀ :=
  { obj := comparison_whisker_source_square Q
    map := fun η ↦
      { fst := Functor.whiskerRight η Q.fst
        snd := Functor.whiskerRight η Q.snd
        w := comparison_whisker_source_square_map_w Q η }
    map_id := by
      -- The identity transformation whiskers to identities on both legs.
      intro J
      apply CatCommSqOver.hom_ext <;> ext x <;> simp
    map_comp := by
      -- Composition of whiskered transformations is computed componentwise.
      intro J K M η θ
      apply CatCommSqOver.hom_ext <;> ext x <;> simp }

/-- Helper for Lemma 4.31.13: a square morphism into `Q` is equivalently a costructured arrow
into the functor of whiskered source squares attached to `Q`. -/
private abbrev square_hom_to_comparison_costructuredArrow
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  CostructuredArrow.mk
    ({ fst := u.left.toNatTrans
       snd := u.right.toNatTrans
       w := by
         -- The square-morphism compatibility is exactly the `CatCommSqOver` compatibility for the
         -- whiskered source square after translating the bicategorical relation to `Cat`.
         dsimp [comparison_whisker_source_square]
         simpa only [← Category.assoc] using
           congrArg CategoryTheory.Cat.Hom₂.toNatTrans u.comm } :
      comparison_whisker_source_square Q u.hom.toFunctor ⟶ S)

/-- Helper for Lemma 4.31.13: the `CatCommSqOver` compatibility of a costructured arrow is the
bicategorical square-morphism compatibility for the recovered square map. -/
private theorem comparison_costructuredArrow_to_square_hom_comm
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (a : CostructuredArrow (comparison_whisker_source_square_functor Q) S) :
    Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.fst) L.toCatHom ≫
        S.toBicategoricalSquare.ψ.hom =
      (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.p L.toCatHom).hom ≫
        Bicategory.whiskerLeft a.left.toCatHom Q.toBicategoricalSquare.ψ.hom ≫
        (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.q R.toCatHom).inv ≫
        Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.snd) R.toCatHom := by
  -- Evaluate the bicategorical square equation objectwise, so both sides can be compared to the
  -- ordinary `CatCommSqOver` midpoint.
  apply Cat.Hom₂.ext
  ext x
  let mid := Q.iso.hom.app (a.left.obj x) ≫ R.map (a.hom.snd.app x)
  have hnorm :
      ((a.left.associator Q.fst L).hom ≫
          (a.left.isoWhiskerLeft Q.iso).hom ≫
          (a.left.associator Q.snd R).inv).app x =
        Q.iso.hom.app (a.left.obj x) := by
    simp
  have hw :
      (Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.fst) L.toCatHom ≫
          S.toBicategoricalSquare.ψ.hom).toNatTrans.app x = mid := by
    -- The comma-arrow compatibility is exactly the left-hand comparison with that midpoint.
    change (Functor.whiskerRight a.hom.fst L ≫ S.iso.hom).app x = mid
    simpa [mid] using
      hnorm ▸ (CatCommSqOver.w_app
        (X := Y₀) (S := comparison_whisker_source_square Q a.left) (S' := S) a.hom x)
  have hr :
      ((Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.p L.toCatHom).hom ≫
          Bicategory.whiskerLeft a.left.toCatHom Q.toBicategoricalSquare.ψ.hom ≫
          (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.q R.toCatHom).inv ≫
          Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.snd) R.toCatHom).toNatTrans.app x =
        mid := by
    -- The right-hand bicategorical expression expands to the same midpoint.
    change ((a.left.associator Q.fst L).hom ≫ a.left.whiskerLeft Q.iso.hom ≫
        (a.left.associator Q.snd R).inv ≫ Functor.whiskerRight a.hom.snd R).app x = mid
    repeat rw [NatTrans.comp_app]
    simp [mid]
  exact hw.trans hr.symm

/-- Helper for Lemma 4.31.13: a costructured arrow into the whiskered-square functor recovers the
corresponding square morphism into `Q`. -/
private abbrev comparison_costructuredArrow_to_square_hom
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (a : CostructuredArrow (comparison_whisker_source_square_functor Q) S) :
    S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare :=
  { hom := a.left.toCatHom
    left := a.hom.fst.toCatHom₂
    right := a.hom.snd.toCatHom₂
    comm := comparison_costructuredArrow_to_square_hom_comm S Q a }

/-- Helper for Lemma 4.31.13: a `2`-morphism of square maps becomes the corresponding morphism in
the comma category of whiskered source squares. -/
private theorem square_twohom_to_comparison_costructuredArrow_hom_eq
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    {u v : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare}
    (η : u ⟶ v) :
    (comparison_whisker_source_square_functor Q).map η.hom.toNatTrans ≫
        (square_hom_to_comparison_costructuredArrow S Q v).hom =
      (square_hom_to_comparison_costructuredArrow S Q u).hom := by
  -- Equality in the comma category is detected on the two displayed natural-transformation legs.
  apply CatCommSqOver.hom_ext
  · ext x
    simpa [comparison_whisker_source_square_functor, comparison_whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.left_comm)
  · ext x
    simpa [comparison_whisker_source_square_functor, comparison_whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.right_comm)

/-- Helper for Lemma 4.31.13: a morphism in the comma category of whiskered source squares
recovers the corresponding `2`-morphism of square maps. -/
private abbrev comparison_costructuredArrow_hom_to_square_twohom
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    {a b : CostructuredArrow (comparison_whisker_source_square_functor Q) S}
    (η : a ⟶ b) :
    comparison_costructuredArrow_to_square_hom S Q a ⟶
      comparison_costructuredArrow_to_square_hom S Q b :=
  { hom := by
      simpa [comparison_costructuredArrow_to_square_hom] using η.left.toCatHom₂
    left_comm := by
      -- The left projection of the comma-category relation becomes the left-leg compatibility.
      apply Cat.Hom₂.ext
      ext x
      simpa [comparison_costructuredArrow_to_square_hom,
        comparison_whisker_source_square_functor, comparison_whisker_source_square] using
        congrArg (fun τ ↦ τ.app x) (congrArg CatCommSqOver.Hom.fst (CostructuredArrow.w η))
    right_comm := by
      -- The right projection gives the matching compatibility on the right leg.
      apply Cat.Hom₂.ext
      ext x
      simpa [comparison_costructuredArrow_to_square_hom,
        comparison_whisker_source_square_functor, comparison_whisker_source_square] using
        congrArg (fun τ ↦ τ.app x) (congrArg CatCommSqOver.Hom.snd (CostructuredArrow.w η)) }

/-- Helper for Lemma 4.31.13: square maps into `Q` assemble into a functor to costructured
arrows into the whiskered-source-square functor. -/
private abbrev square_hom_to_comparison_costructuredArrow_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ⥤
      CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  { obj := square_hom_to_comparison_costructuredArrow S Q
    map := fun η ↦
      CostructuredArrow.homMk
        η.hom.toNatTrans
        (square_twohom_to_comparison_costructuredArrow_hom_eq S Q η)
    map_id := by
      -- Identity `2`-morphisms become identity comma morphisms.
      intro u
      apply CostructuredArrow.hom_ext
      rfl
    map_comp := by
      -- Vertical composition of `2`-morphisms is sent to composition in the comma category.
      intro u v w η θ
      apply CostructuredArrow.hom_ext
      rfl }

/-- Helper for Lemma 4.31.13: costructured arrows into the whiskered-source-square functor
assemble into a functor back to square maps. -/
private abbrev comparison_costructuredArrow_to_square_hom_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S ⥤
      (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :=
  { obj := comparison_costructuredArrow_to_square_hom S Q
    map := fun η ↦ comparison_costructuredArrow_hom_to_square_twohom S Q η
    map_id := by
      -- Identity comma morphisms translate back to identity `2`-morphisms.
      intro a
      apply BicategoricalTwoCommutativeSquare.TwoHom.ext
      rfl
    map_comp := by
      -- Composition is preserved because the reconstruction keeps the same apex transformation.
      intro a b c η θ
      apply BicategoricalTwoCommutativeSquare.TwoHom.ext
      rfl }

/-- Helper for Lemma 4.31.13: converting a square map to a costructured arrow and back leaves the
square map unchanged. -/
@[simp] private theorem comparison_square_hom_roundtrip
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    ∀ u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare,
      comparison_costructuredArrow_to_square_hom S Q
        (square_hom_to_comparison_costructuredArrow S Q u) = u := by
  intro u
  -- The reconstructed square map is definitionally the same after unpacking the structure.
  rcases u with ⟨hom, left, right, comm⟩
  rfl

/-- Helper for Lemma 4.31.13: converting a costructured arrow to a square map and back leaves the
costructured arrow unchanged. -/
@[simp] private theorem comparison_costructuredArrow_roundtrip
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    ∀ a : CostructuredArrow (comparison_whisker_source_square_functor Q) S,
      square_hom_to_comparison_costructuredArrow S Q
        (comparison_costructuredArrow_to_square_hom S Q a) = a := by
  intro a
  -- The reverse round-trip preserves the apex functor and the displayed square morphism into `S`.
  rcases a with ⟨left, hom⟩
  rfl

/-- Helper for Lemma 4.31.13: square maps into `Q` are equivalent to costructured arrows into the
whiskered-source-square functor attached to `Q`. -/
private noncomputable abbrev square_hom_equiv_comparison_costructuredArrow
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≌
      CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  let forward := square_hom_to_comparison_costructuredArrow_functor S Q
  let backward := comparison_costructuredArrow_to_square_hom_functor S Q
  let unitIso :
      𝟭 (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≅ forward ⋙ backward :=
    NatIso.ofComponents
      (fun u ↦ CategoryTheory.eqToIso ((comparison_square_hom_roundtrip S Q) u))
      (fun {u v} η ↦ by
        -- After reducing both round-trip equalities, naturality is the identity computation on
        -- the underlying apex `2`-morphism.
        rcases u with ⟨uhom, uleft, uright, ucomm⟩
        rcases v with ⟨vhom, vleft, vright, vcomm⟩
        rcases η with ⟨ηhom, ηleft, ηright⟩
        cases (comparison_square_hom_roundtrip S Q
          { hom := uhom, left := uleft, right := uright, comm := ucomm })
        cases (comparison_square_hom_roundtrip S Q
          { hom := vhom, left := vleft, right := vright, comm := vcomm })
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        change ηhom ≫ 𝟙 vhom = 𝟙 uhom ≫ ηhom
        simp
      )
  let counitIso :
      backward ⋙ forward ≅
        𝟭 (CostructuredArrow (comparison_whisker_source_square_functor Q) S) :=
    NatIso.ofComponents
      (fun a ↦ CategoryTheory.eqToIso ((comparison_costructuredArrow_roundtrip S Q) a))
      (fun {a b} η ↦ by
        -- The counit naturality is the same identity computation in the comma category.
        rcases a with ⟨aleft, aright, ahom⟩
        rcases b with ⟨bleft, bright, bhom⟩
        rcases η with ⟨ηleft, ηw⟩
        cases (comparison_costructuredArrow_roundtrip S Q
          { left := aleft, right := aright, hom := ahom })
        cases (comparison_costructuredArrow_roundtrip S Q
          { left := bleft, right := bright, hom := bhom })
        simp [forward, backward]
      )
  CategoryTheory.Equivalence.mk forward backward unitIso counitIso

/-- Helper for Lemma 4.31.13: finality of `Q` transfers to terminal objects in the comma
categories attached to whiskering into `Q`. -/
private theorem comparison_costructuredArrow_hasTerminal_of_isFinal
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    HasTerminal (CostructuredArrow (comparison_whisker_source_square_functor Q) S) := by
  -- Finality of `Q` gives a terminal object in the hom-category, and the generic equivalence
  -- above transports that terminal object to the corresponding comma category.
  let e := square_hom_equiv_comparison_costructuredArrow S Q
  letI : e.inverse.IsEquivalence := e.symm.isEquivalence_functor
  exact CategoryTheory.hasTerminal_of_equivalence e.inverse

/-- Helper for Lemma 4.31.13: the canonical pullback square over `L` and `R`, viewed in
`CatCommSqOver`, is the target of the comparison-whiskering transport. -/
private abbrev canonical_comparison_square
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀} :
    CatCommSqOver L R (L ⊡ R) :=
  (toCatCommSqOver L R (L ⊡ R)).obj (𝟭 (L ⊡ R))

/-- Helper for Lemma 4.31.13: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
private theorem comparison_whisker_source_square_obj_iso_w
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    Functor.whiskerRight
        (Iso.refl ((comparison_whisker_source_square Q J).fst)).hom L ≫
        (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
              ((toFunctorToCategoricalPullback L R T₀).obj Q) ⋙
            comparison_whisker_source_square_functor
              (canonical_comparison_square (L := L) (R := R))).obj J).iso.hom =
      (comparison_whisker_source_square Q J).iso.hom ≫
        Functor.whiskerRight
          (Iso.refl ((comparison_whisker_source_square Q J).snd)).hom R := by
  -- Both objectwise square descriptions have identical components once the comparison functor is
  -- unfolded back to the canonical pullback square.
  ext x
  simp [comparison_whisker_source_square, canonical_comparison_square]

/-- Helper for Lemma 4.31.13: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
private abbrev comparison_whisker_source_square_obj_iso
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    comparison_whisker_source_square Q J ≅
      (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
            ((toFunctorToCategoricalPullback L R T₀).obj Q)) ⋙
          comparison_whisker_source_square_functor
            (canonical_comparison_square (L := L) (R := R))).obj J :=
  CatCommSqOver.mkIso (Iso.refl _) (Iso.refl _)
    (comparison_whisker_source_square_obj_iso_w Q J)

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor turns a source square for `Q`
into the corresponding source square for the canonical pullback square. -/
private theorem comparison_whisker_source_square_iso_naturality
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    ∀ {J K : Y₀ ⥤ T₀} (η : J ⟶ K),
      (comparison_whisker_source_square_functor Q).map η ≫
          (comparison_whisker_source_square_obj_iso Q K).hom =
        (comparison_whisker_source_square_obj_iso Q J).hom ≫
          (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
                ((toFunctorToCategoricalPullback L R T₀).obj Q) ⋙
              comparison_whisker_source_square_functor
                (canonical_comparison_square (L := L) (R := R))).map η) := by
  -- The transport is identity on both displayed components, so naturality is componentwise.
  intro J K η
  apply CatCommSqOver.hom_ext <;> ext x <;>
    simp [comparison_whisker_source_square_obj_iso, comparison_whisker_source_square,
      canonical_comparison_square]

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor turns a source square for `Q`
into the corresponding source square for the canonical pullback square. -/
private abbrev comparison_whisker_source_square_iso
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    comparison_whisker_source_square_functor Q ≅
      ((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
          ((toFunctorToCategoricalPullback L R T₀).obj Q)) ⋙
        comparison_whisker_source_square_functor
          (canonical_comparison_square (L := L) (R := R)) :=
  NatIso.ofComponents
    (comparison_whisker_source_square_obj_iso Q)
    (comparison_whisker_source_square_iso_naturality Q)

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor induces an equivalence on the
relevant functor categories. -/
private theorem comparison_whiskering_functor_isEquivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (hQ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence) :
    (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
          ((toFunctorToCategoricalPullback L R T₀).obj Q))).IsEquivalence := by
  let _ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence := hQ
  infer_instance

/-- Helper for Lemma 4.31.13: after whiskering along an equivalence comparison functor, the comma
categories of source squares for `Q` and for the canonical pullback square are equivalent. -/
private noncomputable abbrev comparison_costructuredArrow_equivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (S : CatCommSqOver L R Y₀)
    (hQ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S ≌
      CostructuredArrow
        (comparison_whisker_source_square_functor
          (canonical_comparison_square (L := L) (R := R)))
        S :=
  let W : (Y₀ ⥤ T₀) ⥤ (Y₀ ⥤ L ⊡ R) :=
    (Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
      ((toFunctorToCategoricalPullback L R T₀).obj Q)
  letI : W.IsEquivalence := comparison_whiskering_functor_isEquivalence (Y₀ := Y₀) Q hQ
  (CostructuredArrow.mapNatIso (comparison_whisker_source_square_iso (Y₀ := Y₀) Q)).trans
    (Functor.asEquivalence (CostructuredArrow.pre W _ S))

/-- Helper for Lemma 4.31.13: if the canonical comparison functor of a commutative square to the
ordinary categorical pullback is an equivalence, then the associated bicategorical square is
final. -/
private theorem isFinal_of_toFunctorToCategoricalPullback_isEquivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {X₀ : Type (max u v)} [Category.{v} X₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R X₀)
    (hQ : ((toFunctorToCategoricalPullback L R X₀).obj Q).IsEquivalence) :
    Bicategory.IsFinal Q.toBicategoricalSquare := by
  -- Route correction: transport terminal objects from the canonical categorical pullback square
  -- through the comparison functor, then back across the square-hom/comma equivalence.
  let _ : ((toFunctorToCategoricalPullback L R X₀).obj Q).IsEquivalence := hQ
  refine ⟨fun S ↦ ?_⟩
  let R₀ : CatCommSqOver L R S.obj := as_catCommSqOver L R S
  let e₁ := square_hom_equiv_comparison_costructuredArrow R₀ Q
  let e₂ := comparison_costructuredArrow_equivalence Q R₀ hQ
  let _ :
      Bicategory.IsFinal
        (canonical_comparison_square (L := L) (R := R)).toBicategoricalSquare := by
    simpa [canonical_comparison_square, categoricalPullbackSquare] using
      (categoricalPullback_isTwoFibreProduct (F := L) (G := R))
  let _ :
      HasTerminal
        (CostructuredArrow
          (comparison_whisker_source_square_functor
            (canonical_comparison_square (L := L) (R := R)))
          R₀) :=
    comparison_costructuredArrow_hasTerminal_of_isFinal
      R₀
      (canonical_comparison_square (L := L) (R := R))
  let _ :
      HasTerminal
        (CostructuredArrow (comparison_whisker_source_square_functor Q) R₀) := by
    letI : e₂.functor.IsEquivalence := e₂.isEquivalence_functor
    exact CategoryTheory.hasTerminal_of_equivalence e₂.functor
  letI : e₁.functor.IsEquivalence := e₁.isEquivalence_functor
  exact CategoryTheory.hasTerminal_of_equivalence e₁.functor

open scoped Bicategory

/-- The square
`A ×[C] B ⥤ A ×[D] B`, `A ×[C] B ⥤ C`, `A ×[D] B ⥤ C ×[D] C`, `C ⥤ C ×[D] C`
with bottom map the diagonal `Δₚ H`, viewed as the chapter's bicategorical square in `Cat`. -/
abbrev two_fibre_product_diagonal_square
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    BicategoricalTwoCommutativeSquare
      (two_fibre_product_right_vertical F G H).toCatHom
      (Δₚ H).toCatHom :=
  (two_fibre_product_diagonal_square_over F G H).toBicategoricalSquare

/-- Lemma 4.31.13: the displayed square with bottom map the diagonal `Δ_{C/D}` is a
`2`-fibre product diagram, expressed through the chapter's owner predicate
`Bicategory.IsFinal`. -/
theorem two_fibre_product_diagonal_isTwoFibreProduct
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) := by
  -- The explicit comparison equivalence feeds directly into the generic finality-transfer bridge.
  refine isFinal_of_toFunctorToCategoricalPullback_isEquivalence
    (Q := two_fibre_product_diagonal_square_over F G H) ?_
  have hcomp := two_fibre_product_diagonal_comparison_isEquivalence F G H
  exact hcomp

/-- Lemma 4.31.13, restated as the canonical `IsFinal` instance on the public square
`two_fibre_product_diagonal_square F G H`. -/
noncomputable instance
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) :=
  two_fibre_product_diagonal_isTwoFibreProduct F G H

end CategoryTheory.Limits
