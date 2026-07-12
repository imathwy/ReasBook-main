import StacksProject_2024.Chap08.Lemma_8_4_6.StackMorphismPullHom

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: for a fixed cover, transport one overlap morphism by conjugating it
with the pullback-comparison isomorphisms of the stack morphism. -/
noncomputable abbrev cover_descent_data_functor_hom_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) := by
  -- Route correction: record the fixed-cover overlap map in one stable conjugation normal form so
  -- the later object, morphism, and comparison constructions all rewrite against the same term.
  simpa using
    (FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.4.6: transporting the self-overlap morphism of descent data along a stack
morphism still yields the identity. -/
theorem cover_descent_data_functor_hom_self_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : T.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q g g hg hg = 𝟙 _ := by
  -- Collapse the middle factor to the identity with `D.hom_self`, then cancel the comparison
  -- isomorphism on both sides.
  change
    (FibredCategoryMor.pullbackComparison (H) g (D.obj I)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) ≫
        (FibredCategoryMor.pullbackComparison (H) g (D.obj I)).inv =
      𝟙 _
  have hmid :
      (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) =
        𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
    rw [D.hom_self q g hg]
    exact (FibredCategoryMor.fiberFunctor H Y).map_id _
  let e := FibredCategoryMor.pullbackComparison (H) g (D.obj I)
  calc
    e.hom ≫
        (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) ≫
        e.inv =
    e.hom ≫
        𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
        e.inv := by
          exact congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) hmid
    _ = e.hom ≫
          (𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
            (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
            e.inv) := by
          rfl
    _ = e.hom ≫ e.inv := by
          exact congrArg (fun k ↦ e.hom ≫ k) (Category.id_comp e.inv)
    _ = 𝟙 _ := e.hom_inv_id

/-- Helper for Lemma 8.4.6: transporting the cocycle relation of descent data along a stack
morphism preserves the same cocycle equation. -/
theorem cover_descent_data_functor_hom_comp_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₂ hf₁ hf₂ ≫
      cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₂ f₃ hf₂ hf₃ =
        cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₃ hf₁ hf₃ := by
  let F := FibredCategoryMor.fiberFunctor H Y
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let e₃ := FibredCategoryMor.pullbackComparison (H) f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  -- Rewrite both transported overlap maps into the shared comparison-conjugated normal form.
  have hnormalize :
      cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₂ hf₁ hf₂ ≫
          cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₂ f₃ hf₂ hf₃ =
        e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv := by
    change ((e₁.hom ≫ F.map d₁₂ ≫ e₂.inv) ≫ (e₂.hom ≫ F.map d₂₃ ≫ e₃.inv)) =
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv
    simp only [Category.assoc]
  -- Cancel the middle comparison pair before using the source cocycle identity.
  have hcancel_mid :
      e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv = F.map d₂₃ ≫ e₃.inv := by
    simpa only [F, Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        (H := H) f₂ (D.obj I₂) (k := F.map d₂₃ ≫ e₃.inv)
  have hcancel :
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ e₁.hom ≫ F.map d₁₂ ≫ k) hcancel_mid
  have hmap_comp :
      F.map d₁₂ ≫ F.map d₂₃ = F.map d₁₃ := by
    calc
      F.map d₁₂ ≫ F.map d₂₃ = F.map (d₁₂ ≫ d₂₃) := by
        rw [← F.map_comp]
      _ = F.map d₁₃ := by
        simpa only [d₁₂, d₂₃, d₁₃] using
          congrArg F.map (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
  have hassoc_map :
      e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ (F.map d₁₂ ≫ F.map d₂₃) ≫ e₃.inv := by
    simp only [Category.assoc]
  have hmap :
      e₁.hom ≫ (F.map d₁₂ ≫ F.map d₂₃) ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₃ ≫ e₃.inv := by
    exact congrArg (fun k ↦ e₁.hom ≫ k ≫ e₃.inv) hmap_comp
  have hfinal :
      e₁.hom ≫ F.map d₁₃ ≫ e₃.inv =
        cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
theorem cover_descent_data_functor_pullHom_right_tail_normalized
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) =
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂)) ≫
      (FibredCategoryMor.pullbackComparison
        (H) gf₂ (D.obj I₂)).inv := by
  -- Normalize the exact post-`hmid` right tail once so the shell proof can reuse it verbatim.
  let leftPrefix :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂))
  have htail :
      (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj
            (D.obj I₂))).inv ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) =
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂)) ≫
          (FibredCategoryMor.pullbackComparison
            (H) gf₂ (D.obj I₂)).inv := by
    -- This is exactly the owner-level right boundary already proved for the stack morphism.
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_right_boundary
        (H := H) f₂ g gf₂ hgf₂ (D.obj I₂)
  -- Whisker the boundary equality by the fixed left prefix used in the shell normalization.
  simpa only [leftPrefix, Category.assoc] using
    congrArg (fun k ↦ leftPrefix ≫ k) htail

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
theorem cover_descent_data_functor_pullHom_left_boundary_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let commonSuffix :=
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    let leftRaw :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₁ (D.obj I₁)).hom)
    let leftStrict :=
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv
    leftRaw ≫ commonSuffix = leftStrict ≫ commonSuffix := by
  -- Whisker the already-proved left boundary by the frozen suffix appearing in the shell theorem.
  let commonSuffix :=
    (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂))) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let leftRaw :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₁ (D.obj I₁)).hom)
  let leftStrict :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv
  change leftRaw ≫ commonSuffix = leftStrict ≫ commonSuffix
  simpa only [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ commonSuffix)
      (stack_morphism_pullbackComparison_pullHom_left_boundary
        (H := H) f₁ g gf₁ hgf₁ (D.obj I₁))

/-- Helper for Lemma 8.4.6: the middle inverse-naturality square can be inserted into the exact
owner-level shell that appears in the fixed-cover `pullHom` normalization. -/
theorem cover_descent_data_functor_pullHom_middle_naturality_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftPrefix :=
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let commonRightTail :=
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    let rawMiddle :=
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂)))
    let strictMiddle :=
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv
    leftPrefix ≫ rawMiddle ≫ commonRightTail =
      leftPrefix ≫ strictMiddle ≫ commonRightTail := by
  -- Insert the inverse-naturality square into the exact shell parenthesization.
  let leftPrefix :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let commonRightTail :=
    (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
      (FibredCategoryMor.pullbackComparison
        (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let rawMiddle :=
    (FibredCategoryMor.pullbackComparison (H) g
      (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂)))
  let strictMiddle :=
    (FibredCategoryMor.fiberFunctor H Y').map
      (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
        (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv
  change leftPrefix ≫ rawMiddle ≫ commonRightTail =
    leftPrefix ≫ strictMiddle ≫ commonRightTail
  simpa only [Category.assoc] using
    congrArg
      (fun k ↦ leftPrefix ≫ k ≫ commonRightTail)
      (stack_morphism_pullbackComparison_inv_naturality_over_vertical
        (H := H) (f := g) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
theorem cover_descent_data_functor_pullHom_hom_unfolded_raw_shell
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
              (H) f₁ (D.obj I₁)).hom ≫
            (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
            (FibredCategoryMor.pullbackComparison
              (H) f₂ (D.obj I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) := by
  -- Expand only the transported overlap map and the pseudofunctorial `pullHom` once, so the
  -- remaining shell proof can work entirely with named owner-level boundary rewrites.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, cover_descent_data_functor_hom_of_stack_morphism]
  rfl

/-- Helper for Lemma 8.4.6: split the single mapped threefold composite in the raw shell while
keeping the outer left and right whiskers fixed. -/
theorem cover_descent_data_functor_pullHom_map_threefold_comp_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
    let d := D.hom q f₁ f₂ hf₁ hf₂
    let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
    let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
    let leftTarget :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁)))
    let rightTarget :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget := by
  -- Split the visible threefold composite once, then reassociate back to the shell shape.
  let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let leftTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁)))
  let rightTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  change
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget
  calc
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ (FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv) ≫
        rightTarget := by
        exact
          congrArg
            (fun k ↦ leftTarget ≫ k ≫ rightTarget)
            (functor_map_threefold_comp FYg e₁.hom ((FibredCategoryMor.fiberFunctor H Y).map d) e₂.inv)
    _ =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget := by
        simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: after the boundary normalizations, the strict source shell folds back
to the source `pullHom`, with the comparison factors already whiskered on both sides. -/
theorem cover_descent_data_functor_pullHom_source_shell_fold_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
    let d := D.hom q f₁ f₂ hf₁ hf₂
    let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
    let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
    let leftSource :=
      (((canonicalFiberPseudofunctor A.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let rightSource :=
      (((canonicalFiberPseudofunctor A.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
    eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
        (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
        (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
      eg₁.hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) ≫
        eg₂.inv := by
  -- First fold the strict source shell under `FibredCategoryMor.fiberFunctor H Y'`, then restore the outer whiskers.
  let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hfold :
      (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource =
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- The source `pullHom` is definitionally the visible threefold composite.
    change
      (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource =
        (FibredCategoryMor.fiberFunctor H Y').map (leftSource ≫ FXg.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  calc
    eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
        (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
        (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
      eg₁.hom ≫
        ((FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource) ≫
        eg₂.inv := by
        simp only [Category.assoc]
    _ =
      eg₁.hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) ≫
        eg₂.inv := by
        exact congrArg (fun k ↦ eg₁.hom ≫ k ≫ eg₂.inv) hfold

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
theorem cover_descent_data_functor_pullHom_hom_normalized_shell
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
      (FibredCategoryMor.pullbackComparison
          (H) gf₂ (D.obj I₂)).inv := by
  -- Route correction: the fixed-cover source route now matches `Lemma_8_4_8` exactly. Expand
  -- the raw shell once, normalize left/middle/right in order, and then fold the source shell.
  let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  let cg₁ := FibredCategoryMor.pullbackComparison (H) g
    (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))
  let cg₂ := FibredCategoryMor.pullbackComparison (H) g
    (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        (((canonicalFiberPseudofunctor B.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (H) f₁ (D.obj I₁)).hom ≫
              (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              (FibredCategoryMor.pullbackComparison
                (H) f₂ (D.obj I₂)).inv)) ≫
          rightTarget := by
    -- Expand the transported overlap map only once before entering the boundary normalizations.
    exact
      cover_descent_data_functor_pullHom_hom_unfolded_raw_shell
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmap' :
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (H) f₁ (D.obj I₁)).hom ≫
              (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              (FibredCategoryMor.pullbackComparison
                (H) f₂ (D.obj I₂)).inv)) ≫
          rightTarget =
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Split the single mapped threefold composite in the raw shell.
    simpa only [FYg, d, e₁, e₂] using
      cover_descent_data_functor_pullHom_map_threefold_comp_whiskered
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hleft' :
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Normalize the left boundary while keeping the middle and right shell frozen.
    simpa only [Category.assoc, eg₁, leftSource] using
      cover_descent_data_functor_pullHom_left_boundary_whiskered
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmid' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Insert the middle inverse-naturality square before reflattening the shell.
    calc
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d)) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          ((FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫ k ≫ FYg.map e₂.inv ≫
                rightTarget)
              (stack_morphism_pullbackComparison_inv_naturality_over_vertical
                (H := H) (f := g) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell with the left and middle normalizations.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  have hright' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv := by
    -- Normalize the right boundary in the already-frozen post-middle shell.
    simpa only [Category.assoc, FYg, FXg, d, eg₁, eg₂, cg₂, leftSource, rightSource] using
      cover_descent_data_functor_pullHom_right_tail_normalized
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hstep_source_flat :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- Fold the strict source shell back to `pullHom`.
    simpa only [FXg, d, eg₁, eg₂, leftSource, rightSource] using
      cover_descent_data_functor_pullHom_source_shell_fold_whiskered
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  exact
    hprefix.trans
      (hright'.trans
        (hstep_source_flat.trans rfl))

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
theorem cover_descent_data_functor_pullHom_hom_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      cover_descent_data_functor_hom_of_stack_morphism
        (J := J) H T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let e₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  -- Normalize the transported shell once, then replace the middle factor by `D.pullHom_hom`.
  have hnormalize :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv := by
    -- Reuse the packaged shell lemma so the main proof stays flat.
    simpa only [e₁, e₂] using
      cover_descent_data_functor_pullHom_hom_normalized_shell
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmiddle :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv := by
    -- The middle factor is exactly the source descent-data pullback law transported by `H`.
    exact congrArg (fun k ↦ e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map k ≫ e₂.inv)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  have hfinal :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv =
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    -- Fold the target back to the fixed conjugation normal form.
    rfl
  exact hnormalize.trans (hmiddle.trans hfinal)

/-- Helper for Lemma 8.4.6: the component maps of a morphism of descent data remain compatible
after transporting fixed-cover overlap maps through a stack morphism. -/
theorem cover_descent_data_functor_comm_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H I₁.Y).map (φ.hom I₁))) ≫
      cover_descent_data_functor_hom_of_stack_morphism
        (J := J) H T D₂ q f₁ f₂ hf₁ hf₂ =
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₁ q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H I₂.Y).map (φ.hom I₂))) := by
  let F := FibredCategoryMor.fiberFunctor H Y
  let α₁ :=
    ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H I₁.Y).map (φ.hom I₁))
  let α₂ :=
    ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H I₂.Y).map (φ.hom I₂))
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁))
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))
  let e₁₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D₁.obj I₁)
  let e₁₂ := FibredCategoryMor.pullbackComparison (H) f₁ (D₂.obj I₁)
  let e₂₁ := FibredCategoryMor.pullbackComparison (H) f₂ (D₁.obj I₂)
  let e₂₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
    -- Move the left comparison shell across the transported vertical component map.
    simpa only [α₁, β₁, e₁₁, e₁₂] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        H (f := f₁) (φ := φ.hom I₁)
  have hmid :
      β₁ ≫ F.map d₂ = F.map d₁ ≫ β₂ := by
    -- The middle square is the source descent-data compatibility of `φ`, mapped through `H`.
    calc
      β₁ ≫ F.map d₂ =
          F.map
            ((((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁)) ≫
              d₂) := by
            dsimp [β₁]
            rw [← F.map_comp]
      _ = F.map
            (d₁ ≫
              (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))) := by
            simpa only [d₁, d₂] using congrArg F.map (φ.comm q f₁ f₂ hf₁ hf₂)
      _ = F.map d₁ ≫ β₂ := by
            dsimp [β₂]
            rw [F.map_comp]
  have hright :
      β₂ ≫ e₂₂.inv = e₂₁.inv ≫ α₂ := by
    -- Move the right comparison inverse across the transported vertical component map.
    simpa only [α₂, β₂, e₂₁, e₂₂] using
      stack_morphism_pullbackComparison_inv_naturality_over_vertical
        H (f := f₂) (φ := φ.hom I₂)
  -- Rewrite both sides into the common comparison-conjugated normal form.
  have hnormalize_left :
      α₁ ≫ cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₂ q f₁ f₂ hf₁ hf₂ =
        (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv := by
    change α₁ ≫ (e₁₂.hom ≫ F.map d₂ ≫ e₂₂.inv) =
      (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv
    simp only [Category.assoc]
  have hleft' :
      (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv =
        (e₁₁.hom ≫ β₁) ≫ F.map d₂ ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ k ≫ F.map d₂ ≫ e₂₂.inv) hleft
  have hassoc_left :
      (e₁₁.hom ≫ β₁) ≫ F.map d₂ ≫ e₂₂.inv =
        e₁₁.hom ≫ (β₁ ≫ F.map d₂) ≫ e₂₂.inv := by
    simp only [Category.assoc]
  have hmid' :
      e₁₁.hom ≫ (β₁ ≫ F.map d₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ (F.map d₁ ≫ β₂) ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ k ≫ e₂₂.inv) hmid
  have hassoc_mid :
      e₁₁.hom ≫ (F.map d₁ ≫ β₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ F.map d₁ ≫ (β₂ ≫ e₂₂.inv) := by
    simp only [Category.assoc]
  have hright' :
      e₁₁.hom ≫ F.map d₁ ≫ (β₂ ≫ e₂₂.inv) =
        e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ F.map d₁ ≫ k) hright
  have hnormalize_right :
      e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) =
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    change e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) =
      (e₁₁.hom ≫ F.map d₁ ≫ e₂₁.inv) ≫ α₂
    simp only [Category.assoc]
  exact
    hnormalize_left.trans
      (hleft'.trans (hassoc_left.trans (hmid'.trans (hassoc_mid.trans (hright'.trans hnormalize_right)))))

/-- Helper for Lemma 8.4.6: a stack morphism induces the fixed-cover functor on descent data by
acting componentwise and conjugating overlap maps with the pullback-comparison isomorphisms. -/
noncomputable def cover_descent_data_functor_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor B.p).DescentData (fun I : T.Arrow ↦ I.f)) where
  obj D :=
    { obj := fun I ↦ (FibredCategoryMor.fiberFunctor H I.Y).obj (D.obj I)
      hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        -- Delegate the only remaining object-field transport obligation to the dedicated helper.
        simpa using
          cover_descent_data_functor_pullHom_hom_of_stack_morphism
            (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := by
        intro Y q I g hg
        -- The transported self-overlap map is the identity by the comparison cancellation lemma.
        simpa using
          cover_descent_data_functor_hom_self_of_stack_morphism
            (J := J) H T D q g hg
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        -- Reuse the dedicated cocycle transport lemma so the object constructor stays flat.
        simpa using
          cover_descent_data_functor_hom_comp_of_stack_morphism
            (J := J) H T D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map {D₁ D₂} φ :=
    { hom := fun I ↦ (FibredCategoryMor.fiberFunctor H I.Y).map (φ.hom I)
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- The componentwise descent-data compatibility is exactly the conjugation lemma above.
        simpa using
          cover_descent_data_functor_comm_of_stack_morphism
            (J := J) H T φ q f₁ f₂ hf₁ hf₂ }
  map_id X := by
    -- The fixed-cover transport functor acts componentwise through the fiber functors.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (FibredCategoryMor.fiberFunctor H I.Y).map (𝟙 (X.obj I)) = 𝟙 ((FibredCategoryMor.fiberFunctor H I.Y).obj (X.obj I))
    exact (FibredCategoryMor.fiberFunctor H I.Y).map_id (X.obj I)
  map_comp f g := by
    -- Composition is computed componentwise because every fiber functor is an ordinary functor.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (FibredCategoryMor.fiberFunctor H I.Y).map (f.hom I ≫ g.hom I) =
      (FibredCategoryMor.fiberFunctor H I.Y).map (f.hom I) ≫ (FibredCategoryMor.fiberFunctor H I.Y).map (g.hom I)
    exact (FibredCategoryMor.fiberFunctor H I.Y).map_comp (f.hom I) (g.hom I)

end CategoryTheory
