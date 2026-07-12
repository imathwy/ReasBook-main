import StacksProject_2024.Chap08.Lemma_8_4_6.CoverDescentTransport

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: equivalence of fixed-cover canonical descent functors can be
transported across a comparison isomorphism that is whiskered by equivalences on both sides. -/
theorem isEquivalence_iff_of_whiskered_iso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (K : A ⥤ B) (TF : D ⥤ E) (F₁ : A ⥤ D) (F₂ : B ⥤ E)
    [K.IsEquivalence] [TF.IsEquivalence]
    (e : F₁ ⋙ TF ≅ K ⋙ F₂) :
    F₁.IsEquivalence ↔ F₂.IsEquivalence := by
  constructor
  · intro h₁
    -- Compose with the target equivalence and then cancel the source equivalence.
    letI : F₁.IsEquivalence := h₁
    have hcomp₁ : (F₁ ⋙ TF).IsEquivalence :=
      Functor.isEquivalence_trans F₁ TF
    have hcomp₂ : (K ⋙ F₂).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).1 hcomp₁
    letI : (K ⋙ F₂).IsEquivalence := hcomp₂
    exact Functor.isEquivalence_of_comp_left K F₂
  · intro h₂
    -- Reverse the same cancellation argument across the comparison isomorphism.
    letI : F₂.IsEquivalence := h₂
    have hcomp₂ : (K ⋙ F₂).IsEquivalence :=
      Functor.isEquivalence_trans K F₂
    have hcomp₁ : (F₁ ⋙ TF).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).2 hcomp₂
    letI : (F₁ ⋙ TF).IsEquivalence := hcomp₁
    exact Functor.isEquivalence_of_comp_right F₁ TF

/-- Helper for Lemma 8.4.6: the right leg of the canonical target overlap, after postcomposing
with the mapped `I₂`-comparison hom, is exactly the specialized left-boundary shell over `q`. -/
theorem canonical_target_descent_right_leg_postcompose_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₂ : T.Arrow}
    (f₂ : V ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) =
      (FibredCategoryMor.pullbackComparison (H) q x).hom ≫
        (FibredCategoryMor.fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (H) f₂
          (((canonicalFiberPseudofunctor A.p).map I₂.f.op.toLoc).toFunctor.obj x)).inv := by
  -- This is exactly the specialized left-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    stack_morphism_pullbackComparison_pullHom_left_boundary
      (H := H) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x

/-- Helper for Lemma 8.4.6: the left leg of the canonical target overlap is the specialized
right-boundary shell whose target comparison lives over the common map `q`. -/
theorem canonical_target_descent_left_leg_normalized_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ : T.Arrow}
    (f₁ : V ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    (FibredCategoryMor.pullbackComparison (H) f₁
        (((canonicalFiberPseudofunctor A.p).map I₁.f.op.toLoc).toFunctor.obj x)).inv ≫
      (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) =
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (H) q x).inv := by
  -- This is exactly the specialized right-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    stack_morphism_pullbackComparison_pullHom_right_boundary
      (H := H) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) x

/-- Helper for Lemma 8.4.6: before cancelling the final mapped `I₂`-comparison, the canonical
target overlap shell already agrees with the grouped comparison-conjugate shell on a fixed cover. -/
theorem canonical_target_descent_component_comm_rhs_owner_normal_form_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
        ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
          (((canonicalFiberPseudofunctor A.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
  let F₁ := ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let Fq := ((canonicalFiberPseudofunctor B.p).map q.op.toLoc).toFunctor
  let D :=
    ((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x
  let e₁ := FibredCategoryMor.pullbackComparison (H) I₁.f x
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  let eq₁ := FibredCategoryMor.pullbackComparison (H) f₁
    (((canonicalFiberPseudofunctor A.p).map I₁.f.op.toLoc).toFunctor.obj x)
  let eq₂ := FibredCategoryMor.pullbackComparison (H) f₂
    (((canonicalFiberPseudofunctor A.p).map I₂.f.op.toLoc).toFunctor.obj x)
  let eqq := FibredCategoryMor.pullbackComparison (H) q x
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  let targetLeft :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x))
  let targetRight :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x))
  let core :=
    F₁.map e₁.hom ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj D).hom q f₁ f₂ hf₁ hf₂
  have hleft_raw :
      eq₁.inv ≫ F₁.map e₁.inv ≫ targetLeft =
        (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv := by
    -- Normalize the left leg to the common `q`-comparison shell.
    simpa only [F₁, eq₁, e₁, leftSource, eqq, targetLeft] using
      canonical_target_descent_left_leg_normalized_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hleft_cancel₁ :
      F₁.map e₁.inv ≫ targetLeft =
        eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv) := by
    -- Cancel the iterated `f₁`-comparison on the far left.
    exact (Iso.inv_comp_eq eq₁).1 (by simpa only [Category.assoc] using hleft_raw)
  have hleft :
      targetLeft =
        F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv := by
    -- Cancel the mapped `I₁`-comparison to isolate the raw target left leg.
    exact
      (Iso.inv_comp_eq (F₁.mapIso e₁)).1 <| by
        simpa only [Category.assoc] using hleft_cancel₁
  have hright :
      targetRight ≫ F₂.map e₂.hom =
        eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv := by
    -- Normalize the right leg after the final mapped `I₂`-comparison postcomposition.
    simpa only [F₂, e₂, eqq, rightSource, eq₂] using
      canonical_target_descent_right_leg_postcompose_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hq_cancel :
      eqq.inv ≫ eqq.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) =
        (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv := by
    -- The inserted `q`-comparison inverse-hom pair cancels before the frozen right tail.
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        (H := H) (g := q) (x := x)
        (k := (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv)
  have hcore :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        core := by
    -- Rewrite left and right legs to the common `q`-comparison shell, cancel that shell, and
    -- then fold the mapped source overlap back to the transported source descent datum.
    let lhsOwner :=
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        F₂.map e₂.hom
    have hstart :
        lhsOwner = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
      calc
        lhsOwner = (targetLeft ≫ targetRight) ≫ F₂.map e₂.hom := by
          rfl
        _ = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
          simp only [Category.assoc]
    have hstep_right :
        lhsOwner = targetLeft ≫ (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      exact hstart.trans (congrArg (fun k ↦ targetLeft ≫ k) hright)
    have hstep_left :
        lhsOwner =
          (F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv) ≫
            (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      exact hstep_right.trans <|
        congrArg
          (fun k ↦ k ≫ (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv))
          hleft
    have hstep_flat :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv ≫ eqq.hom ≫
              (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      simpa only [Category.assoc] using hstep_left
    have hstep_cancel :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫
              ((FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv)) := by
      exact hstep_flat.trans <|
        congrArg
          (fun k ↦
            F₁.map e₁.hom ≫ eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ k))
          hq_cancel
    have hstep_map :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            (FibredCategoryMor.fiberFunctor H V).map (leftSource ≫ rightSource) ≫ eq₂.inv := by
      have hstep_grouped :
          lhsOwner =
            F₁.map e₁.hom ≫ eq₁.hom ≫
              ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫
                (FibredCategoryMor.fiberFunctor H V).map rightSource) ≫ eq₂.inv := by
        simpa only [Category.assoc] using hstep_cancel
      exact hstep_grouped.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ k ≫ eq₂.inv)
          ((FibredCategoryMor.fiberFunctor H V).map_comp leftSource rightSource).symm
    -- Fold the source overlap shell to the fixed-cover transport functor's normal form.
    simpa only [lhsOwner] using hstep_map.trans rfl
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The final mapped `I₂`-comparison pair cancels on the right.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hinsert :
      core =
        ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
            ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
              (((canonicalFiberPseudofunctor A.p).toDescentData
                (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
          (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
    -- Insert the final mapped inverse-hom identity on the right so the owner theorem has the
    -- postcomposed shape needed by the later cancellation lemma.
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        simp only [Category.assoc]
      _ =
          ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
              ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
                (((canonicalFiberPseudofunctor A.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
            simpa only [core, D, F₁, F₂, e₁, e₂, Category.assoc]
  exact hcore.trans hinsert

/-- Helper for Lemma 8.4.6: the canonical target overlap morphism is the pullback-comparison
conjugate of the transported canonical source overlap morphism on a fixed cover. -/
theorem canonical_target_descent_hom_eq_comparison_conjugate_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
      (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
        ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
          (((canonicalFiberPseudofunctor A.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv) := by
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  -- Cancel the final mapped `I₂`-comparison in the grouped owner normal form.
  exact
    (Iso.cancel_iso_hom_right _ _ (F₂.mapIso e₂)).1 <| by
      change
        ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
            F₂.map e₂.hom =
          ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
              ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
                (((canonicalFiberPseudofunctor A.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              F₂.map e₂.inv) ≫
            F₂.map e₂.hom
      simpa only [F₂, e₂, Category.assoc] using
        canonical_target_descent_component_comm_rhs_owner_normal_form_of_stack_morphism
          (J := J) (H := H) T x (q := q)
          (I₁ := I₁) (I₂ := I₂)
          (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)

/-- Helper for Lemma 8.4.6: the pullback-comparison components identify the image of the
canonical source descent datum of `x` with the canonical target descent datum of `H(x)`. -/
theorem cover_descent_data_functor_of_stack_morphism_component_comm
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
        (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x)).hom
          q f₁ f₂ hf₁ hf₂ =
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  let core :=
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
        (((canonicalFiberPseudofunctor A.p).toDescentData
          (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂
  have hstrong :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
        core ≫ F₂.map e₂.inv := by
    -- Reassociate the strong comparison-conjugate theorem to the `core ≫ map(inv)` form.
    simpa only [core, F₂, e₂, Category.assoc] using
      canonical_target_descent_hom_eq_comparison_conjugate_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hpost :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
    -- Postcompose the strong comparison-conjugate identity by the mapped right comparison hom.
    exact congrArg
      (fun k ↦ k ≫ F₂.map e₂.hom)
      hstrong
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The mapped right comparison pair cancels by functoriality.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hcancel : (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom = core := by
    -- The mapped right comparison pair cancels in one step.
    calc
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
          core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
            simp only [Category.assoc]
      _ = core ≫ 𝟙 _ := by
            exact congrArg (fun k ↦ core ≫ k) htail
      _ = core := by
            rw [Category.comp_id]
  have hpost' :
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
        ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom := by
    exact hpost.symm
  exact hcancel.symm.trans hpost'

/-- Helper for Lemma 8.4.6: the fixed-cover transport functor induced by a stack morphism carries
canonical descent data to canonical descent data, with components given by pullback comparison. -/
noncomputable abbrev cover_descent_data_functor_of_stack_morphism_toDescentData_iso
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) :
    (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) H T) ≅
      ((FibredCategoryMor.fiberFunctor H U) ⋙
        ((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f))) := by
  let η :
      ((FibredCategoryMor.fiberFunctor H U) ⋙
          ((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f))) ≅
        (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
          cover_descent_data_functor_of_stack_morphism (J := J) H T) :=
    NatIso.ofComponents
      (fun x ↦
        -- Package the pullback-comparison components into an isomorphism of descent data.
        Pseudofunctor.DescentData.isoMk
          (fun I ↦ FibredCategoryMor.pullbackComparison (H) I.f x)
          (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            cover_descent_data_functor_of_stack_morphism_component_comm
              (J := J) (H := H) T x (q := q)
              (I₁ := I₁) (I₂ := I₂)
              (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)))
      (fun φ ↦ by
        -- Naturality is exactly the hom-side pullback-comparison square on each cover leg.
        apply Pseudofunctor.DescentData.hom_ext
        intro I
        rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
        simpa only [Functor.comp_map, cover_descent_data_functor_of_stack_morphism] using
          stack_morphism_pullbackComparison_naturality_over_vertical
            (H := H) (f := I.f) (φ := φ))
  exact η.symm

/-- Helper for Lemma 8.4.6: the forward component of the fixed-cover comparison isomorphism from
transported source descent data to target canonical descent data is exactly the inverse
pullback-comparison morphism on each cover leg. -/
theorem cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (x : A.p.Fiber U) (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) H T).hom.app x).hom I) =
      (FibredCategoryMor.pullbackComparison (H) I.f x).inv := by
  -- Unfold the packaged comparison only far enough to read off its objectwise component.
  rfl

/-- Helper for Lemma 8.4.6: the inverse component of the fixed-cover comparison isomorphism from
transported source descent data to target canonical descent data is exactly the forward
pullback-comparison morphism on each cover leg. -/
theorem cover_descent_data_functor_of_stack_morphism_toDescentData_iso_inv_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (x : A.p.Fiber U) (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) H T).inv.app x).hom I) =
      (FibredCategoryMor.pullbackComparison (H) I.f x).hom := by
  -- The inverse direction is the same packaged `isoMk`, read before taking the final symmetry.
  rfl

/-- Helper for Lemma 8.4.6: once the fixed-cover canonical descent functors for `X`, `Y`, and `S`
are frozen with their exact owners, Chapter 4's `two_fibre_product_map_isEquivalence` applies
directly to the comparison isomorphisms induced by `F` and `G`. -/
theorem cover_descent_two_fibre_product_map_isEquivalence_bridge_explicit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (two_fibre_product_map
      (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor G) T)
      ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence := by
  let ΦY :=
    ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let ΦX :=
    ((canonicalFiberPseudofunctor X.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let ΦS :=
    ((canonicalFiberPseudofunctor S.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let α :
      ΦY ⋙ cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T ≅
        fiberFunctor G U ⋙ ΦS :=
    cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor G) T
  let β :
      fiberFunctor F U ⋙ ΦS ≅
        ΦX ⋙ cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T :=
    (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor F) T).symm
  -- Freeze the three stack-side fixed-cover canonical descent equivalences before invoking the
  -- categorical pullback comparison from Chapter 4.
  let hY : ΦY.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J Y.p).1
      inferInstance U T
  letI : ΦY.IsEquivalence := hY
  let hX : ΦX.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor X.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J X.p).1
      inferInstance U T
  letI : ΦX.IsEquivalence := hX
  let hS : ΦS.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor S.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J S.p).1
      inferInstance U T
  letI : ΦS.IsEquivalence := hS
  letI : ΦS.Faithful := hS.faithful
  letI : ΦS.Full := hS.full
  -- The comparison isomorphisms already match the owner order expected by
  -- `two_fibre_product_map_isEquivalence`.
  change (two_fibre_product_map α β).IsEquivalence
  exact
    @two_fibre_product_map_isEquivalence
      _ _ _ _ _ _ _ _ _ _ _ _
      (fiberFunctor F U)
      (fiberFunctor G U)
      ΦX
      ΦY
      ΦS
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T)
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T)
      α β hY hX hS.full hS.faithful

/-- Helper for Lemma 8.4.6: whiskering the fixed-cover pullback-model comparison by the owner
fiber equivalence from Lemma `4.32.5` preserves equivalence once both pieces are frozen with
their exact local owners. -/
theorem cover_descent_pullback_model_isEquivalence_bridge_explicit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor) ⋙
      two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence := by
  let eFib := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    (toBasedFunctor F) (toBasedFunctor G) U
  let TF :=
    two_fibre_product_map
      (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor G) T)
      ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor F) T).symm)
  -- Freeze the two factors separately so the whiskered equivalence is obtained by a single
  -- application of `Functor.isEquivalence_trans`.
  letI : eFib.functor.IsEquivalence := by
    infer_instance
  have hTF : TF.IsEquivalence := by
    -- Route correction: restate the exact local alias `TF` before invoking the bridge theorem.
    change
      (two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence
    exact
      cover_descent_two_fibre_product_map_isEquivalence_bridge_explicit
        (J := J) F G (T := T)
  letI : TF.IsEquivalence := hTF
  exact
    @Functor.isEquivalence_trans _ _ _ _ _ _
      eFib.functor TF inferInstance hTF

/-- Helper for Lemma 8.4.6: the fixed-cover left projection from descent data on the explicit
stack-level `2`-fibre product is the descent-data functor induced by the ambient left projection
of the Chapter 4 owner. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_left_projection
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)) :=
  cover_descent_data_functor_of_stack_morphism
    (J := J)
    (FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G))
    T

/-- Helper for Lemma 8.4.6: the fixed-cover right projection from descent data on the explicit
stack-level `2`-fibre product is the descent-data functor induced by the ambient right projection
of the Chapter 4 owner. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_right_projection
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor Y.p).DescentData (fun I : T.Arrow ↦ I.f)) :=
  cover_descent_data_functor_of_stack_morphism
    (J := J)
    (FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G))
    T

end CategoryTheory
