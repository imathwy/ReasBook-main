import StacksProject_2024.Chap08.Lemma_8_4_3.PullbackComparisonNaturality
import StacksProject_2024.Chap08.Lemma_8_4_3.AmbientIsoClosure

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: the forward overlap map is the comparison-conjugated image of the
restricted overlap morphism inside the ambient inverse-image fiber. -/
noncomputable def restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
          (D.obj I₁)).obj) ⟶
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
          (D.obj I₂)).obj) :=
  (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
      (D.hom q f₁ f₂ hf₁ hf₂)).hom ≫
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom

/-- Helper for Lemma 8.4.3: the comparison-conjugated forward overlap map satisfies the fixed-
cover pullback law once the two boundary comparison maps are rewritten by naturality. -/
theorem restricted_cover_descent_isoClosure_obj_hom_pullHom_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  -- The remaining work is the standard boundary normalization for the pullback-comparison shell,
  -- followed by the source descent-data pullback law on the middle restricted overlap morphism.
  sorry

/-- Helper for Lemma 8.4.3: on equal legs, the comparison-conjugated forward overlap map reduces
to the identity after the comparison shell cancels. -/
theorem restricted_cover_descent_isoClosure_obj_hom_self
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      𝟙 _ := by
  -- Expand the conjugation shell, cancel the comparison isomorphisms, and reduce to the
  -- restricted descent identity axiom on the middle morphism.
  let e :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g (D.obj I)
  have hmid :
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom = 𝟙 _ := by
    calc
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom =
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (𝟙
            (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map g.op.toLoc).toFunctor.obj
              (D.obj I)))).hom := by
          rw [D.hom_self q g hg]
      _ = 𝟙 _ := by
          rfl
  calc
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      e.inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom ≫
        e.hom := by
          rfl
    _ = e.inv ≫ 𝟙 _ ≫ e.hom := by
          exact congrArg (fun k ↦ e.inv ≫ k ≫ e.hom) hmid
    _ = 𝟙 _ := by
          simp

/-- Helper for Lemma 8.4.3: the comparison-conjugated forward overlap maps satisfy the cocycle
relation after the boundary comparison maps telescope. -/
theorem restricted_cover_descent_isoClosure_obj_hom_comp
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
  -- Reassociate the two conjugated shells so the middle comparison pair cancels, then the
  -- remaining core is exactly the restricted descent cocycle relation.
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let e₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)
  let e₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)
  let e₃ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  have hnormalize :
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    change ((e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom) ≫
        (e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom)) =
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom
    simp only [Category.assoc]
  have hassoc_cancel :
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom =
        ((e₁.inv ≫ (F.map d₁₂).hom) ≫ (e₂.hom ≫ e₂.inv)) ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simp only [Category.assoc]
  have hcancel₁ :
      ((e₁.inv ≫ (F.map d₁₂).hom) ≫ (e₂.hom ≫ e₂.inv)) ≫ (F.map d₂₃).hom ≫ e₃.hom =
        ((e₁.inv ≫ (F.map d₁₂).hom) ≫ 𝟙 _) ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simpa only [F] using
      congrArg
        (fun k ↦ ((e₁.inv ≫ (F.map d₁₂).hom) ≫ k) ≫ (F.map d₂₃).hom ≫ e₃.hom)
        e₂.hom_inv_id
  have hcancel₂ :
      ((e₁.inv ≫ (F.map d₁₂).hom) ≫ 𝟙 _) ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simp only [Category.id_comp, Category.assoc]
  have hcancel :
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    exact hassoc_cancel.trans (hcancel₁.trans hcancel₂)
  have hmap_comp :
      (F.map d₁₂).hom ≫ (F.map d₂₃).hom = (F.map d₁₃).hom := by
    have hmap_comp_fiber : F.map d₁₂ ≫ F.map d₂₃ = F.map d₁₃ := by
      simpa only [Functor.map_comp, d₁₂, d₂₃, d₁₃] using congrArg F.map
        (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    exact congrArg (fun k ↦ k.hom) hmap_comp_fiber
  have hassoc_map :
      e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ ((F.map d₁₂).hom ≫ (F.map d₂₃).hom) ≫ e₃.hom := by
    simp only [Category.assoc]
  have hmap :
      e₁.inv ≫ ((F.map d₁₂).hom ≫ (F.map d₂₃).hom) ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₃).hom ≫ e₃.hom := by
    exact congrArg (fun k ↦ e₁.inv ≫ k ≫ e₃.hom) hmap_comp
  have hfinal :
      e₁.inv ≫ (F.map d₁₃).hom ≫ e₃.hom =
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.4.3: a morphism of restricted descent data commutes with the new forward
comparison-conjugated overlap maps. -/
theorem restricted_cover_descent_to_isoClosure_map_comm_via_pullbackComparison
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).map
          (φ.hom I₁)).hom ≫
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).map
          (φ.hom I₂)).hom := by
  -- TODO: rewrite both overlap maps to the same comparison-conjugated shell, move the boundary
  -- terms by the pullback-comparison naturality lemmas, and apply `φ.comm` to the middle term.
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let α₁ :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).map
        (φ.hom I₁)).hom
  let α₂ :=
    ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).map
        (φ.hom I₂)).hom
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
        (φ.hom I₁))
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
        (φ.hom I₂))
  let e₁₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)
  let e₁₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)
  let e₂₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D₁.obj I₂)
  let e₂₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.inv = e₁₁.inv ≫ β₁.hom := by
    simpa only [α₁, β₁, e₁₁, e₁₂,
      restricted_pullback_vs_ambient_pullback_comparison] using
      (fullSubcategory_inclusion_pullbackComparison_naturality_over_vertical
        (J := J) (p := p) (P := P) hpullback (f := f₁) (φ := φ.hom I₁))
  have hmid :
      β₁.hom ≫ (F.map d₂).hom = (F.map d₁).hom ≫ β₂.hom := by
    have hmid_fiber : β₁ ≫ F.map d₂ = F.map d₁ ≫ β₂ := by
      calc
        β₁ ≫ F.map d₂ =
            F.map
              ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
                  (φ.hom I₁)) ≫ d₂) := by
              dsimp [β₁]
              rw [← F.map_comp]
        _ = F.map
              (d₁ ≫
                (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
                  (φ.hom I₂))) := by
              simpa only [d₁, d₂] using congrArg F.map (φ.comm q f₁ f₂ hf₁ hf₂)
        _ = F.map d₁ ≫ β₂ := by
              dsimp [β₂]
              rw [F.map_comp]
    exact congrArg (fun k ↦ k.hom) hmid_fiber
  have hright :
      e₂₁.hom ≫ α₂ = β₂.hom ≫ e₂₂.hom := by
    simpa only [α₂, β₂, e₂₁, e₂₂,
      restricted_pullback_vs_ambient_pullback_comparison] using
      (fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
        (J := J) (p := p) (P := P) hpullback (f := f₂) (φ := φ.hom I₂)).symm
  have hlast :
      (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ =
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    rfl
  have hchain :
      α₁ ≫
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
        (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ := by
    calc
      α₁ ≫
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
        α₁ ≫ e₁₂.inv ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          rfl
      _ = (α₁ ≫ e₁₂.inv) ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          simp only [Category.assoc]
      _ = (e₁₁.inv ≫ β₁.hom) ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          exact congrArg (fun k ↦ k ≫ (F.map d₂).hom ≫ e₂₂.hom) hleft
      _ = e₁₁.inv ≫ (β₁.hom ≫ (F.map d₂).hom) ≫ e₂₂.hom := by
          simp only [Category.assoc]
      _ = e₁₁.inv ≫ ((F.map d₁).hom ≫ β₂.hom) ≫ e₂₂.hom := by
          exact congrArg (fun k ↦ e₁₁.inv ≫ k ≫ e₂₂.hom) hmid
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ (β₂.hom ≫ e₂₂.hom) := by
          simp only [Category.assoc]
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ (e₂₁.hom ≫ α₂) := by
          exact congrArg (fun k ↦ e₁₁.inv ≫ (F.map d₁).hom ≫ k) hright.symm
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom ≫ α₂ := by
          rfl
      _ = (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ := by
          simp only [Category.assoc]
  exact hchain.trans hlast

end RestrictedFibered

end
