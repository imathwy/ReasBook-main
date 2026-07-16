import stacks_proof.stacks_project.Chap08.Lemma_8_5_3.CoverForgetNormalization
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2_Core

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the forgotten overlap maps satisfy the pullback-compatibility
condition for descent data once the inclusion pullback-comparison shell is normalized. -/
private theorem associated_groupoid_cover_forget_pullHom_hom
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (associated_groupoid_cover_forget_hom
          (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      associated_groupoid_cover_forget_hom
        (J := J) (p := p) S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) :=
by
  let e₁ := fibred_morphism_pullbackComparison
    (associated_groupoid_inclusion (p := p)) gf₁ (D.obj I₁)
  let e₂ := fibred_morphism_pullbackComparison
    (associated_groupoid_inclusion (p := p)) gf₂ (D.obj I₂)
  have hnormalize :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (associated_groupoid_cover_forget_hom
            (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv := by
    -- Reuse the owner-side shell normalization so the local theorem only packages the source law.
    simpa only [e₁, e₂] using
      associated_groupoid_cover_forget_pullHom_hom_normalized_shell
        (J := J) (p := p) S D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmiddle :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv := by
    -- Replace the middle factor by the source descent-data pullback identity.
    exact
      congrArg
        (fun k ↦ e₁.hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map k ≫
          e₂.inv)
        (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  have hfinal :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv =
        associated_groupoid_cover_forget_hom
          (J := J) (p := p) S D q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    -- Fold the target back to the fixed comparison-conjugated normal form.
    rfl
  exact hnormalize.trans (hmiddle.trans hfinal)

/-- Helper for Lemma 8.5.3: the source-faithful comparison from associated-groupoid descent data
to ambient descent data should be the fixed-cover functor induced by the inclusion. -/
noncomputable def associated_groupoid_cover_forget_descent_data
    [p.IsFibered] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor p).DescentData (fun I : S.Arrow ↦ I.f)) where
  obj D :=
    { obj := fun I ↦
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).obj
          (D.obj I)
      hom := fun {_} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦
        associated_groupoid_cover_forget_hom
          (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂
      pullHom_hom := fun {Y' Y} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
        -- The remaining transport shell is isolated in the dedicated fixed-cover helper above.
        associated_groupoid_cover_forget_pullHom_hom
          (J := J) (p := p) S D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := fun {_} q {I} g hg ↦
        associated_groupoid_cover_forget_hom_self
          (J := J) (p := p) S D q g hg
      hom_comp := fun {_} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
        associated_groupoid_cover_forget_hom_comp
          (J := J) (p := p) S D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map {D₁ D₂} φ :=
    -- Forget the strongly-cartesian proof on each component and reuse the mapped compatibility.
    { hom := fun I ↦
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).map
          (φ.hom I) :
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).obj
            (D₁.obj I)) ⟶
              ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).obj
                (D₂.obj I)))
      comm := fun {_} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦
        associated_groupoid_cover_forget_morphism_comm
          (J := J) (p := p) S φ (q := q)
          (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂) }
  map_id X := by
    -- Compare the forgotten identity with the identity morphism componentwise.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).map_id
        (X.obj I)
  map_comp f g := by
    -- Compare the forgotten composite with the composite of forgotten morphisms componentwise.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y).map_comp
        (f.hom I) (g.hom I)

/-- Helper for Lemma 8.5.3: on one fixed cover, the pullback-comparison components already
identify the forgotten associated descent datum of `x` with the ambient descent datum of the
forgotten fiber object. -/
private theorem associated_groupoid_cover_forget_component_comm_rhs_owner_normal_form
    [p.IsFibered] {U : C} (S : J.Cover U) (x : (stronglyCartesianProjection p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
        q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
        associated_groupoid_cover_forget_hom (J := J) (p := p) S
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)
          q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x).inv)) ≫
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x).hom) := by
  -- Rewrite only the ambient overlap term; the remaining step is the later right-cancellation.
  rw [ambient_cover_toDescentData_ofObj_hom_eq_comparison_conjugate
    (J := J) (p := p) (U := U) S x (q := q) (f₁ := f₁) (f₂ := f₂)
    (hf₁ := hf₁) (hf₂ := hf₂)]
  rfl

/-- Helper for Lemma 8.5.3: on one fixed cover, the pullback-comparison components already
identify the forgotten associated descent datum of `x` with the ambient descent datum of the
forgotten fiber object. -/
private theorem associated_groupoid_cover_forget_component_comm
    [p.IsFibered] {U : C} (S : J.Cover U) (x : (stronglyCartesianProjection p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
      associated_groupoid_cover_forget_hom (J := J) (p := p) S
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj x)
        q f₁ f₂ hf₁ hf₂ =
    (((canonicalFiberPseudofunctor p).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
        q f₁ f₂ hf₁ hf₂ ≫
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x).hom) :=
by
  let F₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let e₂ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x
  let core :=
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
      associated_groupoid_cover_forget_hom (J := J) (p := p) S
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj x)
        q f₁ f₂ hf₁ hf₂
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The right comparison shell cancels after one `Functor.map_comp` rewrite.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have howner :
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
        (((canonicalFiberPseudofunctor p).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
            q f₁ f₂ hf₁ hf₂ ≫
          F₂.map e₂.hom := by
    -- Reassociate the owner normal form exactly once so the final comparison is a plain symmetry.
    symm
    simpa only [core, F₂, e₂, Category.assoc] using
      associated_groupoid_cover_forget_component_comm_rhs_owner_normal_form
        (J := J) (p := p) S x (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hinsert :
      core = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
    -- Insert the mapped inverse-hom identity on the right before invoking the owner normal form.
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        exact (Category.assoc core (F₂.map e₂.inv) (F₂.map e₂.hom)).symm
  -- Insert the mapped inverse-hom identity on the right, then rewrite the owner shell by the
  -- dedicated ambient comparison normal form.
  simpa only [core] using hinsert.trans howner

/-- Helper for Lemma 8.5.3: the associated-groupoid canonical descent functor compares to the
ambient one after forgetting strongly-cartesian structure on the fixed cover. -/
noncomputable def associated_groupoid_cover_forget_toDescentData_iso
    [p.IsFibered] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
      (fun I : S.Arrow ↦ I.f)) ⋙
        associated_groupoid_cover_forget_descent_data (J := J) (p := p) S ≅
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U) ⋙
        ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)) :=
  let η :
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U) ⋙
          ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)) ≅
        ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙
          associated_groupoid_cover_forget_descent_data (J := J) (p := p) S :=
    NatIso.ofComponents
      (fun x ↦
        -- Package the cover-leg pullback comparisons into the fixed-cover comparison isomorphism.
        Pseudofunctor.DescentData.isoMk
          (fun I ↦
            fibred_morphism_pullbackComparison
              (associated_groupoid_inclusion (p := p)) I.f x)
          (fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            associated_groupoid_cover_forget_component_comm
              (J := J) (p := p) S x (q := q)
              (I₁ := I₁) (I₂ := I₂)
              (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)))
      (fun φ ↦ by
        -- Naturality is exactly the vertical naturality of the pullback-comparison components.
        apply Pseudofunctor.DescentData.hom_ext
        intro I
        rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
        simpa only [Functor.comp_map, associated_groupoid_cover_forget_descent_data] using
            associated_groupoid_pullbackComparison_naturality_over_vertical
              (p := p) (f := I.f) (φ := φ))
  -- The target orientation compares the forgotten associated descent functor to the ambient one.
  η.symm

/-- Helper for Lemma 8.5.3: the `hom_inv_id` law of an ambient isomorphism of forgotten
associated descent data is already visible on each fixed cover component. -/
private theorem associated_groupoid_cover_iso_component_hom_inv_id
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    e.hom.hom I ≫ e.inv.hom I =
      𝟙 (((associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D).obj I) := by
  -- Read `e.hom ≫ e.inv = 𝟙` on the `I`-th component of the descent-data isomorphism.
  rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id]
  rfl

/-- Helper for Lemma 8.5.3: the `inv_hom_id` law of an ambient isomorphism of forgotten
associated descent data is already visible on each fixed cover component. -/
private theorem associated_groupoid_cover_iso_component_inv_hom_id
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    e.inv.hom I ≫ e.hom.hom I =
      𝟙 (((associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E).obj I) := by
  -- Read `e.inv ≫ e.hom = 𝟙` on the same component.
  rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id]
  rfl

/-- Helper for Lemma 8.5.3: the `I`-th component of an ambient isomorphism of forgotten
associated descent data is itself an isomorphism in the ambient fiber over `I.Y`. -/
noncomputable def associated_groupoid_cover_iso_component
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    (((associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D).obj I) ≅
      (((associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E).obj I) :=
  { hom := e.hom.hom I
    inv := e.inv.hom I
    hom_inv_id := associated_groupoid_cover_iso_component_hom_inv_id
      (J := J) (p := p) S e I
    inv_hom_id := associated_groupoid_cover_iso_component_inv_hom_id
      (J := J) (p := p) S e I }

/-- Helper for Lemma 8.5.3: lifting the hom and inverse of one ambient component isomorphism back
to the associated-groupoid fiber still satisfies `hom_inv_id`. -/
private theorem associated_groupoid_cover_iso_lift_component_hom_inv_id
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    associated_groupoid_fiber_hom_of_isIso (p := p)
        ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).hom) ≫
      associated_groupoid_fiber_hom_of_isIso (p := p)
        ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).inv) =
      𝟙 _ := by
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y
  letI : F.Faithful := associated_groupoid_inclusion_fiberFunctor_faithful (p := p) I.Y
  -- Forget the lifted composite back to the ambient fiber, where it is the componentwise
  -- `hom_inv_id` law of the original ambient descent-data isomorphism.
  apply F.map_injective
  simpa only [F, Functor.map_comp] using
    associated_groupoid_cover_iso_component_hom_inv_id
      (J := J) (p := p) S e I

/-- Helper for Lemma 8.5.3: lifting the inverse and hom of one ambient component isomorphism back
to the associated-groupoid fiber still satisfies `inv_hom_id`. -/
private theorem associated_groupoid_cover_iso_lift_component_inv_hom_id
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    associated_groupoid_fiber_hom_of_isIso (p := p)
        ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).inv) ≫
      associated_groupoid_fiber_hom_of_isIso (p := p)
        ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).hom) =
      𝟙 _ := by
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y
  letI : F.Faithful := associated_groupoid_inclusion_fiberFunctor_faithful (p := p) I.Y
  -- The inverse law is proved in the same way: forget to the ambient fiber and read off the
  -- componentwise `inv_hom_id` of the original ambient isomorphism.
  apply F.map_injective
  simpa only [F, Functor.map_comp] using
    associated_groupoid_cover_iso_component_inv_hom_id
      (J := J) (p := p) S e I

/-- Helper for Lemma 8.5.3: each ambient component isomorphism of forgotten descent data lifts to
an isomorphism between the corresponding associated-groupoid fiber components. -/
private noncomputable def associated_groupoid_cover_iso_lift_component
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    (I : S.Arrow) :
    D.obj I ≅ E.obj I :=
  { hom := associated_groupoid_fiber_hom_of_isIso (p := p)
      ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).hom)
    inv := associated_groupoid_fiber_hom_of_isIso (p := p)
      ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I).inv)
    hom_inv_id := associated_groupoid_cover_iso_lift_component_hom_inv_id
      (J := J) (p := p) S e I
    inv_hom_id := associated_groupoid_cover_iso_lift_component_inv_hom_id
      (J := J) (p := p) S e I }

/-- Helper for Lemma 8.5.3: after forgetting to the ambient fibers, the lifted component family
for an ambient descent-data isomorphism satisfies the same commutativity square. -/
private theorem associated_groupoid_cover_forget_iso_lift_component_comm
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₁.op.toLoc).toFunctor.map
        (associated_groupoid_cover_iso_lift_component
          (J := J) (p := p) S e I₁).hom) ≫
      E.hom q f₁ f₂ hf₁ hf₂ =
        D.hom q f₁ f₂ hf₁ hf₂ ≫
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₂.op.toLoc).toFunctor.map
            (associated_groupoid_cover_iso_lift_component
              (J := J) (p := p) S e I₂).hom) := by
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₁.op.toLoc).toFunctor.map
        (associated_groupoid_cover_iso_lift_component
          (J := J) (p := p) S e I₁).hom)
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₂.op.toLoc).toFunctor.map
        (associated_groupoid_cover_iso_lift_component
          (J := J) (p := p) S e I₂).hom)
  let α₁ :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I₁).hom)
  let α₂ :=
    ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
      ((associated_groupoid_cover_iso_component (J := J) (p := p) S e I₂).hom)
  let e₁D := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₁ (D.obj I₁)
  let e₁E := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₁ (E.obj I₁)
  let e₂D := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₂ (D.obj I₂)
  let e₂E := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₂ (E.obj I₂)
  let dD := D.hom q f₁ f₂ hf₁ hf₂
  let dE := E.hom q f₁ f₂ hf₁ hf₂
  letI : F.Faithful := associated_groupoid_inclusion_fiberFunctor_faithful (p := p) Y
  have hforget₁ :
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₁.Y).map
          (associated_groupoid_cover_iso_lift_component
            (J := J) (p := p) S e I₁).hom =
        (associated_groupoid_cover_iso_component (J := J) (p := p) S e I₁).hom := by
    -- Forgeting a lifted ambient component just removes the strongly-cartesian witness.
    simpa only [associated_groupoid_cover_iso_lift_component] using
      associated_groupoid_fiber_hom_of_isIso_forget (p := p)
        (φ := (associated_groupoid_cover_iso_component (J := J) (p := p) S e I₁).hom)
  have hforget₂ :
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₂.Y).map
          (associated_groupoid_cover_iso_lift_component
            (J := J) (p := p) S e I₂).hom =
        (associated_groupoid_cover_iso_component (J := J) (p := p) S e I₂).hom := by
    -- The same forgetting step identifies the second lifted component with the ambient one.
    simpa only [associated_groupoid_cover_iso_lift_component] using
      associated_groupoid_fiber_hom_of_isIso_forget (p := p)
        (φ := (associated_groupoid_cover_iso_component (J := J) (p := p) S e I₂).hom)
  have hleft :
      α₁ ≫ e₁E.hom = e₁D.hom ≫ β₁ := by
    -- Route correction: first transport the left comparison shell across the lifted component,
    -- then rewrite the forgotten lift to the ambient component morphism.
    simpa only [α₁, β₁, e₁D, e₁E, hforget₁] using
      associated_groupoid_pullbackComparison_naturality_over_vertical
        (p := p) (f := f₁)
        (φ := (associated_groupoid_cover_iso_lift_component
          (J := J) (p := p) S e I₁).hom)
  have hright :
      β₂ ≫ e₂E.inv = e₂D.inv ≫ α₂ := by
    -- Transport the right comparison inverse across the lifted component in the same way.
    simpa only [α₂, β₂, e₂D, e₂E, hforget₂] using
      associated_groupoid_pullbackComparison_inv_naturality_over_vertical
        (p := p) (f := f₂)
        (φ := (associated_groupoid_cover_iso_lift_component
          (J := J) (p := p) S e I₂).hom)
  have hcomm :
      α₁ ≫ associated_groupoid_cover_forget_hom (J := J) (p := p) S E q f₁ f₂ hf₁ hf₂ =
        associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    -- Once the comparison shells are in ambient form, the square is exactly the commutativity of
    -- the ambient descent-data isomorphism `e`.
    simpa only [associated_groupoid_cover_iso_component] using
      e.hom.comm q f₁ f₂ hf₁ hf₂
  have hnormalize_left :
      α₁ ≫ associated_groupoid_cover_forget_hom (J := J) (p := p) S E q f₁ f₂ hf₁ hf₂ =
        (α₁ ≫ e₁E.hom) ≫ F.map dE ≫ e₂E.inv := by
    -- Expand the forgotten associated overlap only once, keeping the source route in the ambient
    -- owner shell.
    change α₁ ≫ (e₁E.hom ≫ F.map dE ≫ e₂E.inv) =
      (α₁ ≫ e₁E.hom) ≫ F.map dE ≫ e₂E.inv
    simp only [Category.assoc]
  have hleft' :
      (α₁ ≫ e₁E.hom) ≫ F.map dE ≫ e₂E.inv =
        (e₁D.hom ≫ β₁) ≫ F.map dE ≫ e₂E.inv := by
    exact congrArg (fun k ↦ k ≫ F.map dE ≫ e₂E.inv) hleft
  have hassoc_left :
      (e₁D.hom ≫ β₁) ≫ F.map dE ≫ e₂E.inv =
        e₁D.hom ≫ (β₁ ≫ F.map dE) ≫ e₂E.inv := by
    simp only [Category.assoc]
  have hnormalize_right :
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫ α₂ =
        e₁D.hom ≫ F.map dD ≫ (e₂D.inv ≫ α₂) := by
    -- Expand the forgotten source overlap symmetrically on the right-hand side.
    change (e₁D.hom ≫ F.map dD ≫ e₂D.inv) ≫ α₂ =
      e₁D.hom ≫ F.map dD ≫ (e₂D.inv ≫ α₂)
    simp only [Category.assoc]
  have hcore :
      e₁D.hom ≫ (β₁ ≫ F.map dE) ≫ e₂E.inv =
        e₁D.hom ≫ F.map dD ≫ (e₂D.inv ≫ α₂) := by
    exact
      (hnormalize_left.trans (hleft'.trans hassoc_left)).symm.trans
        (hcomm.trans hnormalize_right)
  have hright' :
      e₁D.hom ≫ F.map dD ≫ (e₂D.inv ≫ α₂) =
        e₁D.hom ≫ F.map dD ≫ (β₂ ≫ e₂E.inv) := by
    exact congrArg (fun k ↦ e₁D.hom ≫ F.map dD ≫ k) hright.symm
  have hconj :
      (e₁D.hom ≫ β₁ ≫ F.map dE) ≫ e₂E.inv =
        (e₁D.hom ≫ F.map dD ≫ β₂) ≫ e₂E.inv := by
    exact (by simpa only [Category.assoc] using hcore.trans hright')
  have hcancel_right :
      e₁D.hom ≫ β₁ ≫ F.map dE = e₁D.hom ≫ F.map dD ≫ β₂ := by
    exact (cancel_mono e₂E.inv).1 hconj
  have hcancel_left :
      β₁ ≫ F.map dE = F.map dD ≫ β₂ := by
    exact (cancel_epi e₁D.hom).1 (by simpa only [Category.assoc] using hcancel_right)
  -- Forget the candidate associated square to the ambient fiber, prove it there by canceling the
  -- comparison shells, and then reflect the equality back through faithfulness.
  apply F.map_injective
  simpa only [β₁, β₂, dD, dE, Functor.map_comp] using hcancel_left

/-- Helper for Lemma 8.5.3: an ambient isomorphism between forgotten associated descent data lifts
componentwise back to an isomorphism in the associated descent-data category. -/
noncomputable def associated_groupoid_cover_forget_iso_lift
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (e :
      (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj D ≅
        (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).obj E) :
    D ≅ E :=
  -- Package the lifted ambient component isomorphisms directly by `isoMk`; the only nontrivial
  -- content is the fixed-cover commutativity square proved immediately above.
  Pseudofunctor.DescentData.isoMk
    (fun I ↦ associated_groupoid_cover_iso_lift_component
      (J := J) (p := p) S e I)
    (fun _Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
      associated_groupoid_cover_forget_iso_lift_component_comm
        (J := J) (p := p) S e (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂))

/-- Helper for Lemma 8.5.3: the ambient stack hypothesis already supplies the fixed-cover
equivalence for the canonical descent functor of `p`. -/
theorem ambient_cover_toDescentData_isEquivalence
    [IsStackOnSite J p] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  -- This is exactly the coverwise form of the ambient stack condition from Lemma `8.4.2`.
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p).1
      inferInstance U S

/-- Helper for Lemma 8.5.3: the fixed-cover canonical descent functor for the associated
groupoid projection. -/
noncomputable abbrev associated_groupoid_cover_descent_functor
    [p.IsFibered] {U : C} (S : J.Cover U) :=
  (canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
    (fun I : S.Arrow ↦ I.f)

/-- Helper for Lemma 8.5.3: the fixed-cover canonical descent functor for the ambient fibred
category. -/
noncomputable abbrev ambient_cover_descent_functor
    [p.IsFibered] {U : C} (S : J.Cover U) :=
  (canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)

/-- Helper for Lemma 8.5.3: forgetting the strongly-cartesian witness on fixed-cover descent data
is faithful because it is fiberwise faithful on each component. -/
theorem associated_groupoid_cover_forget_descent_data_faithful
    [p.IsFibered] {U : C} (S : J.Cover U) :
    (associated_groupoid_cover_forget_descent_data (J := J) (p := p) S).Faithful := by
  refine ⟨fun {_ _} φ ψ hφψ ↦ ?_⟩
  -- Descent-data morphisms are determined componentwise, and each component forgetful functor on
  -- fibers only removes the wide-subcategory proof.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I.Y
  letI : F.Faithful := associated_groupoid_inclusion_fiberFunctor_faithful (p := p) I.Y
  exact F.map_injective (congrArg (fun η ↦ η.hom I) hφψ)

/-- Helper for Lemma 8.5.3: the ambient fixed-cover descent functor maps the reflected
`preimageIso` back to the chosen ambient comparison isomorphism. -/
theorem ambient_cover_preimageIso_hom_map
    [IsStackOnSite J p] {U : C} (S : J.Cover U)
    [(ambient_cover_descent_functor (J := J) (p := p) S).Full]
    [(ambient_cover_descent_functor (J := J) (p := p) S).Faithful]
    {x y : p.Fiber U}
    (e :
      (ambient_cover_descent_functor (J := J) (p := p) S).obj x ≅
        (ambient_cover_descent_functor (J := J) (p := p) S).obj y) :
    (ambient_cover_descent_functor (J := J) (p := p) S).map
        ((Functor.FullyFaithful.ofFullyFaithful
          (ambient_cover_descent_functor (J := J) (p := p) S)).preimageIso e).hom = e.hom := by
  let Famb := ambient_cover_descent_functor (J := J) (p := p) S
  simpa using
    (Functor.FullyFaithful.ofFullyFaithful Famb).map_preimage e.hom

end

end CategoryTheory
