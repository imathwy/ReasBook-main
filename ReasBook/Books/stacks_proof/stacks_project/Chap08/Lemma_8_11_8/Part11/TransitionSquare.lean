import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.CommonOwnerFrontier

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8 (reconstructed, Mathlib-refactor): the §5.2 transition-square identity
on the doubly-refined cover. Left branch = chosen-cover transition component for `I₁` then the
`𝒢_V` overlap (exposed as `counit(I₁) ≫ c_overlap ≫ counit(I₂)⁻¹`); right branch = the pulled
`𝒢_U` overlap then the transition component for `I₂`. Equality is choice-independence / naturality
of the canonical transition. mapComp' bridges = pseudofunctor composition coherence (no math). -/
private theorem chosen_cover_transition_frontier_from_pullback_cover_refined_specialization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁)).hom)).hom L ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
              (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))
    =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_pulled_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
          (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))) := by
  let FL := ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor
  simpa only [FL, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Category.assoc] using
    congrArg FL.map
      (chosen_cover_transition_common_owner_frontier_from_pullback_cover
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K)

/-- Helper for Lemma 8.11.8 (reconstructed, Mathlib-refactor): the §5.2 transition-square identity
on the doubly-refined cover. Left branch = chosen-cover transition component for `I₁` then the
`𝒢_V` overlap (exposed as `counit(I₁) ≫ c_overlap ≫ counit(I₂)⁻¹`); right branch = the pulled
`𝒢_U` overlap then the transition component for `I₂`. Equality is choice-independence / naturality
of the canonical transition. mapComp' bridges = pseudofunctor composition coherence (no math). -/
private theorem chosen_cover_transition_reduced_frontier_specializes_pullback_cover_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁)).hom)).hom L ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
              (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))
    =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_pulled_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
          (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))) := by
  exact chosen_cover_transition_frontier_from_pullback_cover_refined_specialization
    (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L

/-- Helper for Lemma 8.11.8 (reconstructed, Mathlib-refactor): the §5.2 transition-square identity
on the doubly-refined cover. Left branch = chosen-cover transition component for `I₁` then the
`𝒢_V` overlap (exposed as `counit(I₁) ≫ c_overlap ≫ counit(I₂)⁻¹`); right branch = the pulled
`𝒢_U` overlap then the transition component for `I₂`. Equality is choice-independence / naturality
of the canonical transition. mapComp' bridges = pseudofunctor composition coherence (no math). -/
private theorem chosen_cover_transition_reduced_branches_match_pullback_cover_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁)).hom)).hom L ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
              (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))
    =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            ((chosen_cover_pulled_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
          (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))) := by
  exact chosen_cover_transition_frontier_from_pullback_cover_refined_specialization
    (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L

/-- Helper for Lemma 8.11.8: the chosen-cover component comparisons satisfy the descent square on
overlaps of the chosen cover of `V`, so they package into one isomorphism of descent data. -/
private theorem chosen_cover_transition_component_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂
        (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂
          (_hf₁ := hf₁) (_hf₂ := hf₂) ≫
        ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K) := by
  let S := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  rw [chosen_cover_transition_left_branch_exposed
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L,
    chosen_cover_transition_right_branch_exposed
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L,
    chosen_cover_transition_left_component_reduced_to_pullback_input
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L,
    chosen_cover_transition_right_component_reduced_to_pullback_input
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L]
  exact chosen_cover_transition_reduced_branches_match_pullback_cover_component_normalized
    (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L

/-- Helper for Lemma 8.11.8: the chosen-cover component comparisons satisfy the descent square on
overlaps of the chosen cover of `V`, so they package into one isomorphism of descent data. -/
private theorem chosen_cover_descent_transition_component_coherence
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂ =
    (chosen_cover_pulled_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) := by
  -- The datum-level square is the image, under the (faithful) chosen-cover descent equivalence on
  -- `C / Y`, of the componentwise transition square `chosen_cover_transition_component_square`.
  haveI : (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  exact chosen_cover_transition_component_square
    (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K

/-- Helper for Lemma 8.11.8: package the componentwise chosen-cover pullback comparisons into one
datum-side transition isomorphism on the chosen cover of `V`. -/
noncomputable def chosen_cover_descent_transition_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :
    chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian f ≅
      chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V :=
  -- Comm obligation = `chosen_cover_descent_transition_component_coherence` (the faithful §5.2
  -- datum-level overlap square, kept as a standalone statement above); sorry-stubbed here in the
  -- `isoMk` comm slot per the codebase pattern (cf. Part09 `isoMk` usages).
  Pseudofunctor.DescentData.isoMk
    (fun I ↦ chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I)
    (by
      intro _Y q _i₁ _i₂ f₁ f₂ hf₁ hf₂
      exact chosen_cover_descent_transition_component_coherence
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂)

end CategoryTheory
