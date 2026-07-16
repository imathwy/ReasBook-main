import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part03
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.FiberPullbackComp

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Helper for Lemma 8.11.8: over one common owner above `K.Y`, the two pairwise common-owner
conjugations compose to the direct conjugation induced by the pulled `(f₁,f₃)` local
isomorphism. This is the source-level invariant behind the triple-overlap cocycle. -/
private theorem secondary_cover_pairwise_common_owner_conjugation_comp
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₃).Arrow)
    {Z : C} (q : Z ⟶ K.Y)
    {K₁₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS
      (K.f ≫ f₁) (K.f ≫ f₂)).Arrow}
    {K₂₃ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS
      (K.f ≫ f₂) (K.f ≫ f₃)).Arrow}
    (g₁₂ : Z ⟶ K₁₂.Y) (g₂₃ : Z ⟶ K₂₃.Y)
    (hg₁₂ : g₁₂ ≫ K₁₂.f = q := by cat_disch)
    (hg₂₃ : g₂₃ ≫ K₂₃.f = q := by cat_disch) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₁) (K.f ≫ f₂) q g₁₂ hg₁₂).hom ≪≫
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₂) (K.f ≫ f₃) q g₂₃ hg₂₃).hom =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).mapIso
          ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₁ (xS I₁) ≪≫
            local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₃ K ≪≫
            ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃ (xS I₃)).symm)).hom) := by
  rw [← automorphismUnderlyingSheafConj_comp]
  exact automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _
/-- Helper for Lemma 8.11.8: the previous common-owner composition fact is also available on the
underlying sheaf morphisms, which is the form needed in the blocked descent comparison. -/
private theorem secondary_cover_pairwise_common_owner_conjugation_comp_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₃).Arrow)
    {Z : C} (q : Z ⟶ K.Y)
    {K₁₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS
      (K.f ≫ f₁) (K.f ≫ f₂)).Arrow}
    {K₂₃ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS
      (K.f ≫ f₂) (K.f ≫ f₃)).Arrow}
    (g₁₂ : Z ⟶ K₁₂.Y) (g₂₃ : Z ⟶ K₂₃.Y)
    (hg₁₂ : g₁₂ ≫ K₁₂.f = q := by cat_disch)
    (hg₂₃ : g₂₃ ≫ K₂₃.f = q := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₁) (K.f ≫ f₂) q g₁₂ hg₁₂).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₂) (K.f ≫ f₃) q g₂₃ hg₂₃).hom).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).mapIso
          ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₁ (xS I₁) ≪≫
            local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₃ K ≪≫
            ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃ (xS I₃)).symm)).hom)).hom := by
  exact congrArg Iso.hom
    (secondary_cover_pairwise_common_owner_conjugation_comp (𝒮 := 𝒮) hGerbe hAbelian
      S xS f₁ f₂ f₃ K q g₁₂ g₂₃ hg₁₂ hg₂₃)
end

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
theorem chosen_cover_overlap_map_eq_pulled_overlap
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    ((((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂
          (_hf₁ := hf₁) (_hf₂ := hf₂))) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))) =
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂) := by
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂))).functor
  exact (chosen_cover_overlap_map_to_secondary_cover_descent
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ K).trans
    (automorphism_overlap_hom_characterization
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by simp [Category.assoc, hf₁])
      (by simp [Category.assoc, hf₂])).symm
section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
private theorem chosen_cover_pairwise_common_owner_conjugation_comp_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    {Z : C} (qZ : Z ⟶ K.Y)
    {K₁₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow}
    {K₂₃ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow}
    (g₁₂ : Z ⟶ K₁₂.Y) (g₂₃ : Z ⟶ K₂₃.Y)
    (hg₁₂ : g₁₂ ≫ K₁₂.f = qZ := by cat_disch)
    (hg₂₃ : g₂₃ ≫ K₂₃.f = qZ := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂) qZ g₁₂ hg₁₂).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) qZ g₂₃ hg₂₃).hom).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qZ).mapIso
          ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₁
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁) ≪≫
            local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K ≪≫
            ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)).symm)).hom)).hom := by
  refine congrArg Iso.hom
    ((automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂) qZ g₁₂ hg₁₂).hom
        (local_overlap_common_owner_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) qZ g₂₃ hg₂₃).hom).symm.trans
      (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _))
/-- Helper for Lemma 8.11.8: after choosing a common owner over one section object, the pulled
chosen-cover common-owner cocycle can also be evaluated pointwise on that section. This is the
app-level target that remains once the two pulled overlap branches are rewritten to common-owner
conjugations. -/
theorem chosen_cover_pairwise_common_owner_conjugation_comp_hom_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    {Z : C} (qZ : Z ⟶ K.Y)
    {K₁₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow}
    {K₂₃ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow}
    (g₁₂ : Z ⟶ K₁₂.Y) (g₂₃ : Z ⟶ K₂₃.Y)
    (hg₁₂ : g₁₂ ≫ K₁₂.f = qZ := by cat_disch)
    (hg₂₃ : g₂₃ ≫ K₂₃.f = qZ := by cat_disch)
    (R : (Over Z)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (qZ ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁)))).1.obj R) :
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qZ g₁₂ hg₁₂).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) qZ g₂₃ hg₂₃).hom).hom).1.app R) α =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qZ).mapIso
            ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₁
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁) ≪≫
              local_overlap_isomorphism
                (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K ≪≫
              ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)).symm)).hom)).hom).1.app
        R) α := by
  exact congrFun
    (congrArg (fun φ ↦ φ.1.app R)
      (chosen_cover_pairwise_common_owner_conjugation_comp_hom (𝒮 := 𝒮) hGerbe hAbelian
        q f₁ f₂ f₃ K qZ g₁₂ g₂₃ hg₁₂ hg₂₃))
    α

end
/-- Helper for Lemma 8.11.8: a covering family in the slice site detects equality of sections of
one fixed slice sheaf. This packages the separatedness step so the remaining blocker can stay at
the source-faithful common-refinement level. -/
theorem sections_eq_of_cover_on_slice
    {U : C} (ℱ : Sheaf (J.over U) (Type (max u v)))
    (T : Over U) (R : (J.over U).Cover T)
    (s s' : ℱ.1.obj (op T))
    (hss : ∀ I : R.Arrow, ℱ.1.map I.f.op s = ℱ.1.map I.f.op s') :
    s = s' := by
  -- Use separatedness of `ℱ` on the chosen cover of `T` in the slice site.
  apply (((isSheaf_iff_isSheaf_of_type (J.over U) ℱ.1).1 ℱ.property).isSeparated _ R.2).ext
  intro Y f hf
  exact hss ⟨Y, f, hf⟩

/-- Helper for Lemma 8.11.8: a slice cover also detects equality of two section maps on one
fixed owner object. After fixing the input section, separatedness of the target sheaf reduces the
comparison to equality after restriction to each member of the cover. -/
theorem section_map_eq_of_cover_on_slice
    {U : C} {ℱ 𝒢 : Sheaf (J.over U) (Type (max u v))}
    (T : (Over U)ᵒᵖ) (R : (J.over U).Cover T.unop)
    (f g : ℱ.1.obj T → 𝒢.1.obj T)
    (hfg : ∀ I : R.Arrow, ∀ α : ℱ.1.obj T,
      𝒢.1.map I.f.op (f α) = 𝒢.1.map I.f.op (g α)) :
    f = g := by
  -- First freeze one input section so the remaining comparison is between two output sections.
  funext α
  -- Then separatedness of the target sheaf descends the equality from the slice cover `R`.
  exact sections_eq_of_cover_on_slice (J := J) 𝒢 T.unop R (f α) (g α) (fun I ↦ hfg I α)

/-- Helper for Lemma 8.11.8: the base-site common refinement of the two pairwise overlap covers
over one owner object `T` above the `(f₁,f₃)` overlap. -/
noncomputable abbrev chosen_cover_overlap_common_refinement_base_cover
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ) :
    J.Cover T.unop.left :=
  let qT := T.unop.hom
  let S12 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)
  let S23 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)
  (S12.pullback qT).bind fun A ↦ S23.pullback A.base.f

/-- Helper for Lemma 8.11.8: pulling back the two pairwise overlap covers along
`qT := T.unop.hom` and binding them produces the source-faithful common refinement on the base
site, and `Sieve.overEquiv` turns it into a cover of `T.unop` in the slice site. -/
theorem chosen_cover_overlap_common_refinement_cover_on_slice
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ) :
    ∃ B : J.Cover T.unop.left,
      ∃ R : (J.over K.Y).Cover T.unop,
        (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left) := by
  let B : J.Cover T.unop.left :=
    chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T
  let R : (J.over K.Y).Cover T.unop :=
    ⟨(Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left),
      J.overEquiv_symm_mem_over T.unop (B : Sieve T.unop.left) B.condition⟩
  -- The slice cover is exactly the image of the base-site common refinement under `overEquiv`.
  exact ⟨B, R, rfl⟩

/-- Helper for Lemma 8.11.8: every arrow in the slice-site common refinement cover comes from the
corresponding arrow in the base-site common refinement, with the same underlying `left` map. -/
theorem chosen_cover_overlap_common_refinement_base_arrow
    {X : C} {T : Over X} {B : J.Cover T.left} {R : (J.over X).Cover T}
    (hR : (R : Sieve T) = (Sieve.overEquiv T).symm (B : Sieve T.left))
    (I : R.Arrow) :
    (B : Sieve T.left) I.f.left := by
  have hIf : ((Sieve.overEquiv T).symm (B : Sieve T.left)) I.f := by
    simpa [hR] using I.hf
  -- `Sieve.overEquiv_symm_iff` removes the slice transport and recovers the base-cover member.
  exact (Sieve.overEquiv_symm_iff (B : Sieve T.left) I.f).1 hIf

/-- Helper for Lemma 8.11.8: the canonical base-cover arrow lying under a slice-cover arrow in
the common refinement. Keeping this as a definition makes its underlying map definitionally equal
to `I.f.left`, avoiding dependent equality casts for `Cover.Arrow.f`. -/
noncomputable abbrev chosen_cover_overlap_common_refinement_lift_arrow
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hI :
      ((chosen_cover_overlap_common_refinement_base_cover
        (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
          Sieve T.unop.left) I.f.left) :
    (chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T).Arrow :=
  { Y := I.Y.left
    f := I.f.left
    hf := hI }

/-- Helper for Lemma 8.11.8: app-level form of endpoint-independence for common-owner
conjugation maps. -/
theorem local_overlap_common_owner_conjugation_eq_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁))).1.obj T) :
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom).hom).1.app T) α =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom).hom).1.app T) α := by
  simpa using
    congrFun
      (congrArg (fun ψ ↦ (ψ.hom.1.app T))
        (local_overlap_common_owner_conjugation_eq
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂))
      α

/-- Helper for Lemma 8.11.8: evaluating a sheaf morphism after restricting a section along a
slice arrow is the same as first restricting the section and then evaluating the morphism at the
smaller object. This isolates the outer naturality shell in the refinement-member proof. -/
theorem sheaf_hom_app_restrict_eq
    {U : C} {ℱ 𝒢 : Sheaf (J.over U) (Type (max u v))}
    (φ : ℱ ⟶ 𝒢) {T T' : Over U} (i : T' ⟶ T)
    (α : ℱ.1.obj (op T)) :
    𝒢.1.map i.op (((φ.1.app (op T)) α)) =
      ((φ.1.app (op T')) (ℱ.1.map i.op α)) := by
  -- This is exactly naturality of the underlying presheaf map, evaluated on the fixed section.
  simpa using (congrFun (φ.1.naturality i.op) α).symm

/-- Helper for Lemma 8.11.8: if the owner arrow of an object in one slice composes to `h`, then
its image under the corresponding `Over.map` is literally the object `Over.mk h` in the larger
slice. This is the object-level transport that remains after the outer naturality rewrite. -/
theorem over_map_obj_mk_eq
    {Y Z : C} (f : Y ⟶ Z) {W : C} (g : W ⟶ Y) (h : W ⟶ Z)
    (hg : g ≫ f = h) :
    (Over.map f).obj (Over.mk g) = Over.mk h := by
  -- Reduce to the definitional case where the composed owner arrow is exactly `h`.
  cases hg
  rfl

/-- Helper for Lemma 8.11.8: the previous `Over.map` owner-object identification can be moved to
the opposite slice object used by `.app` on a presheaf. This keeps the transport step explicit
without reopening any descent-data internals. -/
theorem over_map_obj_mk_eq_op
    {Y Z : C} (f : Y ⟶ Z) {W : C} (g : W ⟶ Y) (h : W ⟶ Z)
    (hg : g ≫ f = h) :
    op ((Over.map f).obj (Over.mk g)) = op (Over.mk h) := by
  -- Move the owner-object equality across `Opposite.op`, which is the object shell used by `.app`.
  exact congrArg Opposite.op (over_map_obj_mk_eq f g h hg)

/-- Helper for Lemma 8.11.8: once the `Over.map` image object is identified with its owner
`Over.mk h`, the induced section cast is exactly the presheaf action of the corresponding
opposite-side `eqToHom`. This isolates the cast normalization needed in the refinement-member
transport step. -/
theorem over_map_obj_mk_section_cast_eq_map
    {Y : C} {P : (Over Y)ᵒᵖ ⥤ Type (max u v)}
    {X Z : C} (f : X ⟶ Y) (g : Z ⟶ X) (h : Z ⟶ Y)
    (hg : g ≫ f = h) (s : P.obj (op ((Over.map f).obj (Over.mk g)))) :
    Eq.mp (congrArg P.obj (over_map_obj_mk_eq_op f g h hg)) s =
      P.map (eqToHom (over_map_obj_mk_eq_op f g h hg)) s := by
  -- This is exactly the generic opposite-side cast normalization already isolated above.
  rw [local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op]

/-- Helper for Lemma 8.11.8: on one owner arrow `k`, the pullback pseudofunctor evaluates a
mapped sheaf morphism by evaluating the original morphism on the corresponding image object in the
larger slice. This exposes the literal `.app` shell before any owner-object transport is applied.
-/
theorem pseudofunctor_over_map_app_eq_image_app
    {X Y Z : C} (g : X ⟶ Y)
    {ℱ 𝒢 : Sheaf (J.over Y) (Type (max u v))} (φ : ℱ ⟶ 𝒢) (k : Z ⟶ X) :
    ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map φ).1.app
        (op (Over.mk k))) =
      (φ.1.app (op ((Over.map g).obj (Over.mk k)))) := by
  -- `pseudofunctorOver` is built from `overMapPullback`, so the component is definitionally the
  -- original sheaf map on the image object of `Over.map g`.
  rfl

/-- Helper for Lemma 8.11.8: evaluating the pullback of a sheaf morphism at `op (Over.mk k)` can
be rewritten as evaluation of the original morphism on the owner object `op (Over.mk h)` once the
composed owner arrow is normalized by `hk : k ≫ g = h`. This is the generic transport shell still
blocking the refinement-member comparison. -/
theorem pseudofunctor_over_map_app_eq_owner_transport
    {X Y Z : C} (g : X ⟶ Y)
    {ℱ 𝒢 : Sheaf (J.over Y) (Type (max u v))} (φ : ℱ ⟶ 𝒢)
    (k : Z ⟶ X) (h : Z ⟶ Y) (hk : k ≫ g = h)
    (s :
      ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj ℱ).1.obj
        (op (Over.mk k)))) :
    ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map φ).1.app
        (op (Over.mk k))) s =
      (congrArg 𝒢.1.obj (over_map_obj_mk_eq_op g k h hk)).mpr
        ((φ.1.app (op (Over.mk h)))
          (Eq.mp (congrArg ℱ.1.obj (over_map_obj_mk_eq_op g k h hk)) s)) := by
  cases hk
  rfl
/-- Helper for Lemma 8.11.8: on one refinement member `I`, the first pulled overlap branch is
already presented on the owner object `op (Over.mk Ī.toMiddleHom)` where the existing
secondary-cover common-owner comparison theorem applies literally. -/
private theorem chosen_cover_refinement_member_first_branch_eq_common_owner_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base;
    -- Source/target base-change bridges: after the refactor the pulled overlap branch lands in
    -- the iterated pulled sheaf, while the common-owner conjugation lands in the
    -- `autoSheaf` of the iterated fiber pullback; these are no longer defeq, so we mediate both
    -- the input (`bIso`) and output (`cIso`) sides by `automorphismUnderlyingSheafBaseChangeIso`.
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₁)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁₂.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁));
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁₂.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂));
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)))).1.obj
        (op (Over.mk Ī.toMiddleHom))),
    (((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁])
            (by simpa [Category.assoc, _hf₂]))).1.app
        (op (Over.mk Ī.toMiddleHom))) s) =
      (cIso.inv.1.app (op (Over.mk Ī.toMiddleHom))
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
          (op (Over.mk Ī.toMiddleHom)))
        (bIso.hom.1.app (op (Over.mk Ī.toMiddleHom)) s))) := by
  intro Ī K₁₂ bIso cIso s
  -- Bridge the chosen-cover conjugation iso with the self-leg common-owner conjugation: both are
  -- conjugations of parallel isomorphisms between the same pulled fiber objects.
  have hconj :
      (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂) K₁₂).hom =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom :=
    congrArg Iso.hom
      (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _)
  -- Sheaf-level identity: the mapped overlap morphism is the source owner-component iso, followed
  -- by the chosen-cover conjugation, followed by the inverse target owner-component iso.
  have hM0 :
      ((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁]) (by simpa [Category.assoc, _hf₂])) =
        bIso.hom ≫
          (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂).hom ≫
          cIso.inv := by
    rw [automorphism_overlap_hom_secondary_cover_component (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)]
    rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit (𝒮 := 𝒮) hGerbe
      hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂) K₁₂]
    dsimp only [bIso, cIso]
    simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
    rfl
  -- Replace the chosen-cover conjugation by the self-leg common-owner conjugation (parallel).
  have hM := hM0.trans
    (congrArg (fun m ↦ bIso.hom ≫ m ≫ cIso.inv) hconj)
  -- Evaluate the sheaf identity at the owner object and the fixed section.
  have happ := congrFun
    (congrArg (fun φ ↦ φ.1.app (op (Over.mk Ī.toMiddleHom))) hM) s
  simpa using happ

/-- Helper for Lemma 8.11.8: on the same refinement member `I`, the second pulled overlap branch
is already presented on the owner object `op (Over.mk (𝟙 I.Y.left))`, isolating the identity-leg
common-owner shell needed for the remaining memberwise cocycle calculation. -/
private theorem chosen_cover_refinement_member_second_branch_eq_common_owner_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base;
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂₃.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂));
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₃)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂₃.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₃));
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂])
            (by simpa [Category.assoc, _hf₃]))).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s) =
      (cIso.inv.1.app (op (Over.mk (𝟙 I.Y.left)))
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        (bIso.hom.1.app (op (Over.mk (𝟙 I.Y.left))) s))) := by
  intro Ī K₂₃ bIso cIso s
  -- Bridge the chosen-cover conjugation iso with the self-leg common-owner conjugation: both are
  -- conjugations of parallel isomorphisms between the same pulled fiber objects.
  have hconj :
      (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) K₂₃).hom =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom :=
    congrArg Iso.hom
      (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _)
  -- Sheaf-level identity: the mapped overlap morphism is the source owner-component iso, followed
  -- by the chosen-cover conjugation, followed by the inverse target owner-component iso.
  have hM0 :
      ((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃])) =
        bIso.hom ≫
          (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃).hom ≫
          cIso.inv := by
    rw [automorphism_overlap_hom_secondary_cover_component (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)]
    rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit (𝒮 := 𝒮) hGerbe
      hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃) K₂₃]
    dsimp only [bIso, cIso]
    simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
    rfl
  -- Replace the chosen-cover conjugation by the self-leg common-owner conjugation (parallel).
  have hM := hM0.trans
    (congrArg (fun m ↦ bIso.hom ≫ m ≫ cIso.inv) hconj)
  -- Evaluate the sheaf identity at the owner object and the fixed section.
  have happ := congrFun
    (congrArg (fun φ ↦ φ.1.app (op (Over.mk (𝟙 I.Y.left)))) hM) s
  simpa using happ
/-- Helper for Lemma 8.11.8: after restricting to one refinement member, the first pulled overlap
branch evaluated at `op I.Y` is exactly the owner-object evaluation at
`op (Over.mk Ī.toMiddleHom)`. This isolates the first transport shell before the common-owner
comparison theorem is applied. -/
theorem chosen_cover_refinement_member_first_branch_map_app_to_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base;
    let hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI :=
      (by
        have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
        have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
          rw [hms]; exact Over.w I.f
        simpa [K₁₂, qI, GrothendieckTopology.Cover.Arrow.base,
          GrothendieckTopology.Cover.Arrow.fromMiddle, Category.assoc] using step);
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)))).1.obj
        (op (Over.mk Ī.toMiddleHom))),
    (((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
            (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁])
            (by simpa [Category.assoc, _hf₂]))).1.app
        (op (Over.mk Ī.toMiddleHom)) s =
      (congrArg (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.obj
          (over_map_obj_mk_eq_op K₁₂.f Ī.toMiddleHom qI hg₁₂)).mpr
        ((automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
              (K.f ≫ f₂)
              (by simpa [Category.assoc, _hf₁])
              (by simpa [Category.assoc, _hf₂])).1.app
            (op (Over.mk qI))
          (Eq.mp (congrArg (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj
              (over_map_obj_mk_eq_op K₁₂.f Ī.toMiddleHom qI hg₁₂)) s)) := by
  intro Ī qI K₁₂ hg₁₂ s
  exact pseudofunctor_over_map_app_eq_owner_transport K₁₂.f
    (automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by simpa [Category.assoc, _hf₁]) (by simpa [Category.assoc, _hf₂]))
    Ī.toMiddleHom qI hg₁₂ s
/-- Helper for Lemma 8.11.8: after restricting to one refinement member, the second pulled
overlap branch evaluated at `op I.Y` is exactly the owner-object evaluation at
`op (Over.mk (𝟙 I.Y.left))`. This isolates the second transport shell before the common-owner
comparison theorem is applied. -/
theorem chosen_cover_refinement_member_second_branch_map_app_to_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base;
    let hg₂₃ : (𝟙 I.Y.left) ≫ K₂₃.f = qI :=
      (by
        have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
        have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
          rw [hms]; exact Over.w I.f
        simpa [K₂₃, qI, GrothendieckTopology.Cover.Arrow.base,
          GrothendieckTopology.Cover.Arrow.toMiddle, GrothendieckTopology.Cover.Arrow.fromMiddle,
          Category.assoc] using step);
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
            (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂])
            (by simpa [Category.assoc, _hf₃]))).1.app
        (op (Over.mk (𝟙 I.Y.left))) s =
      (congrArg (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₃).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.obj
          (over_map_obj_mk_eq_op K₂₃.f (𝟙 I.Y.left) qI hg₂₃)).mpr
        ((automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃])).1.app
            (op (Over.mk qI))
          (Eq.mp (congrArg (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.obj
              (over_map_obj_mk_eq_op K₂₃.f (𝟙 I.Y.left) qI hg₂₃)) s)) := by
  intro Ī qI K₂₃ hg₂₃ s
  exact pseudofunctor_over_map_app_eq_owner_transport K₂₃.f
    (automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
      (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃]))
    (𝟙 I.Y.left) qI hg₂₃ s
/-- Helper for Lemma 8.11.8: once the first branch is rewritten to the shared owner
`qI := I.Y.hom`, changing the owner leg from `Ī.toMiddleHom` to the identity on `I.Y.left` does
not change the induced common-owner conjugation on the fixed section `αI`. This isolates the
endpoint-independence part of the first-branch normalization from the remaining self-leg
transport. -/
theorem chosen_cover_refinement_member_first_branch_qI_leg_eq_identity_leg
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base;
    let hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI :=
      (by
        have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
        have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
          rw [hms]; exact Over.w I.f
        simpa [K₁₂, qI, GrothendieckTopology.Cover.Arrow.base,
          GrothendieckTopology.Cover.Arrow.fromMiddle, Category.assoc] using step);
    let selfArrow :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      K₁₂.precomp Ī.toMiddleHom;
    ∀ (s : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (qI ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI (K := K₁₂) Ī.toMiddleHom hg₁₂).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI (K := selfArrow) (𝟙 I.Y.left)
            (by simpa [selfArrow] using hg₁₂)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s := by
  intro Ī qI K₁₂ hg₁₂ selfArrow s
  exact local_overlap_common_owner_conjugation_eq_app
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (K.f ≫ f₁) (K.f ≫ f₂) qI (K₁ := K₁₂) (K₂ := selfArrow) Ī.toMiddleHom (𝟙 I.Y.left) hg₁₂
    (by simpa [selfArrow] using hg₁₂)
    (op (Over.mk (𝟙 I.Y.left))) s
/-- Helper for Lemma 8.11.8: on the second branch, the self-leg common-owner shell is already the
shared-owner `qI` shell after unfolding the chosen common-refinement arrow `K₂₃`. This removes
the second branch from the remaining owner-leg blocker entirely. -/
theorem chosen_cover_refinement_member_second_branch_qI_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base;
    let hg₂₃ : (𝟙 I.Y.left) ≫ K₂₃.f = qI :=
      (by
        have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
        have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
          rw [hms]; exact Over.w I.f
        simpa [K₂₃, qI, GrothendieckTopology.Cover.Arrow.base,
          GrothendieckTopology.Cover.Arrow.toMiddle, GrothendieckTopology.Cover.Arrow.fromMiddle,
          Category.assoc] using step);
    let hK : K₂₃.f = qI := by simpa using hg₂₃;
    ∀ (s : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K₂₃.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (K := K₂₃) (𝟙 K₂₃.Y) (Category.id_comp _)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s =
        (congrArg (fun (g : I.Y.left ⟶ K.Y) =>
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (g ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_target_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₃)))).1.obj
            (op (Over.mk (𝟙 I.Y.left)))) hK).mpr
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (local_overlap_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                (K.f ≫ f₂) (K.f ≫ f₃) qI (K := K₂₃) (𝟙 I.Y.left) hg₂₃).hom).hom).1.app
            (op (Over.mk (𝟙 I.Y.left))))
            (Eq.mp (congrArg (fun (g : I.Y.left ⟶ K.Y) =>
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (g ^*[canonicalPullbackChoice 𝒮.p]
                    (local_overlap_source_object (𝒮 := 𝒮)
                      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂)))).1.obj
                  (op (Over.mk (𝟙 I.Y.left)))) hK) s)) := by
  intro Ī qI K₂₃ hg₂₃ hK s
  clear_value hK hg₂₃ qI
  subst hK
  rfl
/-- Helper for Lemma 8.11.8: on one refinement member `I`, the restricted first pulled-overlap
branch is already rewritten to the self-leg common-owner shell on the intermediate owner object
`op (Over.mk Ī.toMiddleHom)`. This packages the solved naturality and owner-object transport on
the first branch so the only remaining work is the self-leg-to-shared-owner comparison. -/
theorem chosen_cover_refinement_member_first_branch_restrict_eq_self_leg_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base;
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁₂.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂));
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₁)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁₂.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁));
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)))).1.obj
        (op (Over.mk Ī.toMiddleHom))),
    (((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁])
            (by simpa [Category.assoc, _hf₂]))).1.app
        (op (Over.mk Ī.toMiddleHom))) s) =
      (cIso.inv.1.app (op (Over.mk Ī.toMiddleHom))
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
          (op (Over.mk Ī.toMiddleHom)))
        (bIso.hom.1.app (op (Over.mk Ī.toMiddleHom)) s))) := by
  intro Ī K₁₂ cIso bIso s
  exact chosen_cover_refinement_member_first_branch_eq_common_owner_app
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T (R := R) I hImem s
/-- Helper for Lemma 8.11.8: on one refinement member `I`, the restricted second pulled-overlap
branch is already rewritten all the way to the shared-owner `qI` shell on
`op (Over.mk (𝟙 I.Y.left))`. This packages the solved second-branch normalization so the live
memberwise blocker is only the first-branch transport to the same shared shell. -/
theorem chosen_cover_refinement_member_second_branch_restrict_eq_qI_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base;
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂₃.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂));
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₃)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂₃.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₃));
    ∀ (s : (((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂])
            (by simpa [Category.assoc, _hf₃]))).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s) =
      (cIso.inv.1.app (op (Over.mk (𝟙 I.Y.left)))
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        (bIso.hom.1.app (op (Over.mk (𝟙 I.Y.left))) s))) := by
  intro Ī K₂₃ bIso cIso s
  exact chosen_cover_refinement_member_second_branch_eq_common_owner_app
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T (R := R) I hImem s
