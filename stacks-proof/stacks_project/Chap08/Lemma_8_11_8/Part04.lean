import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part03

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
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
          (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₃ K)).hom) := by
  -- Route correction: compare all three local identifications on the same owner `q`. Once they
  -- share endpoints, endpoint-independence of conjugation replaces the composite branch by the
  -- direct pulled `(f₁,f₃)` isomorphism.
  rw [← automorphismUnderlyingSheafConj_comp]
  simpa using
    (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      ((local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₁) (K.f ≫ f₂) q g₁₂ hg₁₂).hom ≫
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS (K.f ≫ f₂) (K.f ≫ f₃) q g₂₃ hg₂₃).hom)
      ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).mapIso
        (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₃ K)).hom))

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
          (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₃ K)).hom)).hom := by
  -- Pass from the iso-level source invariant to the morphism-level form used by the descent API.
  simpa using
    congrArg Iso.hom
      (secondary_cover_pairwise_common_owner_conjugation_comp
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ f₃ K (Z := Z) q
        (K₁₂ := K₁₂) (K₂₃ := K₂₃) g₁₂ g₂₃ hg₁₂ hg₂₃)

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
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) =
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂) := by
  let T :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- Compare both morphisms after applying the faithful chosen-cover descent functor on `C / K.Y`.
  apply Functor.map_injective E.functor
  -- The left side is exactly the previously isolated fixed-cover-to-secondary-cover transport.
  rw [chosen_cover_overlap_map_to_secondary_cover_descent
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ K]
  -- The right side has the same descent-data image by the generic overlap characterization.
  exact
    automorphism_overlap_hom_characterization
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by simpa [Category.assoc, hf₁])
      (by simpa [Category.assoc, hf₂])

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
          (local_overlap_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom := by
  -- This is exactly the already-proved common-owner composition law specialized to the fixed
  -- chosen gerbe cover of `U`.
  simpa using
    secondary_cover_pairwise_common_owner_conjugation_comp_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      f₁ f₂ f₃ K (Z := Z) qZ
      (K₁₂ := K₁₂) (K₂₃ := K₂₃) g₁₂ g₂₃ hg₁₂ hg₂₃

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
    ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
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
            (local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
        R) α := by
  -- Evaluate the specialized chosen-cover common-owner composition theorem on the fixed section.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app R))
        (chosen_cover_pairwise_common_owner_conjugation_comp_hom
          (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ K qZ
          (K₁₂ := K₁₂) (K₂₃ := K₂₃) g₁₂ g₂₃ hg₁₂ hg₂₃))
      α

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
  exact (((isSheaf_iff_isSheaf_of_type (J.over U) ℱ.1).1 ℱ.property).isSeparated _ R.2).ext
    (fun I ↦ hss I)

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
  let qT := T.unop.hom
  let S12 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)
  let S23 :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)
  let B : J.Cover T.unop.left :=
    (S12.pullback qT).bind fun A ↦ S23.pullback A.base.f
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
    ∃ Ī : B.Arrow, Ī.f = I.f.left := by
  refine ⟨⟨I.Y.left, I.f.left, ?_⟩, rfl⟩
  have hIf : ((Sieve.overEquiv T).symm (B : Sieve T.left)) I.f := by
    simpa [hR] using I.hf
  -- `Sieve.overEquiv_symm_iff` removes the slice transport and recovers the base-cover member.
  exact (Sieve.overEquiv_symm_iff (B : Sieve T.left) I.f).1 hIf

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
  simpa using congrFun (φ.1.naturality i.op) α

/-- Helper for Lemma 8.11.8: if the owner arrow of an object in one slice composes to `h`, then
its image under the corresponding `Over.map` is literally the object `Over.mk h` in the larger
slice. This is the object-level transport that remains after the outer naturality rewrite. -/
theorem over_map_obj_mk_eq
    {X Y Z : C} (f : Y ⟶ Z) {W : C} (g : W ⟶ Y) (h : W ⟶ Z)
    (hg : g ≫ f = h) :
    (Over.map f).obj (Over.mk g) = Over.mk h := by
  -- Reduce to the definitional case where the composed owner arrow is exactly `h`.
  cases hg
  rfl

/-- Helper for Lemma 8.11.8: the previous `Over.map` owner-object identification can be moved to
the opposite slice object used by `.app` on a presheaf. This keeps the transport step explicit
without reopening any descent-data internals. -/
theorem over_map_obj_mk_eq_op
    {X Y Z : C} (f : Y ⟶ Z) {W : C} (g : W ⟶ Y) (h : W ⟶ Z)
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
      (φ.1.app (op (Over.mk h)))
        (Eq.mp (congrArg ℱ.1.obj (over_map_obj_mk_eq_op g k h hk)) s) := by
  -- First expose the mapped component on the literal image object, then rewrite that image object
  -- to the normalized owner `Over.mk h`.
  rw [pseudofunctor_over_map_app_eq_image_app]
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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle
    (((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁])
            (by simpa [Category.assoc, _hf₂]))).1.app
        (op (Over.mk Ī.toMiddleHom)))
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α)) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
        (op (Over.mk Ī.toMiddleHom)))
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α)) := by
  -- Route correction: specialize the generic secondary-cover component theorem exactly on the
  -- owner object carried by the first branch of the refinement member.
  dsimp
  simpa [Category.assoc] using
    (automorphism_overlap_hom_secondary_cover_component_eq_common_owner_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      K.f q f₁ f₂ _hf₁ _hf₂ (K.f ≫ f₁) (K.f ≫ f₂) rfl rfl
      Ī.fromMiddle
      (op (Over.mk Ī.toMiddleHom))
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α))

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
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left)
    (β : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      ((I.Y.hom) ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂)))).1.obj (op (Over.mk (𝟙 I.Y.left)))) :
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base
    (((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂])
            (by simpa [Category.assoc, _hf₃]))).1.app
        (op (Over.mk (𝟙 I.Y.left)))) β) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) β) := by
  -- Route correction: specialize the same component theorem on the identity leg of the second
  -- branch, keeping the owner object fixed at `I.Y.left`.
  dsimp
  simpa [Category.assoc] using
    (automorphism_overlap_hom_secondary_cover_component_eq_common_owner_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      K.f q f₂ f₃ _hf₂ _hf₃ (K.f ≫ f₂) (K.f ≫ f₃) rfl rfl
      Ī.toMiddle.base
      (op (Over.mk (𝟙 I.Y.left))) β)

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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
    ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
            (K.f ≫ f₂)
            (by simpa [Category.assoc, _hf₁])
            (by simpa [Category.assoc, _hf₂]))).1.app
        (op I.Y)) αI)) =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
              (K.f ≫ f₂)
              (by simpa [Category.assoc, _hf₁])
              (by simpa [Category.assoc, _hf₂]))).1.app
          (op (Over.mk Ī.toMiddleHom)))
        αI)) := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let K₁₂ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
    Ī.fromMiddle
  have hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI := by
    -- The first branch of the common refinement lies over the owner `qI`.
    simpa [K₁₂, qI, T, hĪ, Category.assoc] using congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec
  have hObj12op :
      op ((Over.map K₁₂.f).obj (Over.mk Ī.toMiddleHom)) = op I.Y := by
    -- Move the owner-object identification to the opposite slice object used by `.app`.
    simpa [qI] using over_map_obj_mk_eq_op K₁₂.f Ī.toMiddleHom qI hg₁₂
  -- Route correction: instantiate the generic owner-transport theorem on the first branch and
  -- normalize the resulting owner object back to `op I.Y`.
  dsimp [qI, K₁₂]
  symm
  simpa [hObj12op] using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := Ī.fromMiddle.f)
      (φ := automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (by simpa [Category.assoc, _hf₁])
        (by simpa [Category.assoc, _hf₂]))
      (k := Ī.toMiddleHom) (h := I.Y.hom) (hk := hg₁₂)
      (s := (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α))

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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base
    let βI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
    ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
            (K.f ≫ f₃)
            (by simpa [Category.assoc, _hf₂])
            (by simpa [Category.assoc, _hf₃]))).1.app
        (op I.Y)) βI =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃]))).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI) := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let K₂₃ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
    Ī.toMiddle.base
  let βI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  have hg₂₃ : (𝟙 I.Y.left) ≫ K₂₃.f = qI := by
    -- The second branch uses the identity owner leg over the same owner `qI`.
    simpa [K₂₃, qI, hĪ, GrothendieckTopology.Cover.Arrow.base, Category.assoc] using
      congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec
  have hObj23op :
      op ((Over.map K₂₃.f).obj (Over.mk (𝟙 I.Y.left))) = op I.Y := by
    -- Move the owner-object identification to the opposite slice object used by `.app`.
    simpa [qI] using over_map_obj_mk_eq_op K₂₃.f (𝟙 I.Y.left) qI hg₂₃
  -- Route correction: instantiate the same owner-transport theorem on the identity-leg branch and
  -- normalize the resulting owner object back to `op I.Y`.
  dsimp [qI, K₂₃, βI]
  symm
  simpa [hObj23op] using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := Ī.toMiddle.base.f)
      (φ := automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
        (by simpa [Category.assoc, _hf₂])
        (by simpa [Category.assoc, _hf₃]))
      (k := 𝟙 I.Y.left) (h := I.Y.hom) (hk := hg₂₃)
      (s := (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α))))

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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom
            (by
              simpa [K₁₂, qI, T, hĪ, Category.assoc] using
                congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI (𝟙 I.Y.left)
            (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let K₁₂ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
    Ī.fromMiddle
  let αI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
  have hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI := by
    -- The first branch of the common refinement lies over the shared owner `qI`.
    simpa [K₁₂, qI, T, hĪ, Category.assoc] using congrArg (fun k ↦ k ≫ T.unop.hom) Ī.middle_spec
  -- Evaluate the generic endpoint-independence theorem at the shared owner object `op (Over.mk 1)`.
  dsimp [qI, K₁₂, αI]
  simpa using
    (local_overlap_common_owner_conjugation_eq_app
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (K.f ≫ f₁) (K.f ≫ f₂) qI Ī.toMiddleHom (𝟙 I.Y.left)
      hg₁₂ (by simp [qI]) (op (Over.mk (𝟙 I.Y.left)))
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α))

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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base
    let βI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left)
            (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let K₂₃ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
    Ī.toMiddle.base
  let βI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  -- The second refinement arrow is definitionally the shared owner `qI`.
  dsimp [qI, K₂₃, βI]
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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
        (op (Over.mk Ī.toMiddleHom)))
      αI := by
  let K₁₂ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
    Ī.fromMiddle
  let αI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.map I.f.op α
  have hFirstRestrict :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α) =
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app
            (op I.Y)) αI) := by
    -- First remove the outer restriction from the `(f₁,f₂)` branch by naturality.
    simpa [αI] using
      sheaf_hom_app_restrict_eq
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)))
        I.f α
  have hFirstMapToOwner :
      ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
              (K.f ≫ f₂)
              (by simpa [Category.assoc, _hf₁])
              (by simpa [Category.assoc, _hf₂]))).1.app
          (op I.Y)) αI =
        ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
                (K.f ≫ f₂)
                (by simpa [Category.assoc, _hf₁])
                (by simpa [Category.assoc, _hf₂]))).1.app
            (op (Over.mk Ī.toMiddleHom)))
          αI) := by
    -- Then move that component to the literal owner object `op (Over.mk Ī.toMiddleHom)`.
    simpa [K₁₂, αI] using
      chosen_cover_refinement_member_first_branch_map_app_to_owner
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  -- Route correction: the first branch is now normalized exactly to the self-leg shell at the
  -- middle owner object. The unresolved transport to the shared owner `qI` is factored out.
  calc
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
        =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
              (K.f ≫ f₂)
              (by simpa [Category.assoc, _hf₁])
              (by simpa [Category.assoc, _hf₂]))).1.app
          (op I.Y)) αI := hFirstRestrict
    _ =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₁₂.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
              (K.f ≫ f₂)
              (by simpa [Category.assoc, _hf₁])
              (by simpa [Category.assoc, _hf₂]))).1.app
          (op (Over.mk Ī.toMiddleHom)))
        αI := hFirstMapToOwner
    _ =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) K₁₂.f (𝟙 K₁₂.Y)).hom).hom).1.app
        (op (Over.mk Ī.toMiddleHom)))
      αI := by
        -- Finally apply the existing component theorem on the first secondary-cover branch.
        simpa [K₁₂, αI] using
          chosen_cover_refinement_member_first_branch_eq_common_owner_app
            (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
            (B := B) (R := R) I Ī hĪ

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
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))).1.obj T)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base
    let βI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app T)
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)) =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left)
            (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := by
  let qI : I.Y.left ⟶ K.Y := I.Y.hom
  let K₂₃ :
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
    Ī.toMiddle.base
  let βI :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))).1.map I.f.op
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  have hSecondRestrict :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app T)
            ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                  (automorphism_overlap_hom_of_locally_isomorphic_cover
                    (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)) =
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app
            (op I.Y))
          βI) := by
    -- First remove the outer restriction from the `(f₂,f₃)` branch by naturality.
    simpa [βI] using
      sheaf_hom_app_restrict_eq
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)))
        I.f
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
  have hSecondMapToOwner :
      ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃]))).1.app
          (op I.Y)) βI =
        ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
                (K.f ≫ f₃)
                (by simpa [Category.assoc, _hf₂])
                (by simpa [Category.assoc, _hf₃]))).1.app
            (op (Over.mk (𝟙 I.Y.left))))
          βI) := by
    -- Then move that component to the literal shared-owner object `op (Over.mk 1)`.
    simpa [qI, K₂₃, βI] using
      chosen_cover_refinement_member_second_branch_map_app_to_owner
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  have hSecondSelfLeg :
      ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃]))).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := by
    -- Apply the existing component theorem on the second secondary-cover branch.
    simpa [K₂₃, βI] using
      chosen_cover_refinement_member_second_branch_eq_common_owner_app
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T
        (B := B) (R := R) I Ī hĪ βI
  have hSecondQIShell :
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left) (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI := by
    -- The second branch is already the shared-owner shell after unfolding `K₂₃`.
    simpa [qI, K₂₃, βI] using
      chosen_cover_refinement_member_second_branch_qI_shell
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
        (B := B) (R := R) I Ī hĪ
  calc
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)).1.app T)
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).1.app T) α)
        =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃]))).1.app
          (op I.Y)) βI := hSecondRestrict
    _ =
      ((((((J.pseudofunctorOver (Type (max u v))).map K₂₃.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
              (K.f ≫ f₃)
              (by simpa [Category.assoc, _hf₂])
              (by simpa [Category.assoc, _hf₃]))).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        βI := hSecondMapToOwner
    _ =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) K₂₃.f (𝟙 K₂₃.Y)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := hSecondSelfLeg
    _ =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₂) (K.f ≫ f₃) qI (𝟙 I.Y.left)
            (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      βI := hSecondQIShell

end CategoryTheory
