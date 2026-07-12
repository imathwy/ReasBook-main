import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part08

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

section
-- Class B: the `^*[cpc]` composite-pullback and `Conj` types in the pullback-cover statements
-- below trigger a `whnf`/`isDefEq` storm when `canonicalPullbackChoice` unfolds into its
-- `Classical.choice`-built fibered `ObjectProperty.FullSubcategory` objects. Freezing the abbrev
-- as irreducible stops the storm at statement-elaboration time without a resource bump.
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Helper for Lemma 8.11.8: once the common owner is fixed to one secondary-cover refinement
`L`, the normalized local-overlap descent square specializes to the comparison between the source
and target boundary maps on `L.f`. This packages the repeated `g = 𝟙` instantiation used in the
pullback-cover target comparison.

FAITHFULNESS NOTE (Mathlib-refactor restatement): the old conjugation-iso phrasing of this square
relied on the (now-broken) identity-pullback defeq `(pf.map 𝟙).obj X ≡ X` and on
`local_overlap_conjugation_iso`; post-refactor those sides land in non-defeq sheaves. The genuine
content is exactly the `g = 𝟙` specialization of `local_overlap_secondary_descent_square_normalized`
(Part02), restated here over the canonical `local_overlap_secondary_component_iso`. -/
theorem local_overlap_secondary_descent_square_at_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.map
        ((local_overlap_secondary_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ L).hom) ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom L.f (𝟙 L.Y) (𝟙 L.Y) =
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom L.f (𝟙 L.Y) (𝟙 L.Y) ≫
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.map
        ((local_overlap_secondary_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ L).hom) := by
  -- The `g = 𝟙` specialization of the normalized local-overlap secondary-cover square, read off
  -- the `comm` field of the public secondary-cover descent comparison iso.
  exact (secondary_cover_descent_iso_on_local_overlap
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom.comm L.f (𝟙 L.Y) (𝟙 L.Y)
    (Category.id_comp _) (Category.id_comp _)

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_component_refined
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) := by
  -- DEEP DEFERRED (genuine member-cross grind): this is the fixed-(K,L) source/target boundary
  -- comparison on the pullback-cover's target branch. It must be assembled from the Part08
  -- assembly-bridge machinery (`assembly_*_bridge`, `pullback_cover_target_secondary_cover_*`,
  -- `pullback_cover_target_secondary_cover_outer_transport_normalized`) plus the normalized
  -- common-owner square `local_overlap_secondary_descent_square_normalized`. The remaining
  -- transport-stable normalization is isolated in the Part08 assembly adapter.
  exact (pullback_cover_target_secondary_cover_assembly_adapter
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).2

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K) := by
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor
  ext L
  exact pullback_cover_target_secondary_cover_component_refined
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is the chosen-local comparison square over the common owner `r`. Isolating
this smaller square keeps the main pullback-cover proof as a pure pasting argument. -/
private theorem pullback_cover_target_secondary_cover_reduction
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂)) =
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv) := by
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor
  ext K
  exact pullback_cover_target_secondary_cover_component_normalized
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is the chosen-local comparison square over the common owner `r`. Isolating
this smaller square keeps the main pullback-cover proof as a pure pasting argument. -/
private theorem pullback_cover_target_component_coherence
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂)) =
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv) := by
  exact pullback_cover_target_secondary_cover_reduction
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂


/-- Generic abstract-category assembler for the owner-comparison square: once the residual
`cover_iso.inv ≫ cover_iso.hom` is the identity, the SCT-normalized left branch collapses to the
local-object component on the right.  Phrased over abstract objects so the (definitional but not
syntactic) owner discrepancy between the pulled chosen-cover datum and the pulled local-object
datum is absorbed by the `exact`. -/
private theorem star_assemble {D : Type*} [Category D] {O0 O1 O2 O3 O4 O5 : D}
    (dpull : O0 ⟶ O1) (ps : O1 ⟶ O2) (ciInv : O2 ⟶ O3) (ciHom : O3 ⟶ O2)
    (cl : O2 ⟶ O4) (bcInv : O4 ⟶ O5)
    (hc : ciInv ≫ ciHom = 𝟙 O2) :
    (dpull ≫ ps ≫ ciInv) ≫ ciHom ≫ cl ≫ bcInv = dpull ≫ ps ≫ cl ≫ bcInv := by
  rw [Category.assoc, Category.assoc, ← Category.assoc ciInv, hc, Category.id_comp]

/-- Helper for Lemma 8.11.8: the pullback-cover component family satisfies the `isoMk` overlap
square once both branches are rewritten through the normalized source component and the
pairwise-local comparison. This isolates the first remaining datum-level blocker after the
componentwise map has been separated out. -/
private theorem pullback_cover_local_object_component_coherence
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((pullback_cover_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y I₁).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).hom r g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((pullback_cover_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y I₂).hom) := by
  -- Assembly of the owner-comparison square from the two proven halves:
  --   * the chosen-local owner-comparison `pullback_cover_target_secondary_cover_reduction`
  --     (the `y ↔ chosen-local` part), and
  --   * the source-faithful transition `pullback_cover_source_component_transition` (SCT,
  --     the `Wch ↔ chosen` part).
  -- After unfolding `pullback_cover_local_object_component_iso = pscomp ≪≫ chosen_local ≪≫ bc.symm`,
  -- the chosen-local/base-change/descent tail is rewritten by `reduction`, the pscomp/cover-iso
  -- head is normalized to the chosen-cover transition and absorbed by SCT, and the residual
  -- `cover_iso.inv ≫ cover_iso.hom` cancels.
  have hred := pullback_cover_target_secondary_cover_reduction
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  have hsct := pullback_cover_source_component_transition
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂
  rw [Functor.mapIso_inv, Functor.mapIso_inv] at hred
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp] at hsct
  simp only [pullback_cover_local_object_component_iso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  erw [hred, reassoc_of% hsct]
  have e2 :
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom = 𝟙 _ := by
    rw [← Functor.map_comp]; simp
  exact star_assemble _ _ _ _ _ _ e2

/-- Helper for Lemma 8.11.8: the source-faithful pullback comparison should first be constructed
as an isomorphism of descent data on the pullback cover of the chosen gerbe cover of `U` along
`q : Y ⟶ U`. This isolates the remaining blocker at the datum level before transporting back to
sheaves on `C / Y`. -/
noncomputable def pullback_cover_local_object_comparison_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)) ≅
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y) := by
  -- Route correction: the datum-level comparison is now split into an explicit component map and
  -- one remaining overlap square on the pullback cover.
  exact
    Pseudofunctor.DescentData.isoMk
      (fun I ↦
        pullback_cover_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y I)
      (by
        intro _Z _r _i₁ _i₂ _g₁ _g₂ _hg₁ _hg₂
        exact pullback_cover_local_object_component_coherence
          (𝒮 := 𝒮) hGerbe hAbelian q y _r _g₁ _g₂ _hg₁ _hg₂)

/-- Helper for Lemma 8.11.8: first build the source-faithful comparison between the pulled
chosen-cover sheaf from `U` and the automorphism sheaf of `y` on `C / Y`, and only afterwards
let the chosen-cover descent functor extract components. -/
-- De-privatized (was `private`) for Lemma 8.11.8 Part11: the §5.4 identity/cocycle laws
-- (`chosen_cover_descent_transition_id_*`, `chosen_cover_transport_transition_comp_*`) reference
-- this sheaf-level comparison directly. Flagged de-privatization; Part09 still builds green.
noncomputable def chosen_cover_pullback_to_local_object_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y) :
    (J.overMapPullback (Type (max u v)) q).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y :=
  -- Route correction: the sheaf-level comparison is now only the transport of the datum-level
  -- comparison on the pullback cover of the chosen gerbe cover of `U`.
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q)
    (pullback_cover_local_object_comparison_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y)

/-- Helper for Lemma 8.11.8: package the generic chosen-cover pullback comparison against a fixed
object `y : 𝒮.p.Fiber Y` as the image of the sheaf comparison under the chosen-cover descent
functor on `Y`. -/
noncomputable def chosen_cover_pullback_to_local_object_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y) :
    (chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe Y).obj
        ((J.overMapPullback (Type (max u v)) q).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≅
      (chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe Y).mapIso
    (chosen_cover_pullback_to_local_object_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y)

/-- Helper for Lemma 8.11.8: the `L`-component of the chosen-cover pullback comparison satisfies
the inverse law because it is extracted from a single isomorphism of descent data. -/
private theorem chosen_cover_pullback_to_local_object_component_hom_inv_id
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_pullback_to_local_object_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y).hom.hom L) ≫
        ((chosen_cover_pullback_to_local_object_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y).inv.hom L) =
      𝟙 _ := by
  let e := chosen_cover_pullback_to_local_object_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian q y
  -- Evaluate the descent-data inverse law at the chosen-cover arrow `L`.
  change e.hom.hom L ≫ e.inv.hom L = 𝟙 _
  rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id,
    Pseudofunctor.DescentData.id_hom]

/-- Helper for Lemma 8.11.8: the `L`-component of the chosen-cover pullback comparison satisfies
the forward inverse law for the same reason. -/
private theorem chosen_cover_pullback_to_local_object_component_inv_hom_id
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_pullback_to_local_object_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y).inv.hom L) ≫
        ((chosen_cover_pullback_to_local_object_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y).hom.hom L) =
      𝟙 _ := by
  let e := chosen_cover_pullback_to_local_object_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian q y
  -- Evaluate the descent-data forward inverse law at the chosen-cover arrow `L`.
  change e.inv.hom L ≫ e.hom.hom L = 𝟙 _
  rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id,
    Pseudofunctor.DescentData.id_hom]

/-- Helper for Lemma 8.11.8: on one chosen-cover arrow `L` of an arbitrary base `Y`, the pulled
chosen-cover comparison is just the `L`-component of the already-packaged sheaf comparison. -/
private noncomputable def chosen_cover_pullback_to_local_object_component_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe Y).obj
        ((J.overMapPullback (Type (max u v)) q).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))).obj L ≅
      ((chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj L :=
  { hom := (chosen_cover_pullback_to_local_object_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y).hom.hom L
    inv := (chosen_cover_pullback_to_local_object_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y).inv.hom L
    hom_inv_id := chosen_cover_pullback_to_local_object_component_hom_inv_id
      (𝒮 := 𝒮) hGerbe hAbelian q y L
    inv_hom_id := chosen_cover_pullback_to_local_object_component_inv_hom_id
      (𝒮 := 𝒮) hGerbe hAbelian q y L }

/-- Helper for Lemma 8.11.8: the `L`-component of the chosen-cover pullback comparison is the
raw pullback of the sheaf-side comparison along `L.f`. This is the transport-stable interface
needed before comparing it with conjugation on the same slice. -/
theorem chosen_cover_pullback_to_local_object_component_iso_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (chosen_cover_pullback_to_local_object_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y L).hom =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y).hom) := by
  -- The chosen-cover descent functor is `toDescentData`, so its `L`-component is definitionally
  -- the pullback map along `L.f`.
  rfl

/-- Helper for Lemma 8.11.8: the inverse `L`-component of the chosen-cover pullback comparison is
the pullback of the inverse sheaf-side comparison along `L.f`. This isolates the inverse-side
transport shell before the fixed-`K` identity cancellation step. -/
theorem chosen_cover_pullback_to_local_object_component_iso_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (chosen_cover_pullback_to_local_object_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y L).inv =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y).inv) := by
  -- Read the inverse component from the same descended isomorphism, but now on the inverse side.
  rfl

/-- Helper for Lemma 8.11.8: the `L`-component of the chosen-cover descent image of a
conjugation isomorphism is the pullback of that conjugation along `L.f`. This keeps the blocked
slice-comparison proof on the owner-level map it really needs. -/
theorem chosen_cover_descent_functor_mapIso_conj_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)).hom.hom L) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj
          (𝒮 := 𝒮) hAbelian φ).hom) := by
  -- Again, `toDescentData` records the `L`-component by pulling back along `L.f`.
  rfl

/-- Helper for Lemma 8.11.8: once the sheaf-level pullback comparison is packaged as one
descent-data isomorphism, the component coherence on overlaps is the corresponding `comm` field. -/
private theorem chosen_cover_pullback_to_local_object_component_coherence
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {L₁ L₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow}
    (g₁ : Z ⟶ L₁.Y) (g₂ : Z ⟶ L₂.Y)
    (hg₁ : g₁ ≫ L₁.f = r := by cat_disch) (hg₂ : g₂ ≫ L₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y L₁).hom) ≫
      ((chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ =
    ((chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe Y).obj
        ((J.overMapPullback (Type (max u v)) q).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))).hom r g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y L₂).hom) := by
  let e := chosen_cover_pullback_to_local_object_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian q y
  -- Extract the overlap square from the descent-data morphism produced by `mapIso`.
  simpa [chosen_cover_pullback_to_local_object_component_iso, e] using
    e.hom.comm r g₁ g₂ hg₁ hg₂

/-- Helper for Lemma 8.11.8: on one arrow `K` of the chosen cover of `I.Y`, isolate the mixed-cover
local descent comparison on the slice `C / K.Y` before transporting it back to a sheaf
isomorphism. This is the datum-first pivot that keeps the remaining blocker on the local
comparison itself rather than on the outer sheaf transport shell. -/
private noncomputable def mixed_cover_secondary_cover_local_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y).Arrow ↦ L.f)).obj
      (((chosen_cover_descent_functor
          (𝒮 := 𝒮) hGerbe I.Y).obj
            ((J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U))).obj K) ≅
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y).Arrow ↦ L.f)).obj
        (((chosen_cover_descent_functor
            (𝒮 := 𝒮) hGerbe I.Y).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).obj K) := by
  -- Route correction: the mixed-cover local datum is just the specialization of the generic
  -- chosen-cover pullback comparison to `Y := I.Y`, `q := I.f ≫ f`, and the chosen local object
  -- over `V` indexed by `I`, followed by the chosen-cover descent functor on `K.Y`.
  exact
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe K.Y).mapIso
      (chosen_cover_pullback_to_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (q := I.f ≫ f)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I) K)

/-- Helper for Lemma 8.11.8: on one arrow `K` of the chosen cover of `I.Y`, isolate the mixed-cover
component comparison between the normalized pullback of the descended chosen-cover sheaf from `U`
and the local automorphism sheaf of the chosen object over `V`. This is the component family that
the source proof packages by `Pseudofunctor.DescentData.isoMk`. -/
noncomputable def mixed_cover_secondary_cover_component_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        ((J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))).obj K ≅
    ((chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe I.Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).obj K :=
  -- Transport the mixed local comparison on `C / K.Y` back from the chosen local cover. This
  -- removes the outer sheaf-level construction from the remaining blocker.
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y)
    (mixed_cover_secondary_cover_local_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I K)

/-- Helper for Lemma 8.11.8: after transporting the mixed local comparison on `C / K.Y` back to
sheaves, reapplying the explicit chosen-cover descent functor on `K.Y` recovers the original
local descent-data morphism. This is the exact transport rewrite needed before reducing the
coherence square to the normalized secondary-cover square. -/
private theorem mixed_cover_secondary_cover_component_iso_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y)).functor.map
      ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I K).hom)) =
        (mixed_cover_secondary_cover_local_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K).hom := by
  -- This is the generic cover-descent transport identity specialized to the mixed-cover
  -- component on the slice `C / K.Y`.
  simpa [mixed_cover_secondary_cover_component_iso] using
    localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y)
      (mixed_cover_secondary_cover_local_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I K)

/-- Helper for Lemma 8.11.8: after cancelling the local cover-descent transport on `C / K.Y`,
the mixed-cover component is exactly the generic chosen-cover pullback comparison against the
chosen local object over `V`. This exposes the stable owner-level comparison used repeatedly in
the later coherence and identity calculations. -/
theorem mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I K =
      chosen_cover_pullback_to_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (q := I.f ≫ f)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I) K := by
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe K.Y
  let e := mixed_cover_secondary_cover_local_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian f I K
  -- Cancel the local cover-descent transport on `C / K.Y`; the transported mixed-cover component
  -- is the original chosen-cover pullback comparison on that slice.
  apply Iso.ext
  apply Functor.map_injective
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor)
  change
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
      ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I K).hom)) =
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
      ((chosen_cover_pullback_to_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (q := I.f ≫ f)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I) K).hom))
  rw [mixed_cover_secondary_cover_component_iso_functor_map]
  rfl

/-- Helper for Lemma 8.11.8: the mixed-cover component family on the chosen cover of `I.Y`
satisfies the `isoMk` comm square once both boundary maps are rewritten to the same secondary-cover
owner. This isolates the transport-heavy blocker from the datum packaging itself. -/
private theorem mixed_cover_secondary_cover_component_coherence
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    {Z : C} (q : Z ⟶ I.Y)
    {K₁ K₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K₁).hom) ≫
      ((chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe I.Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom q g₁ g₂ =
    ((chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        ((J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))).hom q g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K₂).hom) := by
  -- Route correction: the transport cancellation on each fixed `Kᵢ` is now a standalone helper,
  -- so the remaining proof is exactly the generic chosen-cover pullback coherence square.
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian f I K₁]
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian f I K₂]
  simpa using
    chosen_cover_pullback_to_local_object_component_coherence
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := I.f ≫ f)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
      (r := q) g₁ g₂ hg₁ hg₂

/-- Helper for Lemma 8.11.8: once the mixed-cover component family and its comm square are named
explicitly, the datum-level mixed-cover comparison on the chosen cover of `I.Y` is the direct
`isoMk` package. This keeps later proofs from reopening the same transport shell. -/
private noncomputable def mixed_cover_secondary_cover_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        ((J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≅
      (chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe I.Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)) :=
  Pseudofunctor.DescentData.isoMk
    (fun K ↦
      mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I K)
    (by
      intro _Z _q _i₁ _i₂ _g₁ _g₂ _hg₁ _hg₂
      exact mixed_cover_secondary_cover_component_coherence
        (𝒮 := 𝒮) hGerbe hAbelian f I _q _g₁ _g₂ _hg₁ _hg₂)

/-- Helper for Lemma 8.11.8: on one chosen-cover member `I` of `V`, compare the pulled chosen-cover
component of `U` directly with the automorphism sheaf of the chosen local object over `V`. This is
the datum-side source-faithful base-change component isolated from the later transport shell. -/
private noncomputable def chosen_cover_pulled_component_local_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).obj I) ≅
      (chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe I.Y).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)) := by
  -- Route correction: the mixed-cover datum is now packaged separately, so this definition is a
  -- short composite from the normalized outer pullback shell to that packaged local comparison.
  refine
    chosen_cover_pulled_component_local_source_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I ≪≫ ?_
  exact
    mixed_cover_secondary_cover_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I

/-- Helper for Lemma 8.11.8: on one chosen-cover member `I` of `V`, compare the pulled chosen-cover
component of `U` directly with the automorphism sheaf of the chosen local object over `V`. This is
the datum-side source-faithful base-change component isolated from the later transport shell. -/
private noncomputable def chosen_cover_pulled_component_comparison_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_pulled_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian f).obj I ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I) :=
  -- Transport the still-missing datum-side comparison on the chosen cover of `I.Y` back to the
  -- slice sheaf on `C / I.Y`. This removes the outer transport shell from later overlap proofs.
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)
    (chosen_cover_pulled_component_local_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I)

/-- Helper for Lemma 8.11.8: after transporting the pulled chosen-cover comparison on `C / I.Y`
back from descent data to sheaves, reapplying the explicit chosen-cover descent functor on `I.Y`
recovers the original local descent morphism. This removes the outer transport shell from the
later chosen-cover transition calculation. -/
private theorem chosen_cover_pulled_component_comparison_iso_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map
      (chosen_cover_pulled_component_comparison_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom) =
      (chosen_cover_pulled_component_local_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom := by
  -- Cancel the cover-descent transport on `C / I.Y`; this turns the sheaf-side comparison back
  -- into the datum-side mixed-cover comparison that the later overlap proof should package.
  simpa [chosen_cover_pulled_component_comparison_iso] using
    localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)
      (chosen_cover_pulled_component_local_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I)

/-- Helper for Lemma 8.11.8: compose the local pulled-component comparison with the existing
chosen-cover comparison for `V` itself, so each chosen-cover component lands directly in the
datum-side owner `chosen_cover_descent_datum V`. -/
noncomputable def chosen_cover_descent_transition_component_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_pulled_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian f).obj I ≅
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V).obj I :=
  chosen_cover_pulled_component_comparison_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I ≪≫
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian V I).symm

/-- Helper for Lemma 8.11.8: after applying the chosen-cover descent equivalence on `C / I.Y`,
the component transition iso is exactly the pulled local comparison followed by the inverse of the
fixed chosen-cover counit comparison. This exposes the datum-side square in the transport-stable
form needed before proving overlap coherence. -/
private theorem chosen_cover_descent_transition_component_iso_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map
      ((chosen_cover_descent_transition_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom)) =
      (chosen_cover_pulled_component_local_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
        ((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I).inv)) := by
  -- Expand the packaged component transition once, then cancel the pulled-comparison transport on
  -- `C / I.Y` using the already normalized local comparison theorem.
  rw [show (chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I).hom
          = (chosen_cover_pulled_component_comparison_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I).inv from rfl,
    ← chosen_cover_pulled_component_comparison_iso_functor_map]
  exact (localizedSheafToCoverDescentEquivalence (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map_comp _ _

/-- Helper for Lemma 8.11.8: on a fixed secondary-cover arrow `K`, the local descent comparison
for one chosen-cover member `I` splits into the normalized outer source shell followed by the
mixed-cover comparison on the common owner over `K.Y`. This freezes the datum-side owner before
the final chosen-cover counit comparison is appended. -/
private theorem chosen_cover_pulled_component_local_descent_iso_hom_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    (chosen_cover_pulled_component_local_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom.hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K).hom := by
  -- Evaluate the packaged local comparison at `K`; the first factor is the already-normalized
  -- outer pullback shell, and the second factor is definitionally the `K`-component of the
  -- mixed-cover descent comparison.
  change
    (chosen_cover_pulled_component_local_source_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom.hom K ≫
        (mixed_cover_secondary_cover_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom.hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K).hom
  rw [mixed_cover_source_component_normalized]
  rfl

/-- Helper for Lemma 8.11.8: after mapping the chosen-cover transition component through the
chosen-cover descent equivalence on `C / I.Y` and then taking the fixed `K`-component, the result
is exactly the normalized mixed-cover comparison followed by the pulled inverse chosen-cover
counit. This is the fixed-`K` transport-stable interface needed before proving the overlap
square. -/
theorem chosen_cover_descent_transition_component_mapped_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map
      ((chosen_cover_descent_transition_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom)).hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I).inv)) := by
  -- Read the fixed `K`-component from the already-packaged transition map, then rewrite the
  -- local comparison and the pulled counit comparison separately on that component.
  rw [chosen_cover_descent_transition_component_iso_functor_map,
    Pseudofunctor.DescentData.comp_hom,
    chosen_cover_pulled_component_local_descent_iso_hom_component,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  exact Category.assoc _ _ _

/-- Helper for Lemma 8.11.8: evaluating the chosen-cover descent datum on the chosen-cover arrow
`K` is literally the overlap morphism for the pulled owner `K.f ≫ q`. This freezes the middle
term on the common owner before the secondary-cover normalization is applied. -/
theorem chosen_cover_descent_datum_hom_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {V Y : C} {q : Y ⟶ V}
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      ((chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K =
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))) := by
  -- Class A: the refactor turned the `mapComp'` pseudofunctor-composition coherence from a
  -- definitional equality into a propositional one; the `K`-component is the pulled overlap on
  -- the common owner `K.f ≫ q` sandwiched by the `mapComp'` 2-cells.  This is exactly the
  -- generic `map_eq_pullHom` decomposition of a descent-datum transition followed by the descent
  -- datum's own `pullHom_hom` cocycle on the pulled owner `K.f ≫ q`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component,
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom (g := K.f) (gf₁ := K.f ≫ f₁) (gf₂ := K.f ≫ f₂) (hgf₁ := rfl) (hgf₂ := rfl),
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).pullHom_hom
      K.f q (K.f ≫ q) rfl f₁ f₂ hf₁ hf₂ (K.f ≫ f₁) (K.f ≫ f₂) rfl rfl]

/-- Helper for Lemma 8.11.8: the same component evaluation for the pulled chosen-cover descent
datum is definitionally the overlap morphism over the common owner `K.f ≫ q`. This exposes the
right branch of the transition square on the same owner as the left branch. -/
private theorem chosen_cover_pulled_descent_datum_hom_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V Y : C} (f : V ⟶ U) {q : Y ⟶ V}
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      ((chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K =
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      (chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₂))) := by
  -- Class A: the pulled chosen-cover descent datum component on `K` is the overlap morphism for
  -- the pulled owner `K.f ≫ q`, now sandwiched by the propositional `mapComp'` coherence cells.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component,
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom (g := K.f) (gf₁ := K.f ≫ f₁) (gf₂ := K.f ≫ f₂) (hgf₁ := rfl) (hgf₂ := rfl),
    (chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).pullHom_hom
      K.f q (K.f ≫ q) rfl f₁ f₂ hf₁ hf₂ (K.f ≫ f₁) (K.f ≫ f₂) rfl rfl]

/-- Helper for Lemma 8.11.8: after evaluating the pulled chosen-cover descent datum on the fixed
chosen-cover arrow `K`, applying the secondary-cover descent functor simply pulls that common-owner
overlap morphism further along `L.f`. This is the thin transport adapter needed before comparing
the right branch with the normalized local-overlap square. -/
theorem chosen_cover_transition_pulled_overlap_common_owner
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
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
        (chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
          (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₂))) := by
  -- Class A + cover-descent component: the outer secondary-cover component is pullback along
  -- `L.f` of the inner chosen-cover component, which is the pulled overlap on `K.f ≫ q`
  -- sandwiched by the propositional `mapComp'` coherence cells.
  rw [chosen_cover_pulled_descent_datum_hom_component
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ hf₁ hf₂ K,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  rfl

end

end CategoryTheory
