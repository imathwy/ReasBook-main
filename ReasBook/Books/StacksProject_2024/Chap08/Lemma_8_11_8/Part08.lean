import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part07

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component_expose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) 
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)) := by
  -- Route correction: expose the outer secondary-cover component first, then expose the inner
  -- local-overlap component. This leaves only the literal iterated pullback map to normalize.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K) L]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)
    ((((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂) K]

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem chosen_cover_overlap_map_to_secondary_cover_descent_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))))).hom L).1.app S =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂) L).hom).1.app S := by
  -- Evaluate the normalized secondary-cover comparison on the fixed owner leg `S`.
  simpa using
    congrArg
      (fun ψ ↦ ψ.1.app S)
      (chosen_cover_overlap_map_to_secondary_cover_descent_component
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ K L)

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component_expose_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app S =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L).1.app
        S) := by
  -- Evaluate the already-exposed fixed-`L` equality on the owner leg `S`.
  exact
    congrArg (fun ψ ↦ ψ.1.app S)
      (pullback_cover_target_secondary_cover_exposed_middle_component_expose
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L)

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_raw_shell_eq_local_overlap_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app S =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app S := by
  have hg₁' : g₁ ≫ I₁.base.f = r ≫ q := by
    -- Normalize the first pullback-cover owner to the fixed chosen-cover owner `r ≫ q`.
    change g₁ ≫ (I₁.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₁]
  have hg₂' : g₂ ≫ I₂.base.f = r ≫ q := by
    -- The second pullback-cover owner has the same chosen-cover owner after the same rewrite.
    change g₂ ≫ (I₂.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₂]
  -- Route correction: compare the raw fixed-`K,L,S` shell to the common-owner conjugation
  -- directly, instead of descending the raw and chosen branches together over another slice cover.
  funext α
  simpa [Category.assoc] using
    automorphism_overlap_hom_pull_middle_component_eq_local_overlap_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian
      (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (g := K.f) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
      hg₁' hg₂' (gf₁ := K.f ≫ g₁) (gf₂ := K.f ≫ g₂)
      (by simp) (by simp) L S α

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_to_chosen_middle_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    (((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L).1.app
      S) =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L).1.app
        S) := by
  -- Route correction: compare the exposed raw branch and the chosen branch through the already
  -- isolated common-owner conjugation shell on the fixed owner leg `S`.
  calc
    (((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L).1.app
      S) =
        ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((((J.pseudofunctorOver (Type (max u v))).toDescentData
                  (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app
            S) := by
          symm
          exact
            pullback_cover_target_secondary_cover_exposed_middle_component_expose_app
              (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L S
    _ =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app
        S := by
          exact
            pullback_cover_target_secondary_cover_exposed_middle_raw_shell_eq_local_overlap_conjugation_app
              (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L S
    _ =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L).1.app
        S) := by
          symm
          exact
            pullback_cover_target_secondary_cover_middle_component_as_conjugation_app
              (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L S

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app S =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app S := by
  have hg₁' : g₁ ≫ I₁.base.f = r ≫ q := by
    -- Normalize the first pullback-cover owner to the chosen-cover owner `r ≫ q`.
    change g₁ ≫ (I₁.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₁]
  have hg₂' : g₂ ≫ I₂.base.f = r ≫ q := by
    -- The second pullback-cover branch has the same chosen-cover owner after rewriting.
    change g₂ ≫ (I₂.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₂]
  have hnormalized :=
    chosen_cover_overlap_map_to_secondary_cover_descent_component_app
      (𝒮 := 𝒮) hGerbe hAbelian (q := r ≫ q) g₁ g₂ g₂ hg₁' hg₂' K L S
  have hexposedS :=
    pullback_cover_target_secondary_cover_exposed_middle_component_expose_app
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L S
  have hchosenS :=
    pullback_cover_target_secondary_cover_middle_component_as_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L S
  -- Route correction: the owner-leg transport has now been peeled off explicitly. The remaining
  -- blocker is exactly one sectionwise comparison between the exposed raw middle component and the
  -- already-normalized chosen-cover middle branch.
  calc
    ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app S =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L).1.app
        S) := by
          exact hexposedS
    _ =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L).1.app
        S) := by
          let _ := hnormalized
          exact
            pullback_cover_target_secondary_cover_exposed_middle_to_chosen_middle_app
              (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L S
    _ =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app S := by
          exact hchosenS

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
  -- Route correction: the sheaf-level equality is now only an extensional wrapper. The actual
  -- blocker has been reduced to the owner-leg statement in
  -- `pullback_cover_target_secondary_cover_exposed_middle_component_app`.
  have hexposed :=
    pullback_cover_target_secondary_cover_exposed_middle_component_expose
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
  apply Sheaf.hom_ext
  ext S β
  -- First rewrite the original fixed-`L` component to the raw iterated pullback map exposed by
  -- `hexposed`.
  calc
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L).1.app S)
      β =
        ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((((J.pseudofunctorOver (Type (max u v))).toDescentData
                  (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂))).1.app S)
          β := by
            exact congrFun (congrArg (fun ψ ↦ ψ.1.app S) hexposed) β
    _ =
        (((local_overlap_conjugation_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app S)
          β := by
            exact congrFun
              (pullback_cover_target_secondary_cover_exposed_middle_component_app
                (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L S)
              β

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_expose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))) := by
  -- Expose the outer secondary-cover component first, then expose the inner overlap component.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K) L]
  -- The inner chosen-cover comparison is now a literal pullback along the fixed overlap arrow `K`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) K]

/-- Helper for Lemma 8.11.8: on the self-leg of the fixed secondary-cover refinement `L`, the
source-side descent datum is already the explicit `mapComp'` boundary shell. This isolates the
right-hand normalization from the remaining common-owner comparison. -/
private theorem pullback_cover_target_secondary_cover_source_common_owner_iso_eq_local_overlap_source_iso
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y Z : C} {q : Y ⟶ U}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe
        (x := local_overlap_source_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁))
        (z := local_overlap_target_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₂))
        (q := L.f) (K := L) (g := 𝟙 L.Y) (by simp) =
      local_overlap_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe
        (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (f₁ := K.f ≫ g₁) (f₂ := K.f ≫ g₂)
        (q := L.f) (K := L) (g := 𝟙 L.Y) (by simp) := by
  -- Unfold the overlap source object once; both common-owner source isomorphisms are then the
  -- same `eqToIso ≪≫ pullbackCompComponentIso` package on the self-leg `L`.
  rfl

/-- Helper for Lemma 8.11.8: on the self-leg of the fixed secondary-cover refinement `L`, the
source-side descent datum is already the explicit `mapComp'` boundary shell. This isolates the
right-hand normalization from the remaining common-owner comparison. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_self_leg_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf
          (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁))) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf
            (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁))) := by
  -- Expand the descent datum on the self-leg `L.f` and simplify the identity refinements.
  rw [local_overlap_source_secondary_transition_normalize
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (f₁ := K.f ≫ g₁) (f₂ := K.f ≫ g₂)
    (q := L.f) (g₁ := 𝟙 L.Y) (g₂ := 𝟙 L.Y)]
  -- Nothing else happens on the self-leg except the canonical `mapComp'` shell.
  simp only [Category.comp_id, Category.id_comp]

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
        (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) := by
  -- Route correction: after `hexposed` splits off the source branch, the only unresolved
  -- normalization is this fixed-`L` source boundary component.
  -- First expose the left side to the literal iterated pullback of the chosen-local comparison.
  calc
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))) := by
          exact
            pullback_cover_target_secondary_cover_source_boundary_expose
              (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
    _ =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf
          (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁))) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf
            (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁))) := by
          -- Rewrite the exposed chosen-local shell to the common-owner source comparison on the
          -- self-leg `L`, then identify that source comparison with the normalized secondary-cover
          -- `mapComp'` boundary.
          rw [local_overlap_source_secondary_mapComp'_inv_eq_common_owner_source_iso_inv
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (f₁ := K.f ≫ g₁) (f₂ := K.f ≫ g₂)
            (q := L.f) (K := L) (g := 𝟙 L.Y) (by simp)]
          rw [← pullback_cover_target_secondary_cover_source_common_owner_iso_eq_local_overlap_source_iso
            (𝒮 := 𝒮) hGerbe (g₁ := g₁) (g₂ := g₂) K L]
          simp [Category.assoc]
    _ =
      (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) := by
          symm
          exact
            pullback_cover_target_secondary_cover_source_boundary_self_leg_normalize
              (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ K L

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_left_component_decompose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L =
      (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
  -- Route correction: expose only the source shell on the fixed refinement `L`; this keeps the
  -- blocker at one transport normalization instead of the older paired conjunction proof.
  have hexposed :=
    pullback_cover_target_secondary_cover_left_branch_exposed
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
  have hmiddle :=
    pullback_cover_target_secondary_cover_exposed_middle_component
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  have hsource :=
    pullback_cover_target_secondary_cover_source_boundary_component
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
  -- Once the exposed source branch is replaced by the source boundary term and the exposed middle
  -- branch is replaced by the common-owner conjugation, the target equality is a direct paste.
  calc
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L) := by
          exact hexposed
    _ =
      (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L) := by
          rw [hsource]
    _ =
      (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
          rw [hmiddle]

/-- Helper for Lemma 8.11.8: on the same fixed secondary-cover refinement `L`, the remaining
target shell of the pullback-cover target square should rewrite directly to the target boundary
term of the normalized local-overlap square. -/
private theorem pullback_cover_target_secondary_cover_right_component_decompose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂ ≫
            ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L) := by
  -- Route correction: isolate the target shell separately from the source shell; this keeps the
  -- remaining transport work symmetric and local to one boundary term.
  have hexposed :=
    pullback_cover_target_secondary_cover_right_branch_exposed
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
  -- The exposed form isolates exactly the two pieces needed next: the middle branch is already
  -- normalized by `pullback_cover_target_secondary_cover_middle_normalized`, and the terminal
  -- shell is the target counit component on the same refinement `L`.
  calc
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y)
        =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((chosen_cover_descent_datum
              (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
            ((((localizedSheafToCoverDescentEquivalence (J := J)
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
              (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                ((chosen_local_automorphism_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L) := by
            rw [← pullback_cover_target_secondary_cover_middle_normalized
              (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L]
            rfl
    _ =
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂ ≫
            ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L) := by
        exact hexposed.symm

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_outer_transport_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂)).hom K)).hom L =
      (local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom) ∧
      ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (local_overlap_target_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) =
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂ ≫
            ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L) := by
  -- Route correction: keep the paired theorem as a thin wrapper only; the transport work now
  -- lives in the one-sided source and target shell lemmas above.
  constructor
  · exact
      pullback_cover_target_secondary_cover_left_component_decompose
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  · exact
      pullback_cover_target_secondary_cover_right_component_decompose
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

end CategoryTheory
