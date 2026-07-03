import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part10

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: rewrite the exact named-input specialization of the old
pullback-cover theorem to the current chosen-cover frontier. This keeps the theorem boundary
separate from the literal `Cover.Arrow` normalization step. -/
private theorem chosen_cover_transition_frontier_literal_boundary
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) ≫
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
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
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  have hInputs :=
    chosen_cover_transition_named_inputs_exact_boundary_data
      (𝒮 := 𝒮) hGerbe q f₁ f₂ K
  have hExact :=
    chosen_cover_transition_pullback_cover_refined_specialization_exact
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L
  rcases hInputs with
    ⟨hI₁_base, hI₁_owner, hI₁_precomp_base, hI₁_precomp_owner,
      hI₂_base, hI₂_owner, hI₂_precomp_base, hI₂_precomp_owner⟩
  -- Route correction: this theorem is now only the wrapper that extracts the explicit projection
  -- equalities and passes them to the isolated theorem-boundary adapter.
  exact
    chosen_cover_transition_exact_specialization_literal_boundary
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L
      hI₁_base hI₁_owner hI₁_precomp_base hI₁_precomp_owner
      hI₂_base hI₂_owner hI₂_precomp_base hI₂_precomp_owner
      hExact

/-- Helper for Lemma 8.11.8: once the two chosen-cover branches are rewritten to the literal
pullback-cover frontiers, both sides are the same specialization of the normalized
pullback-cover component theorem at the common owner `(K.f ≫ q)`. This is the shared
post-rewrite bridge that replaces the previous one-sided adapter chain. -/
private theorem chosen_cover_transition_frontier_from_pullback_cover_refined_specialization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) ≫
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
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
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  -- The current frontier theorem is now only a wrapper around the literal-boundary adapter.
  exact
    chosen_cover_transition_frontier_literal_boundary
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L

/-- Helper for Lemma 8.11.8: once the two chosen-cover branches are rewritten to the literal
pullback-cover frontiers, both sides are the same specialization of the normalized
pullback-cover component theorem at the common owner `(K.f ≫ q)`. This is the shared
post-rewrite bridge that replaces the previous one-sided adapter chain. -/
private theorem chosen_cover_transition_reduced_frontier_specializes_pullback_cover_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) ≫
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
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
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  -- The old frontier theorem is now only a wrapper around the direct theorem-boundary adapter.
  exact
    chosen_cover_transition_frontier_from_pullback_cover_refined_specialization
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L

/-- Helper for Lemma 8.11.8: once the two chosen-cover branches are rewritten to the literal
pullback-cover frontiers, both sides are the same specialization of the normalized
pullback-cover component theorem at the common owner `(K.f ≫ q)`. This is the shared
post-rewrite bridge that replaces the previous one-sided adapter chain. -/
private theorem chosen_cover_transition_reduced_branches_match_pullback_cover_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) ≫
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
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
              (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂))).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  -- The large branch theorem is now only a wrapper around the explicit boundary adapter above.
  exact
    chosen_cover_transition_reduced_frontier_specializes_pullback_cover_component
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L

/-- Helper for Lemma 8.11.8: once both chosen-cover branches are normalized on the fixed
secondary-cover refinement `L`, the remaining comparison is exactly the common-owner secondary
descent square on `(K.f ≫ f₁, K.f ≫ f₂)`. This packages the final source-faithful square used by
`chosen_cover_transition_component_square` after the two blocked branch decompositions are proved. -/
private theorem chosen_cover_transition_common_owner_component_normalized_specialization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂) L).hom =
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂) L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) := by
  -- Route correction: specialize the already normalized common-owner square directly at the
  -- chosen-cover branch data instead of re-deriving one-sided branch adapters first.
  simpa using
    local_overlap_secondary_descent_square_at_refinement
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
      (K.f ≫ f₁) (K.f ≫ f₂) L

/-- Helper for Lemma 8.11.8: once both chosen-cover branches are normalized on the fixed
secondary-cover refinement `L`, the remaining comparison is exactly the common-owner secondary
descent square on `(K.f ≫ f₁, K.f ≫ f₂)`. This packages the final source-faithful square used by
`chosen_cover_transition_component_square` after the two blocked branch decompositions are proved. -/
private theorem chosen_cover_transition_common_owner_secondary_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) ≫
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂) L).hom =
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂) L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) := by
  -- Reuse the direct chosen-cover specialization so the square proof below depends only on the
  -- stabilized common-owner frontier.
  exact
    chosen_cover_transition_common_owner_component_normalized_specialization
      (𝒮 := 𝒮) hGerbe hAbelian
      f f₁ f₂ K L

/-- Helper for Lemma 8.11.8: the chosen-cover component comparisons satisfy the descent square on
overlaps of the chosen cover of `V`, so they package into one isomorphism of descent data. -/
private theorem chosen_cover_transition_component_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂)).hom K =
    (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ ≫
        ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K := by
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- Route correction: after evaluating on the chosen-cover arrow `K`, descend once more along
  -- the common secondary cover so only the exposed common-owner normalization remains.
  apply Functor.map_injective E.functor
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  -- First expose both branches as literal compositions on the fixed secondary-cover refinement.
  rw [chosen_cover_transition_left_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  rw [chosen_cover_transition_right_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  -- Route correction: reduce both branches straight to the literal pullback-cover frontiers and
  -- compare those frontiers by the shared normalized pullback-cover specialization.
  rw [chosen_cover_transition_left_component_reduced_to_pullback_input
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  rw [chosen_cover_transition_right_component_reduced_to_pullback_input
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  exact
    chosen_cover_transition_reduced_branches_match_pullback_cover_component_normalized
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L

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
  let T := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- The remaining transport shell is only the chosen-cover descent equivalence on `C / Y`.
  apply Functor.map_injective E.functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  simpa [T, E, Functor.map_comp, Category.assoc] using
    chosen_cover_transition_component_square
      (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K

/-- Helper for Lemma 8.11.8: package the componentwise chosen-cover pullback comparisons into one
datum-side transition isomorphism on the chosen cover of `V`. -/
private noncomputable def chosen_cover_descent_transition_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :
    chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian f ≅
      chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian V :=
  Pseudofunctor.DescentData.isoMk
    (fun I ↦ chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I)
    (fun q f₁ f₂ hf₁ hf₂ ↦
      chosen_cover_descent_transition_component_coherence
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
private theorem chosen_cover_descent_transition_id_component_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.map
      ((chosen_cover_descent_transition_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom)).hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom) ≫
            ((chosen_cover_pullback_to_local_object_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (q := I.f)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I).inv) := by
  -- First expose the fixed-`K` component of the mapped transition on the chosen cover of `I.Y`.
  rw [chosen_cover_descent_transition_component_mapped_normalized
    (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U) I K]
  -- Then rewrite the mixed local comparison to the literal pullback comparison on `C / K.Y`.
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U) I K]
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I.f)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) K]
  -- The remaining shell is just the pullback of the explicit identity-pullback comparison,
  -- followed by the inverse chosen-cover counit comparison.
  rw [← Functor.map_comp]

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
private theorem chosen_cover_descent_transition_id_composite_to_identity_pullback
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom) ≫
          ((chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := I.f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom)) =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (q := 𝟙 I.Y)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom) := by
  -- Route correction: unfold only the transport shell coming from
  -- `localizedSheafTransportIsoOfCoverDescentIso`; the comparison itself stays on the source
  -- chosen-cover pullback route.
  simp [chosen_cover_pulled_component_composite_pullback_iso,
    chosen_cover_pullback_to_local_object_iso, localizedSheafTransportIsoOfCoverDescentIso,
    Category.assoc]

/-- Helper for Lemma 8.11.8: after normalizing the identity-pullback comparison on the fixed
secondary-cover arrow `K`, the remaining pulled inverse chosen-cover counit is the inverse of the
same local comparison component, so the endgame is a single inverse cancellation. -/
private theorem chosen_cover_descent_transition_id_pulled_cover_iso_inv_as_component_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I).inv) =
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe I.Y K)
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).inv) ≫
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian I.Y K).inv) := by
  -- Route correction: first expose the fixed `K`-component of the generic pullback comparison on
  -- the inverse side; only then simplify that component to the local inverse comparison followed
  -- by the chosen-cover counit on `I.Y`.
  rw [chosen_cover_pullback_to_local_object_component_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I.f)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) K]
  simp [chosen_cover_underlying_automorphism_sheaf,
    chosen_cover_underlying_automorphism_sheaf_cover_iso,
    chosen_cover_underlying_automorphism_descent, chosen_cover_descent_datum,
    chosen_cover_descent_functor, Functor.mapIso_inv, Category.assoc]

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
private theorem chosen_cover_descent_transition_id_inner_composite_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (q := 𝟙 I.Y)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom) =
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian I.Y K).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe I.Y K)
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom) := by
  -- Route correction: isolate the refined-arrow normalization at `I.Y` first, so the remaining
  -- identity blocker only has to compare the outer chosen-cover comparison with its inverse.
  simpa using
    chosen_cover_identity_pullback_component_normalized
      (𝒮 := 𝒮) hGerbe hAbelian
      (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) K

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
private theorem chosen_cover_descent_transition_id_component_is_id
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom) ≫
            ((chosen_cover_pullback_to_local_object_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (q := I.f)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I).inv) =
      𝟙 _ := by
  -- Route correction: first replace the composite-pullback shell by the literal
  -- identity-pullback comparison on `I.Y`, then rewrite the remaining pulled inverse chosen-cover
  -- counit as the inverse local comparison component and cancel.
  calc
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom) ≫
            ((chosen_cover_pullback_to_local_object_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (q := I.f)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I).inv) =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := 𝟙 I.Y)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I).inv) := by
        rw [chosen_cover_descent_transition_id_composite_to_identity_pullback
          (𝒮 := 𝒮) hGerbe hAbelian U I K]
    _ =
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian I.Y K).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe I.Y K)
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I).inv) := by
        rw [chosen_cover_descent_transition_id_inner_composite_normalized
          (𝒮 := 𝒮) hGerbe hAbelian U I K]
    _ =
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian I.Y K).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe I.Y K)
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).hom) ≫
        (((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe I.Y K)
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))).inv) ≫
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian I.Y K).inv)) := by
        rw [chosen_cover_descent_transition_id_pulled_cover_iso_inv_as_component_inv
          (𝒮 := 𝒮) hGerbe hAbelian U I K]
    _ = 𝟙 _ := by
        simp [Category.assoc]

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
theorem chosen_cover_descent_transition_iso_id_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) :
    (chosen_cover_descent_transition_iso
      (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).hom = 𝟙 _ := by
  -- Route correction: after the overlap square is packaged, the identity case should be proved
  -- componentwise on the chosen cover of `U`, using the normalized identity-pullback comparison on
  -- each fixed chosen-cover arrow.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  -- The `isoMk` package records the `I`-component literally by the chosen component isomorphism.
  change
    (chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) I).hom = 𝟙 _
  let E := localizedSheafToCoverDescentEquivalence (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)
  -- Apply the chosen-cover descent equivalence on `C / I.Y`; this removes the outer sheaf
  -- transport and leaves only the normalized identity-pullback component.
  apply Functor.map_injective E.functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- Rewrite the fixed-`K` component to one explicit pullback shell on `C / K.Y`.
  rw [chosen_cover_descent_transition_id_component_shell
    (𝒮 := 𝒮) hGerbe hAbelian U I K]
  -- The remaining transport-heavy component identity is now isolated in one fixed-`I`, fixed-`K`
  -- helper, so this theorem only packages the descent-data extensionality shell.
  exact
    chosen_cover_descent_transition_id_component_is_id
      (𝒮 := 𝒮) hGerbe hAbelian U I K

/-- Helper for Lemma 8.11.8: the identity branch of the transported chosen-cover transition
reduces, after applying the chosen-cover descent equivalence, to proving that the datum-side
transition for `𝟙 U` is already the identity morphism. -/
private theorem chosen_cover_transport_transition_id_reduction
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) :
    chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)) =
      (J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ↔
    (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).hom =
      𝟙 _ := by
  constructor
  · intro h
    -- Apply the chosen-cover descent functor to both sides so the transport shell disappears.
    have hmap :=
      congrArg
        (fun i ↦
          (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map i.hom)
        h
    -- The left image is the packaged datum-side transition, while the right image is the
    -- identity pullback comparison already normalized earlier.
    rw [chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U))] at hmap
    rw [chosen_cover_descent_functor_map_overMapPullbackId_hom
      (𝒮 := 𝒮) hGerbe hAbelian U] at hmap
    exact hmap
  · intro h
    let E := localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    apply Iso.ext
    -- The chosen-cover descent functor is faithful because it is the functor part of an
    -- equivalence, so equality of the transported sheaf morphisms is detected after descent.
    apply Functor.map_injective E.functor
    change
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
          (chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U))).hom =
        (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
          ((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).hom
    rw [chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U))]
    rw [chosen_cover_descent_functor_map_overMapPullbackId_hom
      (𝒮 := 𝒮) hGerbe hAbelian U]
    exact h

/-- Helper for Lemma 8.11.8: once the datum-side transition
`chosen_cover_descent_transition_iso` is fixed, transporting it back through the chosen-cover
descent equivalence yields the required identity and cocycle laws on the slice sheaves. This
isolates the remaining pullback-transition blocker to one datum-level normalization statement. -/
/-- Helper for Lemma 8.11.8: if the datum-side identity transition on the chosen cover of `U`
is already the identity, then transporting it back to the slice sheaf on `C / U` gives exactly
the canonical `overMapPullbackId` comparison. This packages the faithful-descent reduction from
`chosen_cover_transport_transition_id_reduction` into a reusable one-line bridge. -/
theorem chosen_cover_transport_transition_id_of_descent_identity
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (hidentity :
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).hom =
        𝟙 _) :
    chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)) =
      (J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) := by
  -- Route correction: the sheaf-side identity law is equivalent to the datum-side identity after
  -- applying the chosen-cover descent functor, so the already-isolated reduction closes it.
  exact
    (chosen_cover_transport_transition_id_reduction
      (𝒮 := 𝒮) hGerbe hAbelian U).2 hidentity

/-- Helper for Lemma 8.11.8: the transported cocycle law on slice sheaves can be checked after
applying the chosen-cover descent functor on `C / W`. This isolates the remaining composition
blocker to one descent-data equality, without reopening the outer transport shell. -/
theorem chosen_cover_transport_transition_comp_reduction
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullbackComp (Type (max u v)) g f).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
      chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)) =
      (J.overMapPullback (Type (max u v)) g).mapIso
        (chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian (f := f)
          (chosen_cover_descent_transition_iso
            (𝒮 := 𝒮) hGerbe hAbelian f)) ≪≫
        chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian (f := g)
          (chosen_cover_descent_transition_iso
            (𝒮 := 𝒮) hGerbe hAbelian g) ↔
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
          chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f))).hom) =
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        ((((J.overMapPullback (Type (max u v)) g).mapIso
          (chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian f)) ≪≫
          chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := g)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian g)).hom) := by
  constructor
  · intro hcomp
    -- Apply the faithful chosen-cover descent functor to both isomorphisms so the remaining
    -- blocker is recorded entirely in descent data.
    exact
      congrArg
        (fun i ↦ (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map i.hom)
        hcomp
  · intro hcomp
    let E := localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W)
    apply Iso.ext
    -- The chosen-cover descent functor is faithful because it is the functor part of an
    -- equivalence, so equality after descent already gives the desired sheaf-side cocycle law.
    apply Functor.map_injective E.functor
    simpa [E, chosen_cover_descent_functor] using hcomp

/-- Helper for Lemma 8.11.8: after the three
`chosen_cover_transport_transition_functor_map` rewrites in the composition branch, the remaining
descent-data equality is exactly the pullback-composition comparison on the chosen cover of `W`.
This isolates the final cocycle normalization away from the sheaf-side transport shell. -/
private theorem chosen_cover_pullFunctorCompIso_component_specialization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)).hom).hom I =
    ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian g).hom).hom I := by
  -- Route correction: the remaining cocycle blocker is no longer a frontier rewrite. Freeze the
  -- chosen-cover arrow `I`, specialize `Pseudofunctor.DescentData.pullFunctorCompIso` to the
  -- chosen-cover descent datum of `U`, and rewrite both visible branches to that exact datum
  -- boundary before cancelling the common shell.
  let T := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- First descend once more on `C / I.Y`; this turns the fixed-`I` equality of sheaf morphisms
  -- into a componentwise equality on the chosen secondary cover of `I.Y`.
  apply Functor.map_injective E.functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- First normalize both visible branches to the explicit fixed-`K` pullback shells on the
  -- common owner over `K.Y`.
  rw [chosen_cover_descent_transition_component_mapped_normalized
    (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f) I K]
  rw [chosen_cover_descent_transition_component_mapped_normalized
    (𝒮 := 𝒮) hGerbe hAbelian (f := g)
    I K]
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f) I K]
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (𝒮 := 𝒮) hGerbe hAbelian (f := g) I K]
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I.f ≫ g ≫ f)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I.f ≫ g)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  -- The remaining blocker is now exactly the `pullFunctorCompIso` specialization for the chosen
  -- cover of `U`, after both sides have been rewritten to the direct-vs-iterated pullback shell.
  rw [← Functor.map_comp]
  let e :=
    Pseudofunctor.DescentData.pullFunctorCompIso
      (F := J.pseudofunctorOver (Type (max u v)))
      (f := fun JI : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ JI.f)
      (p := f)
      (f' := fun JI : ((chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).pullback f).Arrow ↦ JI.f)
      (α := fun JI ↦ JI.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (Over.mk f))
      (q := I.f ≫ g)
      (f'' := fun JI :
        (((chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).pullback f).pullback (I.f ≫ g)).Arrow ↦ JI.f)
      (β := fun JI ↦ JI.base)
      (q' := fun _ ↦ 𝟙 _)
      (w' := localized_cover_descent_pullbackDatum_w (J := J) (U := V)
        ((chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).pullback f) (Over.mk (I.f ≫ g)))
      (r := I.f ≫ g ≫ f)
      (r' := fun _ ↦ 𝟙 _)
      (hr := by rfl)
      (hr' := by intro JI; simp [Category.assoc])
  -- The direct-vs-iterated pullback comparison is exactly the fixed `I`, fixed `K` component of
  -- the specialized `pullFunctorCompIso` on the chosen-cover descent datum of `U`.
  simpa [T, E, Functor.map_comp, Category.assoc, chosen_cover_descent_functor,
    chosen_cover_descent_datum, chosen_cover_pulled_descent_datum] using
    ((e.app (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U)).hom.hom K)

/-- Helper for Lemma 8.11.8: after the three
`chosen_cover_transport_transition_functor_map` rewrites in the composition branch, the remaining
descent-data equality is exactly the pullback-composition comparison on the chosen cover of `W`.
This isolates the final cocycle normalization away from the sheaf-side transport shell. -/
private theorem chosen_cover_transport_transition_comp_after_functor_map_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)).hom).hom I =
    ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian g).hom).hom I := by
  -- The fixed-`I` cocycle equality is now isolated in the exact helper that records the intended
  -- `pullFunctorCompIso` specialization route.
  exact
    chosen_cover_pullFunctorCompIso_component_specialization
      (𝒮 := 𝒮) hGerbe hAbelian f g I

/-- Helper for Lemma 8.11.8: after the three
`chosen_cover_transport_transition_functor_map` rewrites in the composition branch, the remaining
descent-data equality is exactly the pullback-composition comparison on the chosen cover of `W`.
This isolates the final cocycle normalization away from the sheaf-side transport shell. -/
theorem chosen_cover_transport_transition_comp_after_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)).hom =
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian g).hom := by
  -- Route correction: reduce the remaining cocycle comparison to each fixed chosen-cover arrow of
  -- `W`; this exposes the exact `pullFunctorCompIso` specialization still missing and prevents the
  -- unresolved transport from leaking back into the outer descent-data shell.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  -- The unresolved datum-side cocycle is now isolated at one fixed cover member `I`.
  exact
    chosen_cover_transport_transition_comp_after_functor_map_component
      (𝒮 := 𝒮) hGerbe hAbelian f g I

end CategoryTheory
