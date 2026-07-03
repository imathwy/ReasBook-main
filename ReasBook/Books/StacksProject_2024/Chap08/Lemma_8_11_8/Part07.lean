import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part06

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: on one overlap of the fixed chosen gerbe cover of `U`, the descended
chosen-cover transition is still compared to the explicit overlap morphism by the counit
components on the two branches. This isolates the datum-side middle branch before it is pulled to
the secondary cover. -/
private theorem chosen_cover_descent_datum_overlap_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) =
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂)).hom := by
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
  let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
  let D :=
    automorphism_cover_descent_datum
      (𝒮 := 𝒮) hAbelian S xS
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
      (automorphism_cover_overlap_self (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian S xS)
  let FU := localizedSheafFromCoverDescentData (J := J) S D
  let ε := localizedSheafFromCoverDescentData_counitIso (J := J) S D
  have hcomm := ε.hom.comm q g₁ g₂ hg₁ hg₂
  -- Read the overlap comparison directly from the counit of the fixed-cover descent equivalence.
  simpa [S, xS, D, FU, ε, chosen_cover_descent_datum, chosen_cover_descent_functor,
    chosen_cover_underlying_automorphism_sheaf, chosen_cover_underlying_automorphism_sheaf_cover_iso,
    chosen_cover_underlying_automorphism_descent, Functor.mapIso_hom] using hcomm

/-- Helper for Lemma 8.11.8: the middle morphism of `chosen_cover_descent_datum` can be exposed as
the explicit chosen-cover overlap morphism, with only the pulled counit component isomorphisms on
the two sides. This is the raw source-faithful exposure step needed before secondary-cover
normalization. -/
private theorem chosen_cover_descent_datum_overlap_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂)).inv := by
  let F₁ := ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor
  let F₂ := ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor
  let e₁ := F₁.mapIso
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I₁)
  let e₂ := F₂.mapIso
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I₂)
  have hcomponent :
      e₁.hom ≫
          automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂ =
        (chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫ e₂.hom := by
    -- First expose the middle branch together with the two counit comparison components.
    simpa [F₁, F₂, e₁, e₂] using
      chosen_cover_descent_datum_overlap_component
        (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂
  -- Cancel the right counit component isomorphism to isolate the raw middle morphism itself.
  calc
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ =
        (chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫ 𝟙 _ := by
            simp
    _ =
        (chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫ (e₂.hom ≫ e₂.inv) := by
            rw [e₂.hom_inv_id]
    _ =
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫ e₂.hom) ≫ e₂.inv := by
            simp [Category.assoc]
    _ =
        (e₁.hom ≫
          automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) ≫ e₂.inv := by
              rw [hcomponent]
    _ = e₁.hom ≫
          automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂ ≫
          e₂.inv := by
            simp [Category.assoc]
  -- The remaining term is exactly the explicit-overlap exposure promised in the statement.
  simpa [F₁, F₂, e₁, e₂]

/-- Helper for Lemma 8.11.8: after applying the explicit local-overlap descent equivalence to the
raw chosen-cover overlap comparison, one secondary-cover component displays exactly three visible
factors: the left counit flank, the explicit overlap middle morphism, and the right counit flank.
This freezes the transport-heavy normal form used in the blocked secondary-cover reduction. -/
theorem pullback_cover_target_secondary_cover_mapped_raw_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
      ((chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom q f₁ f₂)).hom K =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom)).hom K ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂)).inv)).hom K) := by
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  have hmap :=
    congrArg (fun ψ ↦ (E.functor.map ψ).hom K)
      (chosen_cover_descent_datum_overlap_raw
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ hf₁ hf₂)
  -- Apply the descent-equivalence functor once, then expose the three factors with
  -- `Functor.map_comp`; this is the exact transport-stable normal form needed later.
  simpa [T, E, Functor.map_comp, Category.assoc] using hmap

/-- Helper for Lemma 8.11.8: on one chosen-local cover arrow attached to a pullback-cover
component, the transported local-object comparison is sent back to the original chosen-local
descent component. This removes the remaining target-side transport shell before the pullback-cover
coherence square is reduced to the normalized chosen-local square. -/
theorem pullback_cover_target_component_to_chosen_local_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (L : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) =
      (chosen_local_automorphism_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom L := by
  -- Evaluate the explicit chosen-local descent equivalence on `L`; this exposes the original
  -- chosen-local descent component and cancels the sheaf-side transport shell.
  rw [← localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y))]
  simpa using
    chosen_local_automorphism_iso_functor_map_component
      (𝒮 := 𝒮) hGerbe hAbelian
      (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (z := I.f ^*[canonicalPullbackChoice 𝒮.p] y) L

/-- Helper for Lemma 8.11.8: on one fixed secondary-cover arrow above a pullback-cover branch,
the transported chosen-local comparison component is already the common-owner conjugation shell on
that same owner `K.f`. This is the source-faithful component bridge needed before passing to a
common refinement of the two pullback-cover branches. -/
private theorem pullback_cover_target_secondary_component_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).hom K =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe K.f (K := K) (g := 𝟙 K.Y)
          (by simp)).hom).hom := by
  -- Route correction: first expose the transported `K`-component as the chosen-local
  -- conjugation map itself; only then replace that chosen local isomorphism by the fixed-owner
  -- self-leg comparison on `K.f`.
  rw [chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
    (z := I.f ^*[canonicalPullbackChoice 𝒮.p] y) K]
  -- Both isomorphisms now live over the same owner `K.f` and have the same endpoints, so
  -- endpoint-independence of conjugation identifies the two sheaf morphisms directly.
  exact
    congrArg Iso.hom <|
      automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K).hom
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe K.f (K := K) (g := 𝟙 K.Y)
          (by simp)).hom

/-- Helper for Lemma 8.11.8: after one further owner refinement `s : Z ⟶ K.Y`, the pulled
`K`-component of the transported chosen-local comparison is exactly the common-owner conjugation
shell over the refined owner `s ≫ K.f`. This is the missing refinement-level bridge needed by the
source-faithful secondary-cover reduction. -/
private theorem pullback_cover_target_secondary_component_bridge_on_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
            (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).hom K) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s)
          (by simp [Category.assoc])).hom).hom := by
  -- Route correction: pull back the already normalized self-leg shell along `s`, and only then
  -- rewrite the owner from `K.f` to the refined common owner `s ≫ K.f`.
  rw [pullback_cover_target_secondary_component_bridge
    (𝒮 := 𝒮) hGerbe hAbelian q y I K]
  simpa using
    chosen_local_common_owner_conjugation_pullback_eq_owner_leg
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := K.f) (K := K) (g := 𝟙 K.Y) (by simp) s

/-- Helper for Lemma 8.11.8: after refining one chosen-local branch by `s : Z ⟶ K.Y`, the pulled
`hom` counit component of the chosen-cover comparison becomes exactly the source boundary shell on
the common owner `s ≫ K.f`. This is the left-flank transport rewrite needed by the blocked
secondary-cover reduction. -/
private theorem chosen_cover_secondary_cover_source_counit_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I.base).hom).hom K =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s)
          (by simp [Category.assoc])).inv.hom).hom := by
  -- Route correction: expose the chosen-cover counit component on the chosen-local cover first,
  -- then reuse the already isolated `mapComp'`-to-common-owner boundary normalization.
  rw [← localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y))
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I.base).hom K]
  simpa [chosen_cover_underlying_automorphism_sheaf,
    chosen_cover_underlying_automorphism_sheaf_cover_iso,
    chosen_cover_underlying_automorphism_descent, chosen_cover_descent_datum,
    chosen_cover_descent_functor, Functor.mapIso_hom] using
    chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := s ≫ K.f) (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (z := I.f ^*[canonicalPullbackChoice 𝒮.p] y) (K := K) s

/-- Helper for Lemma 8.11.8: after the same refinement `s : Z ⟶ K.Y`, the pulled `inv` counit
component of the chosen-cover comparison is exactly the target boundary shell on the common owner
`s ≫ K.f`. This is the right-flank transport rewrite needed by the blocked secondary-cover
reduction. -/
private theorem chosen_cover_secondary_cover_target_counit_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I.base).inv).hom K =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s)
          (by simp [Category.assoc])).hom).hom := by
  -- Route correction: expose the inverse chosen-cover counit component on the chosen-local cover,
  -- then identify that pulled boundary with the canonical common-owner target comparison.
  rw [← localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y))
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I.base).inv K]
  simpa [chosen_cover_underlying_automorphism_sheaf,
    chosen_cover_underlying_automorphism_sheaf_cover_iso,
    chosen_cover_underlying_automorphism_descent, chosen_cover_descent_datum,
    chosen_cover_descent_functor, Functor.mapIso_inv] using
    chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := s ≫ K.f) (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (z := I.f ^*[canonicalPullbackChoice 𝒮.p] y) (K := K) s

/-- Helper for Lemma 8.11.8: once the pullback-cover owner is rewritten to `r ≫ q`, the
`K`-component of the chosen-cover middle morphism already has the source-faithful three-factor
shape "left counit flank, explicit overlap comparison, right counit flank" on the common
secondary cover. -/
private theorem pullback_cover_target_secondary_cover_middle_component_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      ((chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂)).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K) := by
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂
  have hg₁' : g₁ ≫ I₁.base.f = r ≫ q := by
    -- Replace the pullback-cover leg by its base arrow so the generic chosen-cover raw overlap
    -- exposure theorem applies on owner `r ≫ q`.
    change g₁ ≫ (I₁.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₁]
  have hg₂' : g₂ ≫ I₂.base.f = r ≫ q := by
    -- The same owner normalization turns the second branch into the same composite owner.
    change g₂ ≫ (I₂.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₂]
  -- Route correction: package the previously local `hrawMapped` calculation as a standalone
  -- theorem so the remaining blocked proof only has to normalize the three visible factors.
  simpa [T] using
    pullback_cover_target_secondary_cover_mapped_raw_component
      (𝒮 := 𝒮) hGerbe hAbelian (q := r ≫ q)
      (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂ hg₁' hg₂' K

/-- Helper for Lemma 8.11.8: after descending once more to the secondary cover over `K.Y`, the
raw fixed-`K` overlap equality can be read componentwise at a fixed refinement arrow `L`. This is
the exact middle-branch rewrite needed in the nested secondary-cover normalization step. -/
private theorem pullback_cover_target_secondary_cover_middle_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K)).hom L ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
            ((((localizedSheafToCoverDescentEquivalence (J := J)
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂)).hom K)).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
            ((((localizedSheafToCoverDescentEquivalence (J := J)
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
              ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
                (chosen_cover_underlying_automorphism_sheaf_cover_iso
                  (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K)).hom L) := by
  let T₂ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)
  let E₂ := localizedSheafToCoverDescentEquivalence (J := J) T₂
  -- Apply the secondary descent functor to the raw fixed-`K` equality and then read off the
  -- chosen `L`-component.
  simpa [T₂, E₂, Functor.map_comp, Category.assoc] using
    congrArg
      (fun φ ↦ (E₂.functor.map φ).hom L)
      (pullback_cover_target_secondary_cover_middle_component_raw
        (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K)

/-- Helper for Lemma 8.11.8: on a fixed secondary-cover refinement `L`, the exposed three-factor
middle branch from `pullback_cover_target_secondary_cover_middle_component` is already the
normalized chosen-local conjugation component on that same refinement arrow. This packages the
source/target counit rewrites once so the remaining blocker only concerns the outer pullback-cover
transport. -/
theorem pullback_cover_target_secondary_cover_middle_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂)).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K)).hom L) =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
  have hg₁' : g₁ ≫ I₁.base.f = r ≫ q := by
    -- Re-express the pullback-cover source leg over the chosen gerbe cover so the existing
    -- overlap-to-secondary-cover comparison theorem applies verbatim.
    change g₁ ≫ (I₁.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₁]
  have hg₂' : g₂ ≫ I₂.base.f = r ≫ q := by
    -- The target leg has the same owner normalization on the common branch `r ≫ q`.
    change g₂ ≫ (I₂.f ≫ q) = r ≫ q
    simpa [Category.assoc, hg₂]
  -- Route correction: first expose the fixed `L`-component of each nested descent term, then the
  -- whole three-factor branch is exactly the previously packaged chosen-cover overlap component.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K L]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂)).hom K L]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K L]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)
    ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom) K]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)
    (automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂) K]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)
    ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv) K]
  simpa [Functor.map_comp, Category.assoc] using
    chosen_cover_overlap_map_to_secondary_cover_descent_component
      (𝒮 := 𝒮) hGerbe hAbelian (q := r ≫ q) g₁ g₂ g₂ hg₁' hg₂' K L

/-- Helper for Lemma 8.11.8: after passing to the fixed secondary-cover refinement `L`, the
chosen-cover middle branch from `pullback_cover_target_secondary_cover_right_branch_exposed`
already collapses to the common-owner conjugation component. This isolates the reusable part of
the right-branch normalization from the remaining target-boundary transport. -/
private theorem pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
  -- Route correction: first expose the fixed-`L` middle factor as the three visible source/middle/
  -- target pieces, then collapse that packaged shell using the already normalized overlap theorem.
  calc
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          ((((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K)).hom L ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
            ((((localizedSheafToCoverDescentEquivalence (J := J)
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) g₁ g₂)).hom K)).hom L) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
            ((((localizedSheafToCoverDescentEquivalence (J := J)
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
              ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
                (chosen_cover_underlying_automorphism_sheaf_cover_iso
                  (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K)).hom L) := by
        exact
          pullback_cover_target_secondary_cover_middle_component
            (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L
    _ =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom := by
        exact
          pullback_cover_target_secondary_cover_middle_normalized
            (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L

/-- Helper for Lemma 8.11.8: evaluating the already-normalized chosen-cover middle branch on one
owner leg `S : Over L.Y` gives the local-overlap conjugation component directly. This keeps the
later fixed-component proofs at the section level and avoids reopening `Sheaf.hom_ext`. -/
theorem pullback_cover_target_secondary_cover_middle_component_as_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L).1.app S =
      ((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂) L).hom).1.app S := by
  -- Evaluate the sheaf-level normalized middle comparison on the fixed owner leg `S`.
  simpa using
    congrArg
      (fun ψ ↦ ψ.1.app S)
      (pullback_cover_target_secondary_cover_middle_component_as_conjugation
        (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L)

/-- Helper for Lemma 8.11.8: after fixing one secondary-cover arrow `L` and one owner leg
`T : Over L.Y`, pull back the same secondary cover along `T.unop.hom`. The resulting base-site
cover and its slice-site avatar are the source-faithful refinement cover used to compare
sections on `C / L.Y`. -/
private theorem local_overlap_secondary_cover_on_slice
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ) :
    ∃ B : J.Cover T.unop.left,
      ∃ R : (J.over L.Y).Cover T.unop,
        (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left) := by
  let qT := T.unop.hom
  let B : J.Cover T.unop.left :=
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).pullback qT
  let R : (J.over L.Y).Cover T.unop :=
    ⟨(Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left),
      J.overEquiv_symm_mem_over T.unop (B : Sieve T.unop.left) B.condition⟩
  -- This is exactly the slice cover produced from the pulled secondary cover by
  -- `Sieve.overEquiv`.
  exact ⟨B, R, rfl⟩

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled secondary cover over a fixed
owner leg `T : Over L.Y`, the identity leg on `I.Y.left` and the base arrow of the induced
secondary-cover member `Ī.base` determine the same common owner `qI := I.Y.hom ≫ L.f`. This is
the arrow witness needed before any app-level owner transport. -/
private theorem local_overlap_secondary_refinement_member_identity_leg_eq
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ)
    {B : J.Cover T.unop.left}
    {R : (J.over L.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ Y := I.Y.hom ≫ L.f
    let LI :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow :=
      Ī.base
    (𝟙 I.Y.left) ≫ LI.f = qI := by
  -- The induced base arrow `LI := Ī.base` lies over exactly the same owner as the restricted
  -- section object `I.Y`.
  dsimp
  simpa [hĪ, Category.assoc] using congrArg (fun k ↦ I.f.left ≫ k) Ī.base_f

/-- Helper for Lemma 8.11.8: after moving the previous common-owner witness to the opposite slice
owner, the object obtained by applying `Over.map LI.f` to the identity owner of `I.Y.left` is
exactly `I.Y`. This packages the object-level cast needed for owner-transport rewrites on the
pulled secondary cover. -/
private theorem local_overlap_secondary_refinement_member_owner_obj_eq_op
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ)
    {B : J.Cover T.unop.left}
    {R : (J.over L.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ Y := I.Y.hom ≫ L.f
    let LI :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow :=
      Ī.base
    op ((Over.map LI.f).obj (Over.mk (𝟙 I.Y.left))) = op I.Y := by
  -- Move the common-owner equality to the opposite owner object used by `.app`.
  dsimp
  simpa using
    over_map_obj_mk_eq_op Ī.base.f (𝟙 I.Y.left) (I.Y.hom ≫ L.f)
      (local_overlap_secondary_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ L T I Ī hĪ)

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_left_branch_exposed
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
  let T₁ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂
  let T₂ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)
  let E₁ := localizedSheafToCoverDescentEquivalence (J := J) T₁
  let E₂ := localizedSheafToCoverDescentEquivalence (J := J) T₂
  let a :=
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)
  let b :=
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂
  have hK :
      (E₁.functor.map (a ≫ b)).hom K =
        ((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K) := by
    -- First expose the `K`-component of the inner descent functor image.
    simpa [Functor.map_comp, Category.assoc]
  -- Once the `K`-component is split, the outer secondary-cover functor sees a literal
  -- composition, so the fixed-`L` branch is visibly "source shell followed by middle term".
  calc
    (E₂.functor.map ((E₁.functor.map (a ≫ b)).hom K)).hom L
        = (E₂.functor.map (((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K))).hom L := by
            rw [hK]
    _ = (E₂.functor.map ((E₁.functor.map a).hom K)).hom L ≫
        (E₂.functor.map ((E₁.functor.map b).hom K)).hom L := by
            simpa [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.11.8: on a fixed secondary-cover refinement `L`, the target-side branch of
the pullback-cover target square factors into the mapped chosen-cover middle component followed by
the mapped target-shell component. This is the transport-stable normal form used before the
target boundary is rewritten by the secondary-cover counit comparison. -/
theorem pullback_cover_target_secondary_cover_right_branch_exposed
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
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂ ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂)).hom K)).hom L ≫
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
  let T₁ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) g₁ g₂
  let T₂ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ g₁) (K.f ≫ g₂)
  let E₁ := localizedSheafToCoverDescentEquivalence (J := J) T₁
  let E₂ := localizedSheafToCoverDescentEquivalence (J := J) T₂
  let a :=
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂
  let b :=
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)
  have hK :
      (E₁.functor.map (a ≫ b)).hom K =
        ((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K) := by
    -- First expose the `K`-component of the inner chosen-cover branch.
    simpa [Functor.map_comp, Category.assoc]
  -- The outer secondary-cover image now sees the right branch as the visible middle factor
  -- followed by the visible target shell.
  calc
    (E₂.functor.map ((E₁.functor.map (a ≫ b)).hom K)).hom L
        = (E₂.functor.map (((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K))).hom L := by
            rw [hK]
    _ = (E₂.functor.map ((E₁.functor.map a).hom K)).hom L ≫
        (E₂.functor.map ((E₁.functor.map b).hom K)).hom L := by
            simpa [Functor.map_comp, Category.assoc]

end CategoryTheory
