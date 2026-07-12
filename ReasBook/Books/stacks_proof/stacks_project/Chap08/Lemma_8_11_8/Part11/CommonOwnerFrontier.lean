import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentityCoherence
import StacksProject_2024.Chap08.Lemma_8_11_8.Part10

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Local Part11 name for the chosen-cover overlap descent datum.  This exposes the counit
compatibility used in the identity-pullback component calculation without reopening the
localized-sheaf construction. -/
noncomputable def chosen_cover_overlap_descent_datum_part11
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f) :=
  automorphism_cover_descent_datum (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (fun {_Y} _q {_I₁ _I₂} f₁ f₂ ↦
      let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
      let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
      let E :=
        localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂)
      (E.unitIso.app (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)).hom ≫
        E.inverse.map
          (secondary_cover_descent_iso_on_local_overlap
            (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom ≫
        (E.unitIso.app (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)).inv)
    (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian (U := U))
    (fun {_Y} q {_I} g hg ↦
      automorphism_cover_overlap_self (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g hg)
    (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)

/-- Local Part11 name for the counit of the chosen-cover overlap descent datum. -/
noncomputable def chosen_cover_overlap_descent_datum_counitIso_part11
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      chosen_cover_overlap_descent_datum_part11 (𝒮 := 𝒮) hGerbe hAbelian U :=
  localizedSheafFromCoverDescentData_counitIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_cover_overlap_descent_datum_part11 (𝒮 := 𝒮) hGerbe hAbelian U)

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Part11-local counit square for exposing one chosen-cover overlap of the descended
automorphism sheaf.  This is the projection lemma used to keep the common-owner transition square
in the raw descent-datum normal form. -/
private theorem chosen_cover_descent_datum_overlap_component_part11
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
  exact (chosen_cover_overlap_descent_datum_counitIso_part11
    (𝒮 := 𝒮) hGerbe hAbelian U).hom.comm q g₁ g₂ hg₁ hg₂

/-- Part11-local raw overlap normal form for `chosen_cover_descent_datum`.  This hides the
counit square behind a single projection lemma so the transition square can talk only about the
datum's own `hom`. -/
private theorem chosen_cover_descent_datum_overlap_raw_part11
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
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr
    (chosen_cover_descent_datum_overlap_component_part11
      (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂).symm

end

/-- Part11-local raw form of the chosen-cover transition component, placed before the common-owner
frontier so that proof does not depend on later refined Part11 declarations. -/
private theorem chosen_cover_descent_transition_component_iso_hom_raw_frontier
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom =
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
        (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I).inv := by
  haveI : (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [chosen_cover_descent_transition_component_mapped_normalized]
  simp only [Functor.map_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component,
    chosen_cover_pullback_to_local_object_component_iso_hom]
  rfl

/-- Normal form for the left branch of the common-owner transition square before applying the
local-overlap descent functor. -/
noncomputable def chosen_cover_transition_common_owner_left_morphism
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :=
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₁)).hom ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
        (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁])
        (_hf₂ := by rw [Category.assoc, hf₂])) ≫
      (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))

/-- Normal form for the right branch of the common-owner transition square before applying the
local-overlap descent functor. -/
noncomputable def chosen_cover_transition_common_owner_right_morphism
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :=
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      (chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
      (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))

/-- Raw descent-datum normal form for the left branch of the common-owner transition square.
Compared with `chosen_cover_transition_common_owner_left_morphism`, this keeps the chosen-cover
overlap as `(chosen_cover_descent_datum V).hom`; the counit expansion is handled separately by
`chosen_cover_descent_datum_overlap_raw_part11`. -/
noncomputable def chosen_cover_transition_common_owner_raw_left_morphism
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :=
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).hom
        (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))

/-- Remaining raw naturality square for the common-owner transition.  This is the smaller §5.2
interface left after the chosen-cover overlap counit plumbing has been peeled off. -/
theorem chosen_cover_transition_common_owner_raw_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    chosen_cover_transition_common_owner_raw_left_morphism
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K =
      chosen_cover_transition_common_owner_right_morphism
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K := by
  -- Remaining §5.2 core: the componentwise naturality square for the transition components,
  -- before the chosen-cover overlap is expanded through the counit normal form.
  sorry

/-- Normal-form core for the common-owner transition square before projecting to a secondary
cover component.  This is the small API boundary for the remaining pullback-cover specialization:
the reduced live-`L` theorem below should only map this equality through the local-overlap descent
functor and evaluate at `L`. -/
theorem chosen_cover_transition_common_owner_normal_form_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    chosen_cover_transition_common_owner_left_morphism
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K =
      chosen_cover_transition_common_owner_right_morphism
        (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K := by
  have hraw :=
    chosen_cover_transition_common_owner_raw_square
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K
  rw [chosen_cover_transition_common_owner_raw_left_morphism,
    chosen_cover_descent_datum_overlap_raw_part11
      (𝒮 := 𝒮) hGerbe hAbelian (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂])] at hraw
  simpa only [chosen_cover_transition_common_owner_left_morphism,
    chosen_cover_transition_common_owner_right_morphism, Category.assoc] using hraw

/-- Fully split live-`L` normal form for the common-owner transition square.  This is the
component-level core left after the local-overlap descent functor component has been evaluated and
the outer pullback along `L.f` has been distributed over the named left/right normal forms. -/
theorem chosen_cover_transition_common_owner_reduced_component_square
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
  let S := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  have hnormal :=
    chosen_cover_transition_common_owner_normal_form_square
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K
  have hcomponent :=
    congrArg
      (fun m ↦ ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map m).hom L)
      hnormal
  simpa only [S, chosen_cover_transition_common_owner_left_morphism,
    chosen_cover_transition_common_owner_right_morphism,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Category.assoc] using hcomponent

/-- Helper for Lemma 8.11.8: the common-owner transition square after applying the
local-overlap descent functor and taking one fixed secondary-cover component `L`. This is the
live-`L` interface between the old pullback-cover target normalization and the datum-level
frontier below; the main theorem should only assemble this component square by faithful descent.
-/
theorem chosen_cover_transition_local_overlap_component_square
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
    let S := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
      (chosen_cover_transition_common_owner_left_morphism
        hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K)).hom L
    =
      ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_cover_transition_common_owner_right_morphism
          hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K)).hom L := by
  simpa only [chosen_cover_transition_common_owner_left_morphism,
    chosen_cover_transition_common_owner_right_morphism,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Category.assoc] using
    chosen_cover_transition_common_owner_reduced_component_square
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L

/-- Helper for Lemma 8.11.8: the chosen-cover transition square on the common owner `K.f ≫ q`,
before pulling the whole equality one step further along a secondary-cover arrow `L`. This is the
member-level core left after the local-overlap descent functor component has been peeled away. -/
theorem chosen_cover_transition_common_owner_frontier_from_pullback_cover
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁)) ≫
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₁).op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I₁)).hom ≫
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
          (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
          (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])) ≫
        (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂)))
    =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁)) ≫
      (chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian f).hom (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂]) ≫
      (((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂)) := by
  let S := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  exact chosen_cover_transition_local_overlap_component_square
    hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L

end CategoryTheory
