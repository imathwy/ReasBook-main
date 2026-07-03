import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part09

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: after exposing the chosen-cover overlap morphism on the common owner
`K.f ≫ q`, the secondary-cover refinement `L` sees exactly the raw three-factor overlap normal
form already packaged earlier. This isolates the middle branch from the remaining boundary-shell
comparison. -/
private theorem chosen_cover_transition_middle_mapped_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂)).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
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
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) := by
  -- First expose the `K`-component of the chosen-cover overlap datum as the overlap morphism on
  -- the common owner `K.f ≫ q`, and then reuse the already-proved raw secondary-cover normal
  -- form on that owner.
  rw [chosen_cover_descent_datum_hom_component
    (𝒮 := 𝒮) hGerbe hAbelian f₁ f₂ K]
  simpa using
    pullback_cover_target_secondary_cover_mapped_raw_component
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := K.f ≫ q) (f₁ := K.f ≫ f₁) (f₂ := K.f ≫ f₂) (K := L)

/-- Helper for Lemma 8.11.8: after refining the fixed chosen-cover component `K` by one
secondary-cover arrow `L`, the left branch of the chosen-cover transition square visibly splits
into the exposed pulled transition shell followed by the exposed middle overlap term. This is the
secondary-cover analogue of the earlier branch-exposure step used to keep the remaining blocker at
one common-owner normalization. -/
theorem chosen_cover_transition_left_branch_exposed
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂)).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂)).hom K)).hom L) := by
  let T₁ := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y
  let T₂ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  let E₁ := localizedSheafToCoverDescentEquivalence (J := J) T₁
  let E₂ := localizedSheafToCoverDescentEquivalence (J := J) T₂
  let a :=
    ((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
      ((chosen_cover_descent_transition_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom)
  let b := (chosen_cover_descent_datum
    (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂
  have hK :
      (E₁.functor.map (a ≫ b)).hom K =
        ((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K) := by
    -- First expose the fixed `K`-component of the inner chosen-cover branch.
    simpa [Functor.map_comp, Category.assoc]
  -- Once the `K`-component is exposed as a literal composition, the secondary-cover functor sees
  -- exactly the left shell followed by the middle overlap factor.
  calc
    (E₂.functor.map ((E₁.functor.map (a ≫ b)).hom K)).hom L
        = (E₂.functor.map (((E₁.functor.map a).hom K) ≫
            ((E₁.functor.map b).hom K))).hom L := by
            rw [hK]
    _ =
      (E₂.functor.map ((E₁.functor.map a).hom K)).hom L ≫
        (E₂.functor.map ((E₁.functor.map b).hom K)).hom L := by
          simpa [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.11.8: after the same secondary-cover refinement, the right branch of the
chosen-cover transition square visibly splits into the exposed middle overlap term followed by the
exposed target shell. This keeps the final square proof symmetric and leaves only the common-owner
normalization unresolved. -/
theorem chosen_cover_transition_right_branch_exposed
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ ≫
        ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_pulled_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂)).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L) := by
  let T₁ := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y
  let T₂ := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  let E₁ := localizedSheafToCoverDescentEquivalence (J := J) T₁
  let E₂ := localizedSheafToCoverDescentEquivalence (J := J) T₂
  let a := (chosen_cover_pulled_descent_datum
    (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂
  let b :=
    ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
      ((chosen_cover_descent_transition_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom)
  have hK :
      (E₁.functor.map (a ≫ b)).hom K =
        ((E₁.functor.map a).hom K) ≫ ((E₁.functor.map b).hom K) := by
    -- First expose the fixed `K`-component of the inner chosen-cover branch.
    simpa [Functor.map_comp, Category.assoc]
  -- The same secondary-cover passage now sees the right branch as the exposed middle factor
  -- followed by the exposed target shell.
  calc
    (E₂.functor.map ((E₁.functor.map (a ≫ b)).hom K)).hom L
        = (E₂.functor.map (((E₁.functor.map a).hom K) ≫
            ((E₁.functor.map b).hom K))).hom L := by
            rw [hK]
    _ =
      (E₂.functor.map ((E₁.functor.map a).hom K)).hom L ≫
        (E₂.functor.map ((E₁.functor.map b).hom K)).hom L := by
          simpa [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.11.8: on the fixed secondary-cover refinement `L`, the exposed left shell
is literally the pullback of the `K`-component along `L.f`. This isolates the remaining blocker to
matching that pulled component with the existing pullback-cover source branch. -/
private theorem chosen_cover_transition_left_shell_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K) := by
  -- Expose the outer secondary-cover component so the shell becomes a literal pullback along
  -- `L.f`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K) L]

/-- Helper for Lemma 8.11.8: symmetrically, on the fixed refinement `L`, the exposed right shell
is literally the pullback of the `K`-component along `L.f`. This removes one outer transport layer
before matching the branch with the existing pullback-cover target decomposition. -/
private theorem chosen_cover_transition_right_shell_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K) := by
  -- Expose the outer secondary-cover component so the target shell is also a literal pullback
  -- along `L.f`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
        ((chosen_cover_descent_transition_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K) L]

/-- Helper for Lemma 8.11.8: after exposing the outer `L.f` pullback shell and normalizing the
fixed `K`-component of the left chosen-cover transition, the remaining left shell is literally the
secondary-cover pullback of the normalized mixed-cover comparison together with the pulled inverse
chosen-cover counit. This isolates the residual mismatch to the existing pullback-cover source
decomposition API. -/
private theorem chosen_cover_transition_left_shell_specializes_pullback_source_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) := by
  -- First expose the outer secondary-cover component, then normalize the fixed `K`-component.
  rw [chosen_cover_transition_left_shell_component
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  rw [chosen_cover_descent_transition_component_mapped_normalized
    (𝒮 := 𝒮) hGerbe hAbelian f I₁ K]

/-- Helper for Lemma 8.11.8: symmetrically, after exposing the outer `L.f` pullback shell and
normalizing the fixed `K`-component of the right chosen-cover transition, the remaining right
shell is literally the secondary-cover pullback of the normalized mixed-cover comparison together
with the pulled inverse chosen-cover counit. This isolates the residual mismatch to the existing
pullback-cover target decomposition API. -/
private theorem chosen_cover_transition_right_shell_specializes_pullback_target_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  -- First expose the outer secondary-cover component, then normalize the fixed `K`-component.
  rw [chosen_cover_transition_right_shell_component
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  rw [chosen_cover_descent_transition_component_mapped_normalized
    (𝒮 := 𝒮) hGerbe hAbelian f I₂ K]

/-- Helper for Lemma 8.11.8: on a fixed secondary-cover refinement `L`, the entire exposed left
branch of the chosen-cover transition square should collapse to the source boundary term of the
normalized local-overlap square followed by the common-owner conjugation isomorphism. This is the
exact source-side specialization of the earlier pullback-cover decomposition that Agent C asked to
reuse instead of reproving the boundary shell from scratch. -/
theorem chosen_cover_transition_left_component_reduced_to_pullback_input
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂)).hom K)).hom L) =
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
                (𝒮 := 𝒮) hGerbe hAbelian V I₂)).inv)).hom L) := by
  -- First expose the normalized left shell on the common owner `K.f ≫ q`.
  rw [chosen_cover_transition_left_shell_specializes_pullback_source_shell
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  -- Then rewrite the middle branch to the literal raw overlap composite on the same owner.
  rw [chosen_cover_transition_middle_mapped_raw
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]

/-- Helper for Lemma 8.11.8: symmetrically, the exposed right branch reduces to the literal
pullback-cover target-decomposition input once the normalized target shell and common-owner middle
overlap term have both been exposed. This isolates the remaining blocker to a pure theorem-input
matching step. -/
theorem chosen_cover_transition_right_component_reduced_to_pullback_input
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_pulled_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂)).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L) =
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
  -- First expose the right shell as the pulled normalized target comparison.
  rw [chosen_cover_transition_right_shell_specializes_pullback_target_shell
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]
  -- Then rewrite the middle factor to the literal common-owner overlap term.
  rw [chosen_cover_transition_pulled_overlap_common_owner
    (𝒮 := 𝒮) hGerbe hAbelian f f₁ f₂ K L]

/-- Helper for Lemma 8.11.8: on a fixed secondary-cover refinement `L`, the entire exposed left
branch of the chosen-cover transition square should collapse to the source boundary term of the
normalized local-overlap square followed by the common-owner conjugation isomorphism. This is the
exact source-side specialization of the earlier pullback-cover decomposition that Agent C asked to
reuse instead of reproving the boundary shell from scratch. -/
private theorem chosen_cover_transition_left_branch_change_target
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} {q : Y ⟶ V}
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (_f₁ : Y ⟶ I₁.Y) (_f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ _f₁) (K.f ≫ _f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (chosen_cover_pullback_to_local_object_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := I₁.f ≫ f)
            (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₁) K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv)) := by
  -- Route correction: rewrite only the mixed factor so the remaining blocker is the literal
  -- specialization of the older pullback-cover decomposition theorem.
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (𝒮 := 𝒮) hGerbe hAbelian f I₁ K]

/-- Helper for Lemma 8.11.8: the symmetric right-branch change-target step rewrites only the
mixed factor to the literal pullback-cover component, leaving one theorem-input specialization
step as the sole remaining blocker. -/
private theorem chosen_cover_transition_right_branch_change_target
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} {q : Y ⟶ V}
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (_f₁ : Y ⟶ I₁.Y) (_f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ _f₁) (K.f ≫ _f₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂ K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
          (chosen_cover_pullback_to_local_object_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := I₂.f ≫ f)
            (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₂) K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv)) := by
  -- Route correction: rewrite only the mixed factor so the remaining blocker is the literal
  -- specialization of the older pullback-cover decomposition theorem.
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
    (𝒮 := 𝒮) hGerbe hAbelian f I₂ K]

/-- Helper for Lemma 8.11.8: after the left branch is rewritten to the literal pullback-cover
component, combine the first two pulled factors on the fixed owner `K.f` so the branch matches
the input shape of the older pullback-cover decomposition theorem. -/
private theorem chosen_cover_transition_left_branch_old_input_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} {q : Y ⟶ V}
    {I₁ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (_f₁ : Y ⟶ I₁.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
      (chosen_cover_pullback_to_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (q := I₁.f ≫ f)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₁) K).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv) =
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom ≫
          (chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := I₁.f ≫ f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₁)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₁).inv) := by
  -- Replace the component comparison by the literal pullback map on `C / K.Y`.
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I₁.f ≫ f)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₁) K]
  -- Then combine the two consecutive pullbacks along `K.f` into the theorem-input core.
  rw [← Functor.map_comp]

/-- Helper for Lemma 8.11.8: symmetrically, after the right branch is rewritten to the literal
pullback-cover component, combine the first two pulled factors on the fixed owner `K.f` so the
branch matches the input shape of the older pullback-cover decomposition theorem. -/
private theorem chosen_cover_transition_right_branch_old_input_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} {q : Y ⟶ V}
    {I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (_f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom) ≫
      (chosen_cover_pullback_to_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (q := I₂.f ≫ f)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₂) K).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv) =
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom ≫
          (chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (q := I₂.f ≫ f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₂)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I₂).inv) := by
  -- Replace the component comparison by the literal pullback map on `C / K.Y`.
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian
    (q := I₂.f ≫ f)
    (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I₂) K]
  -- Then combine the two consecutive pullbacks along `K.f` into the theorem-input core.
  rw [← Functor.map_comp]

/-- Helper for Lemma 8.11.8: after moving to the common owner `K.f`, the left overlap leg still
lands over the same composite owner arrow. This is the explicit owner equation needed when
materializing the old pullback-cover theorem inputs. -/
private theorem chosen_cover_transition_left_branch_common_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} {q : Y ⟶ V}
    {I₁ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (K.f ≫ f₁) ≫ I₁.f = K.f ≫ q := by
  -- Reassociate once and push the fixed owner `K.f` across the known overlap identity `hf₁`.
  simpa [Category.assoc] using congrArg (fun t ↦ K.f ≫ t) hf₁

/-- Helper for Lemma 8.11.8: after moving to the same common owner `K.f`, the right overlap leg
lands over that same composite owner arrow. This is the symmetric owner equation for the old
pullback-cover theorem inputs. -/
private theorem chosen_cover_transition_right_branch_common_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} {q : Y ⟶ V}
    {I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₂ : Y ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (K.f ≫ f₂) ≫ I₂.f = K.f ≫ q := by
  -- The right branch uses the same owner reassociation on the pulled overlap identity `hf₂`.
  simpa [Category.assoc] using congrArg (fun t ↦ K.f ≫ t) hf₂

/-- Helper for Lemma 8.11.8: when one chosen-cover leg `g` already lies over `q`, the literal old
pullback-cover theorem input is the identity arrow of the pullback cover over `q`. Its base arrow
is the refined chosen-cover member `I.precomp g`, so later blocked proofs can name that input
without unfolding `Cover.pullback`. -/
private noncomputable def chosen_cover_transition_pullback_input_arrow
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow :=
  ⟨Y, 𝟙 Y, (chosen_cover_pullback_cover_hom_mem_iff (𝒮 := 𝒮) hGerbe q (𝟙 Y)).2 <| by
      -- Rewrite the pullback-cover membership to the refined chosen-cover leg `g ≫ I.f = q`.
      simpa [Category.id_comp, hg] using (I.precomp g).hf⟩

/-- Helper for Lemma 8.11.8: the explicit old-theorem input arrow above has base arrow exactly
the refined chosen-cover member `I.precomp g`. This is the first transport-stable rewrite needed
before specializing the old pullback-cover decomposition theorems literally. -/
private theorem chosen_cover_transition_pullback_input_base
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g).base = I.precomp g := by
  -- Both arrows have the same source and the same displayed composite `q = g ≫ I.f`.
  ext <;> simp [chosen_cover_transition_pullback_input_arrow, hg]

/-- Helper for Lemma 8.11.8: after precomposing the explicit old-theorem input by the fixed
chosen-cover arrow `K.f`, the base arrow is exactly the common-owner refinement
`I.precomp (K.f ≫ g)`. This packages the `.base` normalization that was still implicit at the
blocked `change` boundary. -/
private theorem chosen_cover_transition_pullback_input_precomp_base
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g).precomp K.f).base = I.precomp (K.f ≫ g) := by
  -- First pass the `.base` projection through `precomp`, then reassociate the visible branch.
  rw [chosen_cover_pullback_cover_precomp_base]
  rw [chosen_cover_transition_pullback_input_base (𝒮 := 𝒮) hGerbe q I g]
  ext <;> simp [Category.assoc]

/-- Helper for Lemma 8.11.8: the explicit old-theorem input arrow still lies over the original
owner `q` after rewriting its hidden base to the literal refined chosen-cover member
`I.precomp g`. This is the owner equation needed when specializing the older pullback-cover
decomposition theorem with a named input arrow. -/
private theorem chosen_cover_transition_pullback_input_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I g).f ≫
        (I.precomp g).f = q := by
  -- Read the owner equation from the named pullback-cover arrow after normalizing its base.
  simpa [chosen_cover_transition_pullback_input_base
    (𝒮 := 𝒮) hGerbe q I g] using
    (chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g).hf

/-- Helper for Lemma 8.11.8: after precomposing the explicit old-theorem input by `K.f`, the
resulting named pullback-cover arrow lies over the common owner `K.f ≫ q` with literal refined
base `I.precomp (K.f ≫ g)`. This isolates the final owner hypothesis that remains hidden at the
blocked `change` boundary. -/
private theorem chosen_cover_transition_pullback_input_precomp_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I g).precomp K.f).f ≫
        (I.precomp (K.f ≫ g)).f = K.f ≫ q := by
  -- First expose the precomposed arrow's owner equation, then rewrite its hidden base.
  simpa [chosen_cover_transition_pullback_input_precomp_base
    (𝒮 := 𝒮) hGerbe q I g (K := K), Category.assoc] using
    ((chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g).precomp K.f).hf

/-- Helper for Lemma 8.11.8: the explicit pullback-cover input used in the chosen-cover
transition route has identity leg over its source object, so after precomposing by `K.f` the
resulting pullback-cover leg is literally `K.f`. This records the actual `Cover.Arrow` field
shape at the blocked specialization boundary. -/
private theorem chosen_cover_transition_pullback_input_precomp_f
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ((chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g).precomp K.f).f = K.f := by
  -- Route correction: unfold only the concrete `Cover.Arrow` fields of the named pullback input.
  rfl

/-- Helper for Lemma 8.11.8: one named pullback-cover input carries exactly the literal base and
owner equations needed at the final old-theorem specialization boundary. This packages the stable
frontier data before the remaining `change` step. -/
private theorem chosen_cover_transition_pullback_input_literal_data
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    let I' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g
    I'.base = I.precomp g ∧
      I'.f ≫ (I.precomp g).f = q ∧
      (I'.precomp K.f).base = I.precomp (K.f ≫ g) ∧
      (I'.precomp K.f).f ≫ (I.precomp (K.f ≫ g)).f = K.f ≫ q := by
  -- Read each literal equality from the dedicated normalization lemmas so the branch proofs can
  -- focus only on the remaining theorem-input `change`.
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      chosen_cover_transition_pullback_input_base
        (𝒮 := 𝒮) hGerbe q I g
  · exact
      chosen_cover_transition_pullback_input_owner
        (𝒮 := 𝒮) hGerbe q I g
  · exact
      chosen_cover_transition_pullback_input_precomp_base
        (𝒮 := 𝒮) hGerbe q I g (K := K)
  · exact
      chosen_cover_transition_pullback_input_precomp_owner
        (𝒮 := 𝒮) hGerbe q I g (K := K)

/-- Helper for Lemma 8.11.8: after precomposing the named old-theorem input by the fixed
chosen-cover arrow `K.f`, the resulting pullback-cover arrow already carries the exact literal
base and owner equations on the common owner `K.f ≫ q`. This isolates the precise precomposed
frontier used by the blocked left/right theorem-level adapters. -/
private theorem chosen_cover_transition_pullback_input_precomp_literal_frontier
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    let I' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g
    let qK : K.Y ⟶ V := K.f ≫ q
    (I'.precomp K.f).base = I.precomp (K.f ≫ g) ∧
      (I'.precomp K.f).f ≫ (I.precomp (K.f ≫ g)).f = qK := by
  -- Read just the precomposed half of the literal frontier from the previously packaged
  -- four-part normalization theorem.
  dsimp
  have h :=
    chosen_cover_transition_pullback_input_literal_data
      (𝒮 := 𝒮) hGerbe q I g K
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- Helper for Lemma 8.11.8: package the two named chosen-cover pullback inputs used in the
common-owner frontier step, together with the literal base/owner equations for both the raw input
arrows and their `K.f`-precomposed frontiers. This keeps the remaining blocker at the old-theorem
specialization boundary instead of re-expanding the same `Cover.Arrow` fields in the main proof.
-/
private theorem chosen_cover_transition_named_inputs_literal_data
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    let I₁' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I₁ f₁
    let I₂' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I₂ f₂
    let qK : K.Y ⟶ V := K.f ≫ q
    let g₁K : K.Y ⟶ I₁.Y := K.f ≫ f₁
    let g₂K : K.Y ⟶ I₂.Y := K.f ≫ f₂
    I₁'.base = I₁.precomp f₁ ∧
      I₁'.f ≫ (I₁.precomp f₁).f = q ∧
      (I₁'.precomp K.f).base = I₁.precomp g₁K ∧
      (I₁'.precomp K.f).f ≫ (I₁.precomp g₁K).f = qK ∧
      I₂'.base = I₂.precomp f₂ ∧
      I₂'.f ≫ (I₂.precomp f₂).f = q ∧
      (I₂'.precomp K.f).base = I₂.precomp g₂K ∧
      (I₂'.precomp K.f).f ≫ (I₂.precomp g₂K).f = qK := by
  -- Read the left and right raw/frontier equalities from the already isolated one-branch
  -- normalization lemmas, so later proofs can specialize the old theorem without reopening them.
  dsimp
  have h₁ :=
    chosen_cover_transition_pullback_input_literal_data
      (𝒮 := 𝒮) hGerbe q I₁ f₁ K
  have h₂ :=
    chosen_cover_transition_pullback_input_literal_data
      (𝒮 := 𝒮) hGerbe q I₂ f₂ K
  exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2, h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2⟩

/-- Helper for Lemma 8.11.8: repackage the bundled named-input literal data into the exact
eight projection equalities expected by the frontier boundary adapter. This keeps the wrapper
proof from re-deriving those `Cover.Arrow` projections by local `simpa` glue. -/
theorem chosen_cover_transition_named_inputs_exact_boundary_data
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I₁ f₁).base = I₁.precomp f₁ ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).f ≫ (I₁.precomp f₁).f = q ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).base = I₁.precomp (K.f ≫ f₁) ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).f ≫
          (I₁.precomp (K.f ≫ f₁)).f = K.f ≫ q ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).base = I₂.precomp f₂ ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).f ≫ (I₂.precomp f₂).f = q ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).base = I₂.precomp (K.f ≫ f₂) ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).f ≫
          (I₂.precomp (K.f ≫ f₂)).f = K.f ≫ q := by
  -- Read the already packaged frontier data once, then project it directly to the exact
  -- hypothesis shapes expected by `chosen_cover_transition_exact_specialization_literal_boundary`.
  rcases
      chosen_cover_transition_named_inputs_literal_data
        (𝒮 := 𝒮) hGerbe q f₁ f₂ K with
    ⟨hI₁_base, hI₁_owner, hI₁_precomp_base, hI₁_precomp_owner,
      hI₂_base, hI₂_owner, hI₂_precomp_base, hI₂_precomp_owner⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hI₁_base
  · simpa using hI₁_owner
  · simpa using hI₁_precomp_base
  · simpa using hI₁_precomp_owner
  · simpa using hI₂_base
  · simpa using hI₂_owner
  · simpa using hI₂_precomp_base
  · simpa using hI₂_precomp_owner

/-- Helper for Lemma 8.11.8: once the two chosen-cover branches are rewritten to the literal
pullback-cover frontiers, both sides are the same specialization of the normalized
pullback-cover component theorem at the common owner `(K.f ≫ q)`. This is the shared
post-rewrite bridge that replaces the previous one-sided adapter chain. -/
theorem chosen_cover_transition_pullback_cover_refined_specialization_exact
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    pullback_cover_target_secondary_cover_component_refined
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := q)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
      (r := K.f)
      (I₁ := chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁)
      (I₂ := chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂)
      (g₁ := K.f) (g₂ := K.f)
      (hg₁ := by
        -- The named left old-theorem input has identity leg, so its owner equation is literal.
        simp [chosen_cover_transition_pullback_input_arrow])
      (hg₂ := by
        -- The right old-theorem input is normalized in the same way.
        simp [chosen_cover_transition_pullback_input_arrow])
      K L := by
  -- Route correction: specialize the old pullback-cover theorem before any boundary rewriting.
  exact
    pullback_cover_target_secondary_cover_component_refined
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := q)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
      (r := K.f)
      (I₁ := chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁)
      (I₂ := chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂)
      (g₁ := K.f) (g₂ := K.f)
      (hg₁ := by
        simp [chosen_cover_transition_pullback_input_arrow])
      (hg₂ := by
        simp [chosen_cover_transition_pullback_input_arrow])
      K L

/-- Helper for Lemma 8.11.8: rewrite the exact named-input specialization of the old
pullback-cover theorem to the current chosen-cover frontier. This keeps the theorem boundary
separate from the literal `Cover.Arrow` normalization step. -/
theorem chosen_cover_transition_exact_specialization_literal_boundary
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    {Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow)
    (hI₁_base :
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).base = I₁.precomp f₁)
    (hI₁_owner :
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).f ≫ (I₁.precomp f₁).f = q)
    (hI₁_precomp_base :
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).base = I₁.precomp (K.f ≫ f₁))
    (hI₁_precomp_owner :
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).f ≫ (I₁.precomp (K.f ≫ f₁)).f = K.f ≫ q)
    (hI₂_base :
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).base = I₂.precomp f₂)
    (hI₂_owner :
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).f ≫ (I₂.precomp f₂).f = q)
    (hI₂_precomp_base :
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).base = I₂.precomp (K.f ≫ f₂))
    (hI₂_precomp_owner :
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).f ≫ (I₂.precomp (K.f ≫ f₂)).f = K.f ≫ q)
    (hExact :
      pullback_cover_target_secondary_cover_component_refined
        (𝒮 := 𝒮) hGerbe hAbelian
        (q := q)
        (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V)
        (r := K.f)
        (I₁ := chosen_cover_transition_pullback_input_arrow
          (𝒮 := 𝒮) hGerbe q I₁ f₁)
        (I₂ := chosen_cover_transition_pullback_input_arrow
          (𝒮 := 𝒮) hGerbe q I₂ f₂)
        (g₁ := K.f) (g₂ := K.f)
        (hg₁ := by
          simp [chosen_cover_transition_pullback_input_arrow])
        (hg₂ := by
          simp [chosen_cover_transition_pullback_input_arrow])
        K L) :
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
  let _ := hI₁_base
  let _ := hI₁_owner
  let _ := hI₁_precomp_base
  let _ := hI₁_precomp_owner
  let _ := hI₂_base
  let _ := hI₂_owner
  let _ := hI₂_precomp_base
  let _ := hI₂_precomp_owner
  -- Route correction: once the explicit `Cover.Arrow` projection equalities are fixed, the
  -- chosen-cover frontier is literally the exact named-input specialization `hExact`.
  simpa only [Category.assoc, hI₁_base, hI₁_owner, hI₁_precomp_base, hI₁_precomp_owner,
    hI₂_base, hI₂_owner, hI₂_precomp_base, hI₂_precomp_owner,
    chosen_cover_transition_pullback_input_precomp_f] using hExact

end CategoryTheory
