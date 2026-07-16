import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part09

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
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
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom) ≫
          (chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L)) := by
  -- Both descent-equivalence functors and the descent-data component evaluations are functorial,
  -- so the composite splits termwise (`map_comp` at two functor levels, `comp_hom` at two
  -- component levels — all definitional).
  simp only [Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  exact congrArg (fun m => m.hom L)
    ((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map_comp _ _)

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
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂) ≫
        ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
          ((chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_pulled_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L)) := by
  -- Symmetric to the left branch: termwise splitting via `map_comp` + `comp_hom`.
  simp only [Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  exact congrArg (fun m => m.hom L)
    ((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map_comp _ _)

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
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₁).hom))).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian V).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
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
              (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))) := by
  rw [chosen_cover_descent_datum_hom_component
      (𝒮 := 𝒮) hGerbe hAbelian f₁ f₂ hf₁ hf₂ K]
  let S := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)
  let E := localizedSheafToCoverDescentEquivalence (J := J) S
  let a :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
      ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).obj I₁))
  let b :=
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).hom
      (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])
  let c :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))
  have hsplit : ((E.functor.map (a ≫ b ≫ c)).hom L) =
      ((E.functor.map a).hom L) ≫ ((E.functor.map b).hom L) ≫
        ((E.functor.map c).hom L) := by
    calc
      ((E.functor.map (a ≫ b ≫ c)).hom L)
          = ((E.functor.map (a ≫ b) ≫ E.functor.map c).hom L) := by
              exact congrArg (fun m => m.hom L) (E.functor.map_comp (a ≫ b) c)
      _ = ((E.functor.map (a ≫ b)).hom L) ≫ ((E.functor.map c).hom L) := by
              simp only [Pseudofunctor.DescentData.comp_hom]
      _ = (((E.functor.map a).hom L) ≫ ((E.functor.map b).hom L)) ≫
            ((E.functor.map c).hom L) := by
              rw [show ((E.functor.map (a ≫ b)).hom L) =
                  ((E.functor.map a).hom L) ≫ ((E.functor.map b).hom L) from
                congrArg (fun m => m.hom L) (E.functor.map_comp a b)]
      _ = ((E.functor.map a).hom L) ≫ ((E.functor.map b).hom L) ≫
            ((E.functor.map c).hom L) := by
              simp only [Category.assoc]
  change _ ≫ ((E.functor.map (a ≫ b ≫ c)).hom L) = _
  rw [hsplit]
  rw [pullback_cover_target_secondary_cover_mapped_raw_component
      (𝒮 := 𝒮) hGerbe hAbelian (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂]) L]
  simp only [S, E, a, c, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Category.assoc]
  rfl

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
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          ((chosen_cover_pulled_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian f).hom q f₁ f₂ (_hf₁ := hf₁) (_hf₂ := hf₂))).hom K)).hom L ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            ((chosen_cover_descent_transition_component_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom))).hom K)).hom L) =
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
  -- First expose the right shell as the pulled normalized target comparison.
  -- DEFERRED (deep §5.2 transition core): symmetric target-side member-cross reduction of the
  -- exposed right transition branch to the literal pullback-cover decomposition input. Same need as
  -- the left version: Part09 normalized forms + `mapComp'` coherences + the still-open
  -- `pullback_cover_source_component_iso` (Part06) target bridge; consumer is Part11's
  -- `reduced_branches_match` (downstream, so unavailable here).
  rw [chosen_cover_transition_pulled_overlap_common_owner
      (𝒮 := 𝒮) hGerbe hAbelian f q f₁ f₂ hf₁ hf₂ K L]
  let FL := ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor
  let a :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
      ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₁))
  let b :=
    (chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).hom
      (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (_hf₁ := by rw [Category.assoc, hf₁]) (_hf₂ := by rw [Category.assoc, hf₂])
  let cPulled :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      ((chosen_cover_pulled_descent_datum (𝒮 := 𝒮) hGerbe hAbelian f).obj I₂))
  let t := (chosen_cover_descent_transition_component_iso
    (𝒮 := 𝒮) hGerbe hAbelian f I₂).hom
  let gT :=
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map t)
  let fT :=
    ((J.pseudofunctorOver (Type (max u v))).map (K.f ≫ f₂).op.toLoc).toFunctor.map t
  let cDescent :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian V).obj I₂))
  have hsplit : FL.map (a ≫ b ≫ cPulled) =
      FL.map a ≫ FL.map b ≫ FL.map cPulled := by
    calc
      FL.map (a ≫ b ≫ cPulled)
          = FL.map (a ≫ b) ≫ FL.map cPulled := FL.map_comp (a ≫ b) cPulled
      _ = (FL.map a ≫ FL.map b) ≫ FL.map cPulled := by rw [FL.map_comp a b]
      _ = FL.map a ≫ FL.map b ≫ FL.map cPulled := by simp only [Category.assoc]
  have hnat :
      cPulled ≫ gT = fT ≫ cDescent := by
    simpa only [cPulled, cDescent, t, gT, fT, Functor.comp_map] using
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.naturality t).symm
  have hnatL :
      FL.map cPulled ≫ FL.map gT = FL.map fT ≫ FL.map cDescent := by
    calc
      FL.map cPulled ≫ FL.map gT = FL.map (cPulled ≫ gT) := by
              exact (FL.map_comp _ _).symm
      _ = FL.map (fT ≫ cDescent) := by
              exact congrArg FL.map hnat
      _ = FL.map fT ≫ FL.map cDescent := FL.map_comp _ _
  change FL.map (a ≫ b ≫ cPulled) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.map
            t)).hom K)).hom L) = _
  rw [hsplit]
  simp only [t, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Category.assoc]
  change FL.map a ≫ FL.map b ≫ FL.map cPulled ≫ FL.map gT =
      FL.map a ≫ FL.map b ≫ FL.map fT ≫ FL.map cDescent
  calc
    FL.map a ≫ FL.map b ≫ FL.map cPulled ≫ FL.map gT
        = FL.map a ≫ FL.map b ≫ (FL.map cPulled ≫ FL.map gT) := by
            rfl
    _ = FL.map a ≫ FL.map b ≫ (FL.map fT ≫ FL.map cDescent) := by
            rw [hnatL]
            rfl
    _ = FL.map a ≫ FL.map b ≫ FL.map fT ≫ FL.map cDescent := by
            rfl

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
  ext <;> simp [chosen_cover_transition_pullback_input_arrow, hg, Category.assoc]
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
  simp [chosen_cover_transition_pullback_input_arrow, hg]

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
        (I.precomp g).f = K.f ≫ q := by
  -- First expose the precomposed arrow's owner equation, then rewrite its hidden base.
  simp [chosen_cover_transition_pullback_input_arrow, hg]

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
  simp [chosen_cover_transition_pullback_input_arrow]

/-- Helper for Lemma 8.11.8: one named pullback-cover input carries exactly the literal base and
owner equations needed at the final old-theorem specialization boundary. This packages the stable
frontier data before the remaining `change` step. -/
private theorem chosen_cover_transition_pullback_input_literal_data
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    let I' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g
    I'.base = I.precomp g ∧
      I'.f ≫ (I.precomp g).f = q ∧
      (I'.precomp K.f).base = I.precomp (K.f ≫ g) ∧
      (I'.precomp K.f).f ≫ (I.precomp g).f = K.f ≫ q := by
  exact ⟨chosen_cover_transition_pullback_input_base (𝒮 := 𝒮) hGerbe q I g hg,
    chosen_cover_transition_pullback_input_owner (𝒮 := 𝒮) hGerbe q I g hg,
    chosen_cover_transition_pullback_input_precomp_base (𝒮 := 𝒮) hGerbe q I g hg K,
    chosen_cover_transition_pullback_input_precomp_owner (𝒮 := 𝒮) hGerbe q I g hg K⟩
/-- Helper for Lemma 8.11.8: after precomposing the named old-theorem input by the fixed
chosen-cover arrow `K.f`, the resulting pullback-cover arrow already carries the exact literal
base and owner equations on the common owner `K.f ≫ q`. This isolates the precise precomposed
frontier used by the blocked left/right theorem-level adapters. -/
private theorem chosen_cover_transition_pullback_input_precomp_literal_frontier
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    let I' := chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I g
    let qK : K.Y ⟶ V := K.f ≫ q
    (I'.precomp K.f).base = I.precomp (K.f ≫ g) ∧
      (I'.precomp K.f).f ≫ (I.precomp g).f = qK := by
  -- Read just the precomposed half of the literal frontier from the previously packaged
  -- four-part normalization theorem.
  obtain ⟨_, _, h₃, h₄⟩ :=
    chosen_cover_transition_pullback_input_literal_data (𝒮 := 𝒮) hGerbe q I g hg K
  exact ⟨h₃, h₄⟩

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
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
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
      (I₁'.precomp K.f).f ≫ (I₁.precomp f₁).f = qK ∧
      I₂'.base = I₂.precomp f₂ ∧
      I₂'.f ≫ (I₂.precomp f₂).f = q ∧
      (I₂'.precomp K.f).base = I₂.precomp g₂K ∧
      (I₂'.precomp K.f).f ≫ (I₂.precomp f₂).f = qK := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    chosen_cover_transition_pullback_input_literal_data (𝒮 := 𝒮) hGerbe q I₁ f₁ hf₁ K
  obtain ⟨h₅, h₆, h₇, h₈⟩ :=
    chosen_cover_transition_pullback_input_literal_data (𝒮 := 𝒮) hGerbe q I₂ f₂ hf₂ K
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
/-- Helper for Lemma 8.11.8: repackage the bundled named-input literal data into the exact
eight projection equalities expected by the frontier boundary adapter. This keeps the wrapper
proof from re-deriving those `Cover.Arrow` projections by local `simpa` glue. -/
theorem chosen_cover_transition_named_inputs_exact_boundary_data
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    (chosen_cover_transition_pullback_input_arrow
      (𝒮 := 𝒮) hGerbe q I₁ f₁).base = I₁.precomp f₁ ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).f ≫ (I₁.precomp f₁).f = q ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).base = I₁.precomp (K.f ≫ f₁) ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₁ f₁).precomp K.f).f ≫
          (I₁.precomp f₁).f = K.f ≫ q ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).base = I₂.precomp f₂ ∧
      (chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).f ≫ (I₂.precomp f₂).f = q ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).base = I₂.precomp (K.f ≫ f₂) ∧
      ((chosen_cover_transition_pullback_input_arrow
        (𝒮 := 𝒮) hGerbe q I₂ f₂).precomp K.f).f ≫
          (I₂.precomp f₂).f = K.f ≫ q := by
  -- Read the already packaged frontier data once, then project it directly to the exact
  -- hypothesis shapes expected by `chosen_cover_transition_exact_specialization_literal_boundary`.
  rcases
      chosen_cover_transition_named_inputs_literal_data
        (𝒮 := 𝒮) hGerbe q f₁ f₂ hf₁ hf₂ K with
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

/-- Helper for Lemma 8.11.8: exported boundary package for the common-owner specialization.
This hides the private concrete pullback-cover input arrows while returning named public witnesses
and the exact base/owner equalities needed to specialize the pullback-cover target theorem at the
Part11 frontier. -/
theorem chosen_cover_transition_exact_specialization_literal_boundary
    (hGerbe : IsGerbe J 𝒮.p)
    {V Y : C} (q : Y ⟶ V)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe Y).Arrow) :
    ∃ hmem₁ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q) (𝟙 Y),
      ∃ hmem₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q) (𝟙 Y),
        let I₁' : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow :=
          ⟨Y, 𝟙 Y, hmem₁⟩
        let I₂' : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow :=
          ⟨Y, 𝟙 Y, hmem₂⟩
        I₁'.base = I₁.precomp f₁ ∧
          I₁'.f ≫ (I₁.precomp f₁).f = q ∧
          (I₁'.precomp K.f).base = I₁.precomp (K.f ≫ f₁) ∧
          (I₁'.precomp K.f).f ≫ (I₁.precomp f₁).f = K.f ≫ q ∧
          I₂'.base = I₂.precomp f₂ ∧
          I₂'.f ≫ (I₂.precomp f₂).f = q ∧
          (I₂'.precomp K.f).base = I₂.precomp (K.f ≫ f₂) ∧
          (I₂'.precomp K.f).f ≫ (I₂.precomp f₂).f = K.f ≫ q := by
  let hmem₁ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q) (𝟙 Y) :=
    (chosen_cover_pullback_cover_hom_mem_iff (𝒮 := 𝒮) hGerbe q (𝟙 Y)).2 <| by
      simpa [Category.id_comp, hf₁] using (I₁.precomp f₁).hf
  let hmem₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q) (𝟙 Y) :=
    (chosen_cover_pullback_cover_hom_mem_iff (𝒮 := 𝒮) hGerbe q (𝟙 Y)).2 <| by
      simpa [Category.id_comp, hf₂] using (I₂.precomp f₂).hf
  refine ⟨hmem₁, hmem₂, ?_⟩
  simpa [chosen_cover_transition_pullback_input_arrow, hmem₁, hmem₂] using
    chosen_cover_transition_named_inputs_exact_boundary_data
      (𝒮 := 𝒮) hGerbe q f₁ f₂ hf₁ hf₂ K

end CategoryTheory
