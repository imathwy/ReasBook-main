import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap12.Lemma_12_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D)

/-- Helper for Lemma 12.7.1: if every inverse binary biproduct comparison of `F` is an
isomorphism, then `F` carries the zero object of `C` to a zero object of `D`. -/
private theorem isZero_obj_zero_of_biprodComparison'_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison' X Y)) : IsZero (F.obj (0 : C)) := by
  -- Evaluate the comparison at `(0, 0)` and transport the known isomorphism of `biprod.inl`.
  letI : IsIso (F.biprodComparison' (0 : C) 0) := h 0 0
  letI : IsIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C)) :=
    (Biprod.isIso_inl_iff_isZero (0 : C) (0 : C)).2 (isZero_zero C)
  have hComp :
      IsIso ((biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) ≫
        F.biprodComparison' (0 : C) 0) := by
    rw [F.inl_biprodComparison' (0 : C) (0 : C)]
    infer_instance
  letI : IsIso ((biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) ≫
      F.biprodComparison' (0 : C) 0) := hComp
  -- Cancel the comparison isomorphism to recover that the target `biprod.inl` is itself an
  -- isomorphism, which characterizes the zero object.
  letI : IsIso (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) :=
    IsIso.of_isIso_comp_right (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C))
      (F.biprodComparison' (0 : C) 0)
  exact (Biprod.isIso_inl_iff_isZero (F.obj (0 : C)) (F.obj (0 : C))).1 inferInstance

omit [HasZeroObject C] in
/-- Helper for Lemma 12.7.1: isomorphisms of all inverse biproduct comparisons imply that `F`
preserves binary biproducts once `F` is known to preserve zero morphisms. -/
private theorem preservesBinaryBiproducts_of_biprodComparison'_isIso
    [F.PreservesZeroMorphisms] (h : ∀ X Y : C, IsIso (F.biprodComparison' X Y)) :
    PreservesBinaryBiproducts F := by
  -- The comparison isomorphisms are in particular epi, so the standard criterion applies.
  refine ⟨fun {X Y} ↦ ?_⟩
  letI : Epi (F.biprodComparison' X Y) := by
    let _ := h X Y
    infer_instance
  exact preservesBinaryBiproduct_of_epi_biprodComparison' F

/-- Helper for Lemma 12.7.1: isomorphisms of all inverse binary biproduct comparisons force `F`
to be additive. -/
private theorem additive_of_biprodComparison'_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison' X Y)) : F.Additive := by
  -- Recover the image of the zero object and then the required zero-morphism preservation.
  have h0 : IsZero (F.obj (0 : C)) := isZero_obj_zero_of_biprodComparison'_isIso F h
  letI : HasZeroObject D := ⟨⟨F.obj (0 : C), h0⟩⟩
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_map_zero_object h0.isoZero
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_biprodComparison'_isIso F h
  -- Once binary biproducts and zero morphisms are preserved, the standard owner theorem gives
  -- additivity.
  exact F.additive_of_preservesBinaryBiproducts

/-- Helper for Lemma 12.7.1: if every forward binary biproduct comparison of `F` is an
isomorphism, then `F` carries the zero object of `C` to a zero object of `D`. -/
private theorem isZero_obj_zero_of_biprodComparison_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison X Y)) : IsZero (F.obj (0 : C)) := by
  -- Evaluate at `(0, 0)` and transfer the zero-object structure from the source biproduct.
  letI : IsIso (F.biprodComparison (0 : C) 0) := h 0 0
  letI : IsIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C)) :=
    (Biprod.isIso_inl_iff_isZero (0 : C) (0 : C)).2 (isZero_zero C)
  have h00 : IsZero ((0 : C) ⊞ (0 : C)) :=
    (isZero_zero C).of_iso (asIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C))).symm
  letI : IsIso (biprod.fst : (0 : C) ⊞ (0 : C) ⟶ (0 : C)) :=
    h00.isIso (isZero_zero C) _
  have hComp :
      IsIso (F.biprodComparison (0 : C) 0 ≫
        (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))) := by
    rw [F.biprodComparison_fst (0 : C) (0 : C)]
    infer_instance
  letI : IsIso (F.biprodComparison (0 : C) 0 ≫
      (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))) := hComp
  -- Cancel the comparison to see that the target projection is an isomorphism as well.
  letI : IsIso (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C)) :=
    IsIso.of_isIso_comp_left (F.biprodComparison (0 : C) 0)
      (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))
  -- A split mono into a biproduct is zero exactly when its complementary injection is zero.
  have hInr : (biprod.inr : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) = 0 := by
    rw [← cancel_mono (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))]
    simp
  rw [IsZero.iff_isSplitMono_eq_zero
    (biprod.inr : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C))]
  exact hInr

omit [HasZeroObject C] in
/-- Helper for Lemma 12.7.1: isomorphisms of all forward biproduct comparisons imply that `F`
preserves binary biproducts once `F` is known to preserve zero morphisms. -/
private theorem preservesBinaryBiproducts_of_biprodComparison_isIso
    [F.PreservesZeroMorphisms] (h : ∀ X Y : C, IsIso (F.biprodComparison X Y)) :
    PreservesBinaryBiproducts F := by
  -- The comparison isomorphisms are in particular mono, so the dual criterion applies.
  refine ⟨fun {X Y} ↦ ?_⟩
  letI : Mono (F.biprodComparison X Y) := by
    let _ := h X Y
    infer_instance
  exact preservesBinaryBiproduct_of_mono_biprodComparison F

/-- Helper for Lemma 12.7.1: isomorphisms of all forward binary biproduct comparisons force `F`
to be additive. -/
private theorem additive_of_biprodComparison_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison X Y)) : F.Additive := by
  -- Recover the image of the zero object and then the required zero-morphism preservation.
  have h0 : IsZero (F.obj (0 : C)) := isZero_obj_zero_of_biprodComparison_isIso F h
  letI : HasZeroObject D := ⟨⟨F.obj (0 : C), h0⟩⟩
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_map_zero_object h0.isoZero
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_biprodComparison_isIso F h
  -- Once binary biproducts and zero morphisms are preserved, the standard owner theorem gives
  -- additivity.
  exact F.additive_of_preservesBinaryBiproducts

/- Source/core/bridge triage for Lemma 12.7.1:
- source-facing: the equivalence between additivity and invertibility of the two canonical binary
  biproduct comparison morphisms
- core/canonical owner: `Functor.Additive`
- bridge/view: `Functor.mapBiprod`, `Functor.biprodComparison`, `Functor.biprodComparison'`,
  `Functor.additive_of_preservesBinaryBiproducts`,
  `Limits.preservesBinaryBiproduct_of_epi_biprodComparison'`, and
  `Limits.preservesBinaryBiproduct_of_mono_biprodComparison`

Primitive data are the zero object and binary biproducts in the source category together with
binary biproducts in the target. Internally, the only extra data needed to recover the owner
predicate `F.Additive` are `IsZero (F.obj 0)` and `PreservesBinaryBiproducts F`; finite
biproducts are not part of the mathematical core of this lemma, so the ambient context is kept at
that primitive layer. -/
-- Proof sketch: use the chapter owner abstraction `F.Additive` from Lemma 12.3.7 to obtain binary
-- biproduct preservation, identify the hom and inverse of `Functor.mapBiprod F X Y` with
-- `Functor.biprodComparison F X Y` and `Functor.biprodComparison' F X Y`, and conversely recover
-- additivity from the primitive pair "`F.obj 0` is a zero object" plus
-- `Functor.PreservesBinaryBiproducts`, using the mono/epi comparison criteria to obtain
-- biproduct preservation.
/-- Lemma 12.7.1: for a functor between additive categories, the following are equivalent: `F` is
additive, the canonical map `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)` is an isomorphism for all
objects `X` and `Y`, and the canonical map `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y` is an isomorphism
for all objects `X` and `Y`. -/
theorem additive_tfae_binary_biprod_comparison_isIso :
    List.TFAE [F.Additive,
      ∀ X Y : C, IsIso (F.biprodComparison' X Y),
      ∀ X Y : C, IsIso (F.biprodComparison X Y)] := by
  -- Additive functors preserve binary biproducts, so both comparison maps are the two-sided
  -- inverses coming from `F.mapBiprod`.
  tfae_have 1 → 2 := by
    intro hF X Y
    letI : F.Additive := hF
    letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    change IsIso (F.mapBiprod X Y).inv
    infer_instance
  -- Conversely, invertibility of the inverse comparison recovers the zero object and binary
  -- biproduct preservation, hence additivity.
  tfae_have 2 → 1 := by
    intro h
    exact additive_of_biprodComparison'_isIso F h
  -- The forward comparison is the `hom` of the same canonical biproduct isomorphism.
  tfae_have 1 → 3 := by
    intro hF X Y
    letI : F.Additive := hF
    letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    change IsIso (F.mapBiprod X Y).hom
    infer_instance
  -- The dual comparison criterion yields the remaining converse.
  tfae_have 3 → 1 := by
    intro h
    exact additive_of_biprodComparison_isIso F h
  tfae_finish

end

end CategoryTheory
