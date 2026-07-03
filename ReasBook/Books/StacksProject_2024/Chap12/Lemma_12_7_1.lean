import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap12.Lemma_12_3_7

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

private theorem isZero_obj_zero_of_biprodComparison'_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison' X Y)) : IsZero (F.obj (0 : C)) := by
  letI : IsIso (F.biprodComparison' (0 : C) 0) := h 0 0
  letI : IsIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C)) :=
    (Biprod.isIso_inl_iff_isZero (0 : C) (0 : C)).2 (isZero_zero C)
  haveI :
      IsIso ((biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) ≫
        F.biprodComparison' (0 : C) 0) := by
    rw [F.inl_biprodComparison' (0 : C) (0 : C)]
    infer_instance
  haveI : IsIso (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) :=
    IsIso.of_isIso_comp_right (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C))
      (F.biprodComparison' (0 : C) 0)
  exact (Biprod.isIso_inl_iff_isZero (F.obj (0 : C)) (F.obj (0 : C))).1 inferInstance

private theorem additive_of_biprodComparison'_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison' X Y)) : F.Additive := by
  have h0 : IsZero (F.obj (0 : C)) := isZero_obj_zero_of_biprodComparison'_isIso F h
  letI : HasZeroObject D := ⟨⟨F.obj (0 : C), h0⟩⟩
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_map_zero_object h0.isoZero
  letI : PreservesBinaryBiproducts F :=
    ⟨fun {X Y} ↦ by
      letI : Epi (F.biprodComparison' X Y) := by
        let _ := h X Y
        infer_instance
      exact preservesBinaryBiproduct_of_epi_biprodComparison' F⟩
  exact F.additive_of_preservesBinaryBiproducts

private theorem isZero_obj_zero_of_biprodComparison_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison X Y)) : IsZero (F.obj (0 : C)) := by
  letI : IsIso (F.biprodComparison (0 : C) 0) := h 0 0
  letI : IsIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C)) :=
    (Biprod.isIso_inl_iff_isZero (0 : C) (0 : C)).2 (isZero_zero C)
  have h00 : IsZero ((0 : C) ⊞ (0 : C)) :=
    (isZero_zero C).of_iso (asIso (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ (0 : C))).symm
  letI : IsIso (biprod.fst : (0 : C) ⊞ (0 : C) ⟶ (0 : C)) :=
    h00.isIso (isZero_zero C) _
  haveI :
      IsIso (F.biprodComparison (0 : C) 0 ≫
        (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))) := by
    rw [F.biprodComparison_fst (0 : C) (0 : C)]
    infer_instance
  haveI : IsIso (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C)) :=
    IsIso.of_isIso_comp_left (F.biprodComparison (0 : C) 0)
      (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))
  have hInr : (biprod.inr : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) = 0 := by
    rw [← cancel_mono (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))]
    simp
  rw [IsZero.iff_isSplitMono_eq_zero
    (biprod.inr : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C))]
  exact hInr

private theorem additive_of_biprodComparison_isIso
    (h : ∀ X Y : C, IsIso (F.biprodComparison X Y)) : F.Additive := by
  have h0 : IsZero (F.obj (0 : C)) := isZero_obj_zero_of_biprodComparison_isIso F h
  letI : HasZeroObject D := ⟨⟨F.obj (0 : C), h0⟩⟩
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_map_zero_object h0.isoZero
  letI : PreservesBinaryBiproducts F :=
    ⟨fun {X Y} ↦ by
      letI : Mono (F.biprodComparison X Y) := by
        let _ := h X Y
        infer_instance
      exact preservesBinaryBiproduct_of_mono_biprodComparison F⟩
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
  tfae_have 1 → 2 := by
    intro hF X Y
    letI : F.Additive := hF
    letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    change IsIso (F.mapBiprod X Y).inv
    infer_instance
  tfae_have 2 → 1 := by
    intro h
    exact additive_of_biprodComparison'_isIso F h
  tfae_have 1 → 3 := by
    intro hF X Y
    letI : F.Additive := hF
    letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    change IsIso (F.mapBiprod X Y).hom
    infer_instance
  tfae_have 3 → 1 := by
    intro h
    exact additive_of_biprodComparison_isIso F h
  tfae_finish

end

end CategoryTheory
