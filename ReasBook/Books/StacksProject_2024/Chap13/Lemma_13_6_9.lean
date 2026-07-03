import Mathlib
import stacks_project.Chap13.Definition_13_6_7
import stacks_project.Chap13.Lemma_13_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open CategoryTheory.Pretriangulated
open scoped ZeroObject CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]

/- Domain-style sampling for Lemma 13.6.9:
- primary domain: Verdier localization of a triangulated category by the cone-defined morphism
  property of a triangulated object property, together with retract closure on the object-property
  side;
- sampled owner declarations:
  `Functor.kernel P.trW.Q`,
  `ObjectProperty.retractClosure`,
  `ObjectProperty.prop_retractClosure_iff`,
  `ObjectProperty.retractClosure_le_iff`,
  `CategoryTheory.Retract`,
  `localization_object_isZero_tfae_of_compatibleWithTriangulation`,
  `trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`;
- best owner abstraction: the core object-property owner is `P.retractClosure`; the kernel
  `Functor.kernel P.trW.Q` is the Verdier-localization view on that owner, while the intrinsic
  source-facing direct-summand witness is `Retract`;
- primitive-vs-derived split:
  primitive data: the triangulated object property `P`;
  derived API: the kernel/retract-closure identification, its source-facing direct-summand
    consequence, and the initiality statement against retract-stable triangulated object
    properties.

Source/core/bridge triage:
- `source-facing`: the kernel of the quotient by `P` and its direct-summand characterization;
- `core/canonical`: `P.retractClosure`, `Functor.kernel P.trW.Q`, and `Retract`;
- `bridge/view`: the identification of those two object properties together with the biproduct
  presentation of a retract/direct summand. -/

-- Proof sketch: apply Lemma 13.5.9 to the localization functor `P.trW.Q`. An object is in the
-- kernel exactly when it becomes a direct summand of the cone term of a distinguished triangle
-- whose first morphism lies in `P.trW`; by `trW_iff_of_distinguished`, that cone term lies in
-- `P.isoClosure`, and the direct-summand clause is already expressed by the canonical retract
-- owner, so retract stability puts the object in `P.retractClosure`. The converse follows by
-- reversing this characterization and using that retracts become zero in the quotient.
/-- Lemma 13.6.9: the kernel of the quotient functor by a full triangulated subcategory `P` is
exactly the retract closure of `P`. Equivalently, this kernel is the smallest strictly full
saturated triangulated subcategory containing `P`. -/
theorem kernel_triangulatedLocalization_eq_retractClosure :
    Functor.kernel P.trW.Q = P.retractClosure := by
  let F : D ⥤ MorphismProperty.Localization P.trW := MorphismProperty.Q P.trW
  ext Z
  constructor
  · intro hZ
    have hzeroTfae :
        List.TFAE
          [ IsZero (F.obj Z)
          , ∃ Z' : D, P.trW (0 : Z ⟶ Z')
          , ∃ Z' : D, P.trW (0 : Z' ⟶ Z)
          , ∃ T : Triangle D,
              T ∈ distTriang D ∧ P.trW T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
          ] := by
      simpa [F] using localization_object_isZero_tfae_of_compatibleWithTriangulation P.trW Z
    have hZ' : IsZero (F.obj Z) := by
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hZ
    obtain ⟨T, hT, hmor, ⟨r⟩⟩ :=
      (hzeroTfae.out 0 3).mp (by simpa using hZ')
    have hTobj : P.isoClosure T.obj₃ := by
      exact ((P.isoClosure).trW_iff_of_distinguished T hT).mp
        (by simpa [P.trW_isoClosure] using hmor)
    have hRetract : (P.isoClosure).retractClosure Z := by
      exact ((P.isoClosure).retractClosure).prop_of_retract r
        (P.isoClosure.le_retractClosure _ hTobj)
    simpa [P.retractClosure_isoClosure] using hRetract
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have hZeroMor : ∃ Z' : D, P.trW (0 : Y ⟶ Z') := by
      exact ⟨0, trW.mk' P (contractible_distinguished Y) hY⟩
    have hzeroTfae :
        List.TFAE
          [ IsZero (F.obj Y)
          , ∃ Z' : D, P.trW (0 : Y ⟶ Z')
          , ∃ Z' : D, P.trW (0 : Z' ⟶ Y)
          , ∃ T : Triangle D,
              T ∈ distTriang D ∧ P.trW T.mor₁ ∧ Nonempty (Retract Y T.obj₃)
          ] := by
      simpa [F] using localization_object_isZero_tfae_of_compatibleWithTriangulation P.trW Y
    have hYzero : IsZero (F.obj Y) := (hzeroTfae.out 1 0).mp hZeroMor
    let hmap : Retract (F.obj Z) (F.obj Y) := Retract.map r F
    let e : F.obj Z ≅ F.obj Y :=
      { hom := hmap.i
        inv := hmap.r
        hom_inv_id := hmap.retract
        inv_hom_id := IsZero.eq_of_src hYzero _ _ }
    have hZzero : IsZero (F.obj Z) := hYzero.of_iso e
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hZzero

-- Proof sketch: rewrite the kernel using `kernel_triangulatedLocalization_eq_retractClosure` and
-- then unfold the owner `P.retractClosure`: membership means exactly being a retract of an object
-- of `P`, i.e. the intrinsic direct-summand condition.
/-- An object lies in the kernel of the quotient functor by `P` exactly when it becomes a direct
summand of some object of `P`, expressed canonically by a retract witness. -/
theorem mem_kernel_triangulatedLocalization_iff
    (Z : D) :
    Functor.kernel P.trW.Q Z ↔ ∃ Y : D, P Y ∧ Nonempty (Retract Z Y) := by
  rw [kernel_triangulatedLocalization_eq_retractClosure P]
  simpa [and_left_comm, and_assoc] using P.prop_retractClosure_iff Z

-- Proof sketch: this is the biproduct-model companion to
-- `mem_kernel_triangulatedLocalization_iff`; in a preadditive category, a retract is equivalently
-- a direct summand, encoded by the canonical split-triangle owner
-- `exists_iso_binaryBiproduct_of_distTriang`.
/-- Biproduct-model companion to `mem_kernel_triangulatedLocalization_iff`. -/
theorem mem_kernel_triangulatedLocalization_iff_biprod
    (Z : D) :
    Functor.kernel P.trW.Q Z ↔ ∃ (Z' Y : D), P Y ∧ Nonempty (Z ⊞ Z' ≅ Y) := by
  constructor
  · rintro hZ
    rcases (mem_kernel_triangulatedLocalization_iff P Z).mp hZ with ⟨Y, hY, ⟨r⟩⟩
    obtain ⟨Z', f, h, hT⟩ := distinguished_cocone_triangle₁ r.r
    let T : Triangle D := Triangle.mk f r.r h
    have hT' : T ∈ distTriang D := hT
    haveI : IsSplitEpi T.mor₂ := IsSplitEpi.mk' { section_ := r.i, id := r.retract }
    have hzero : T.mor₃ = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT' (inferInstance : Epi T.mor₂)
    obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT' hzero
    exact ⟨Z', Y, hY, ⟨biprod.braiding Z Z' ≪≫ e.symm⟩⟩
  · rintro ⟨Z', Y, hY, ⟨e⟩⟩
    have hY' : P.retractClosure Y := P.le_retractClosure _ hY
    have hBiprod : P.retractClosure (Z ⊞ Z') := (P.retractClosure).prop_of_iso e.symm hY'
    have hZ' : P.retractClosure Z :=
      of_biprod_left P.retractClosure hBiprod
    rw [kernel_triangulatedLocalization_eq_retractClosure P]
    exact hZ'

-- Proof sketch: rewrite the kernel using `kernel_triangulatedLocalization_eq_retractClosure` and
-- apply the canonical owner theorem `ObjectProperty.retractClosure_le_iff`.
/-- The kernel of the quotient functor by `P` is initial among retract-stable object properties
containing `P`. -/
theorem kernel_triangulatedLocalization_le_iff
    (R : ObjectProperty D) [R.IsStableUnderRetracts] :
    Functor.kernel P.trW.Q ≤ R ↔ P ≤ R := by
  simpa [kernel_triangulatedLocalization_eq_retractClosure P] using P.retractClosure_le_iff R

end

end CategoryTheory
