import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.CategoryTheory.Localization.Triangulated
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_20
import StacksProject_2024.stacks_project.Chap04.Lemma_4_27_21
import StacksProject_2024.stacks_project.Chap12.Lemma_12_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory
open MorphismProperty
open Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation] (Z : D)

/- Domain-style sampling:
- primary domain: localization of a pretriangulated category at a morphism property compatible with
  distinguished triangles;
- sampled owner declarations:
  `localization_object_isZero_tfae`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `CategoryTheory.Retract`,
  `binaryBiproductTriangle_distinguished`;
- best owner abstraction: the canonical localization functor `S.Q`, with primitive zero-object
  data recorded by `IsZero (S.Q.obj Z)` and the Chapter 12 owner theorem
  `localization_object_isZero_tfae`; the direct-summand clause is most canonically expressed by
  the retract owner `Retract` rather than by equality with a chosen biproduct model;
- primitive data: the morphism property `S`, the object `Z`, and the relevant localization owner
  instances;
- derived API: the triangulated and saturated refinements that add the distinguished-triangle
  formulations, best stated through the owner objects `Triangle D` and `Retract` rather than by
  primitive biproduct-coordinate data.

Source/core/bridge triage:
- `source-facing`: Lemma 13.5.9, which adds the triangulated direct-summand and distinguished-triangle
  formulations to the zero-object criterion;
- `core/canonical`: the localization owner `S.Q`, the zero-object criterion
  `localization_object_isZero_tfae`, and the saturation owner
  `MorphismProperty.IsSaturatedMultiplicativeSystem`;
- `bridge/view`: the passage between zero morphisms in `S` and distinguished triangles, expressed
  through `Triangle D`, `Retract`, and `binaryBiproductTriangle_distinguished` together with
  `S.compatible_with_triangulation`.
-/

-- Proof sketch: combine the additive-localization criterion `localization_object_isZero_tfae`
-- for clauses `(1)`–`(3)` with the pretriangulated binary-biproduct triangle
-- `binaryBiproductTriangle_distinguished`, the retract/direct-summand owner `Retract`, and the
-- compatibility axiom for `S` to pass between a zero morphism in `S` and a distinguished triangle
-- whose third object has `Z` as a direct summand and whose first morphism lies in `S`.
/-- Helper for Lemma 13.5.9: a zero morphism in `S` out of `Z` yields a distinguished triangle
whose third term contains `Z` as a retract and whose first morphism still lies in `S`. -/
lemma exists_distinguished_retract_of_zero_to_mem {Z Z' : D}
    (h : S (0 : Z ⟶ Z')) :
    ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃) := by
  let T : Triangle D := (binaryBiproductTriangle (Z'⟦(-1 : ℤ)⟧) Z).invRotate
  refine ⟨T, ?_, ?_, ?_⟩
  · -- Inverse rotation preserves distinguished triangles.
    simpa [T] using
      (inv_rot_of_distTriang (binaryBiproductTriangle (Z'⟦(-1 : ℤ)⟧) Z)
        (binaryBiproductTriangle_distinguished (Z'⟦(-1 : ℤ)⟧) Z))
  · -- Shift compatibility transports the given zero denominator to the inverse-rotated first edge.
    have hshift : S ((0 : Z ⟶ Z')⟦(-1 : ℤ)⟧') := by
      simpa using (IsCompatibleWithShift.iff S (0 : Z ⟶ Z') (-1 : ℤ)).2 h
    have hzero : S (0 : Z⟦(-1 : ℤ)⟧ ⟶ Z'⟦(-1 : ℤ)⟧) := by
      simpa [Functor.map_zero] using hshift
    have hmor₁ : T.mor₁ = (0 : Z⟦(-1 : ℤ)⟧ ⟶ Z'⟦(-1 : ℤ)⟧) := by
      -- The first edge of the inverse-rotated split triangle is the negation of a zero morphism.
      dsimp [T, Triangle.invRotate, binaryBiproductTriangle]
      rw [Functor.map_zero, zero_comp]
      exact neg_zero
    rw [hmor₁]
    exact hzero
  · -- The third vertex of `T` is the split biproduct `Z'⟦-1⟧ ⊞ Z`, so `Z` is a retract.
    change Nonempty (Retract Z (Z'⟦(-1 : ℤ)⟧ ⊞ Z))
    exact ⟨{ i := biprod.inr, r := biprod.snd }⟩

/-- Helper for Lemma 13.5.9: if a distinguished triangle localizes to one whose first morphism is
invertible and `Z` is a retract of its third term, then `S.Q.obj Z` is zero. -/
lemma isZero_localization_obj_of_distinguished_retract {Z : D} {T : Triangle D}
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    (hT : T ∈ distTriang D) (hS : S T.mor₁) (r : Retract Z T.obj₃) :
    IsZero (S.Q.obj Z) := by
  letI : S.IsMultiplicative := inferInstance
  letI : S.ContainsIdentities := ‹S.IsMultiplicative›.toContainsIdentities
  letI : S.IsStableUnderComposition := ‹S.IsMultiplicative›.toIsStableUnderComposition
  letI : Preadditive S.Localization := inferInstance
  letI : HasZeroObject S.Localization := inferInstance
  letI : HasShift S.Localization ℤ := inferInstance
  letI : ∀ n : ℤ, (shiftFunctor S.Localization n).Additive := inferInstance
  letI : Pretriangulated S.Localization := inferInstance
  letI := Localization.inverts S.Q S T.mor₁ hS
  have hTQ : S.Q.mapTriangle.obj T ∈ distTriang S.Localization :=
    S.Q.map_distinguished T hT
  have hzero₃ : IsZero ((S.Q.mapTriangle.obj T).obj₃) := by
    exact Triangle.isZero₃_of_isIso₁ (S.Q.mapTriangle.obj T) hTQ <| by
      change IsIso (S.Q.map T.mor₁)
      infer_instance
  let rQ : Retract (S.Q.obj Z) (S.Q.obj T.obj₃) := Retract.map r S.Q
  -- A retract of a zero object is zero.
  exact IsZero.of_mono rQ.i (by simpa using hzero₃)

/-- Lemma 13.5.9: for a pretriangulated category `D`, a multiplicative system `S` compatible with
the triangulated structure, and an object `Z` of `D`, the following are equivalent: `S.Q.obj Z`
is zero; some zero morphism `0 : Z ⟶ Z'` lies in `S`; some zero morphism `0 : Z' ⟶ Z` lies in
`S`; and `Z` is a retract, hence a direct summand, of the third term of a distinguished triangle
whose first morphism lies in `S`. -/
theorem localization_object_isZero_tfae_of_compatibleWithTriangulation
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      ] := by
  let P1 : Prop := IsZero (S.Q.obj Z)
  let P2 : Prop := ∃ Z' : D, S (0 : Z ⟶ Z')
  let P3 : Prop := ∃ Z' : D, S (0 : Z' ⟶ Z)
  let P4 : Prop := ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
  have hbase := localization_object_isZero_tfae S Z
  have h12 : P1 ↔ P2 := by
    simpa [P1, P2] using hbase.out 0 1
  have h13 : P1 ↔ P3 := by
    simpa [P1, P3] using hbase.out 0 2
  have h14 : P1 ↔ P4 := by
    constructor
    · intro hZ
      rcases h12.1 hZ with ⟨Z', hzero⟩
      exact exists_distinguished_retract_of_zero_to_mem (S := S) hzero
    · rintro ⟨T, hT, hmor, ⟨r⟩⟩
      exact isZero_localization_obj_of_distinguished_retract (S := S) hT hmor r
  refine List.tfae_of_forall P1 [P1, P2, P3, P4] ?_
  intro a ha
  simp only [P1, P2, P3, P4, List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  rcases ha with rfl | ha
  · exact h12.symm
  rcases ha with rfl | ha
  · exact h13.symm
  rcases ha with rfl | ha
  · exact h14.symm
  cases ha

-- Proof sketch: under saturation, Lemma `4.27.21` identifies `S` with the inverse image of the
-- isomorphisms under `S.Q`; hence the maps `0 ⟶ Z` and `Z ⟶ 0` lie in `S` exactly when
-- `S.Q.obj Z` is zero. The triangle `(0, Z, Z, 0, 𝟙 Z, 0)` is distinguished, so these zero-object
-- conditions are equivalent to the existence of a distinguished triangle with third vertex `Z`
-- whose first morphism lies in `S`.
/-- Helper for Lemma 13.5.9: in a saturated system, if `S.Q.obj Z` is zero then the canonical
zero morphism `0 ⟶ Z` already lies in `S`. -/
lemma zero_from_zero_localization_mem [IsSaturatedMultiplicativeSystem S]
    (hZ : IsZero (S.Q.obj Z)) :
    S (0 : 0 ⟶ Z) := by
  have hzero₀ : IsZero (S.Q.obj (0 : D)) := by
    simpa using Functor.map_isZero S.Q (isZero_zero D)
  have hsaturated : S.saturatedClosure (0 : 0 ⟶ Z) := by
    exact hzero₀.isIso hZ _
  exact (saturatedClosure_le S le_rfl) _ hsaturated

/-- Helper for Lemma 13.5.9: in a saturated system, if `S.Q.obj Z` is zero then the canonical
zero morphism `Z ⟶ 0` already lies in `S`. -/
lemma zero_to_zero_localization_mem [IsSaturatedMultiplicativeSystem S]
    (hZ : IsZero (S.Q.obj Z)) :
    S (0 : Z ⟶ 0) := by
  have hzero₀ : IsZero (S.Q.obj (0 : D)) := by
    simpa using Functor.map_isZero S.Q (isZero_zero D)
  have hsaturated : S.saturatedClosure (0 : Z ⟶ 0) := by
    exact hZ.isIso hzero₀ _
  exact (saturatedClosure_le S le_rfl) _ hsaturated

/-- If `S` is saturated, the preceding zero-object criterion is also equivalent to the canonical
zero morphisms `0 ⟶ Z` and `Z ⟶ 0` lying in `S`, and to the existence of a distinguished triangle
with third vertex exactly `Z` whose first morphism belongs to `S`. -/
theorem localization_object_isZero_tfae_of_saturated_compatibleWithTriangulation
    [IsSaturatedMultiplicativeSystem S] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      , S (0 : 0 ⟶ Z)
      , S (0 : Z ⟶ 0)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ T.obj₃ = Z
      ] := by
  let P1 : Prop := IsZero (S.Q.obj Z)
  let P2 : Prop := ∃ Z' : D, S (0 : Z ⟶ Z')
  let P3 : Prop := ∃ Z' : D, S (0 : Z' ⟶ Z)
  let P4 : Prop := ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
  let P5 : Prop := S (0 : 0 ⟶ Z)
  let P6 : Prop := S (0 : Z ⟶ 0)
  let P7 : Prop := ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ T.obj₃ = Z
  have hbase : List.TFAE [P1, P2, P3, P4] := by
    simpa [P1, P2, P3, P4] using
      localization_object_isZero_tfae_of_compatibleWithTriangulation (S := S) Z
  have h12 : P1 ↔ P2 := by
    simpa [P1, P2] using hbase.out 0 1
  have h13 : P1 ↔ P3 := by
    simpa [P1, P3] using hbase.out 0 2
  have h14 : P1 ↔ P4 := by
    simpa [P1, P4] using hbase.out 0 3
  have h15 : P1 ↔ P5 := by
    constructor
    · intro hZ
      exact zero_from_zero_localization_mem (S := S) (Z := Z) hZ
    · intro hzero
      exact h13.2 ⟨0, hzero⟩
  have h16 : P1 ↔ P6 := by
    constructor
    · intro hZ
      exact zero_to_zero_localization_mem (S := S) (Z := Z) hZ
    · intro hzero
      exact h12.2 ⟨0, hzero⟩
  have h57 : P5 → P7 := by
    intro hzero
    refine ⟨Triangle.mk (0 : 0 ⟶ Z) (𝟙 Z) 0, ?_⟩
    refine ⟨?_, ?_, rfl⟩
    · -- The contractible triangle witnesses the strict third-vertex clause.
      simpa using contractible_distinguished₁ Z
    · simpa using hzero
  have h71 : P7 → P1 := by
    rintro ⟨T, hT, hmor, hobj₃⟩
    have h4 : P4 := by
      refine ⟨T, hT, hmor, ?_⟩
      cases hobj₃
      exact ⟨Retract.refl _⟩
    exact h14.2 h4
  have h17 : P1 ↔ P7 := by
    constructor
    · intro hZ
      exact h57 (h15.1 hZ)
    · exact h71
  refine List.tfae_of_forall P1 [P1, P2, P3, P4, P5, P6, P7] ?_
  intro a ha
  simp only [P1, P2, P3, P4, P5, P6, P7, List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  rcases ha with rfl | ha
  · exact h12.symm
  rcases ha with rfl | ha
  · exact h13.symm
  rcases ha with rfl | ha
  · exact h14.symm
  rcases ha with rfl | ha
  · exact h15.symm
  rcases ha with rfl | ha
  · exact h16.symm
  rcases ha with rfl | ha
  · exact h17.symm
  cases ha

end

end CategoryTheory
