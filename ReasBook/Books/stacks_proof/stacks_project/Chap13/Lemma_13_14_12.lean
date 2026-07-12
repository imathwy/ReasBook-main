import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Lemma_13_14_6
import StacksProject_2024.Chap13.Lemma_13_14_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.14.12:
- primary domain: pointwise computation of right/left derived functors in a triangulated
  localization situation, with closure under distinguished triangles;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.computesRightDerivedObjectProperty`,
  `Functor.computesLeftDerivedObjectProperty`,
  `ObjectProperty.IsTriangulatedClosed₃`,
  `ObjectProperty.ext_of_isTriangulatedClosed₃`;
- best owner abstraction: the source-facing predicates
  `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt` are already organized by the
  Chapter 13 owner object properties `F.computesRightDerivedObjectProperty S` and
  `F.computesLeftDerivedObjectProperty S`; this file should therefore record the third-vertex
  distinguished-triangle closure first as the canonical owner instances
  `IsTriangulatedClosed₃` for those object properties, and only then keep the textbook `obj₃`
  statements as thin wrappers;
- primitive data: a distinguished triangle in `D` and computation hypotheses on its first two
  vertices, where `ComputesRightDerivedAt` / `ComputesLeftDerivedAt` already package the needed
  pointwise derived-definedness together with invertibility of the canonical identity
  leg/projection;
- derived API: the owner-level closure instances and the pointwise `obj₃` consequences.

Source/core/bridge triage:
- `source-facing`: the two textbook `obj₃` closure statements for objects computing the
  right/left derived functor in a distinguished triangle;
- `core/canonical`: the object-property owners
  `F.computesRightDerivedObjectProperty S` / `F.computesLeftDerivedObjectProperty S` together
  with `ObjectProperty.IsTriangulatedClosed₃`;
- `bridge/view`: the two theorem wrappers below, which simply restate the owner-level closure in
  the textbook pointwise form.
-/
variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [hasZeroObjectD' : Limits.HasZeroObject D']
  [HasShift D ℤ] [hasShiftD' : HasShift D' ℤ]
  [Preadditive D] [preadditiveD' : Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [shiftAdditiveD' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [pretriangulatedD' : Pretriangulated D']
  [triangulatedD' : IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [commShiftF : F.CommShift ℤ] [triangulatedF : F.IsTriangulated]
  [satS : IsSaturatedMultiplicativeSystem S] [compatS : S.IsCompatibleWithTriangulation]

section Right

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

/-- Helper for Lemma 13.14.12: the canonical shift comparison for right-derived values sends the
shifted identity leg to the shift of the unshifted identity leg. -/
lemma right_derived_value_shift_iso_hom_naturality_id_leg {X : D}
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    ((F.commShiftIso (1 : ℤ)).app X).hom ≫
        (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)⟦(1 : ℤ)⟧') =
      rightDerivedValueLeg S F (𝟙 (X⟦(1 : ℤ)⟧)) (S.id_mem (X⟦(1 : ℤ)⟧)) ≫
        (rightDerivedValueShiftIso F S X (1 : ℤ)).hom := by
  -- Route correction: the main triangle-comparison argument is already fixed. The remaining
  -- issue is the explicit universal-property computation for the canonical shift isomorphism.
  -- TODO: read off the identity-denominator component of `rightDerivedValueShiftIso` from the
  -- shifted colimit cocone, equivalently strengthening Lemma 13.14.11's existential helper to
  -- this canonical statement.
  sorry

/-- Helper for Lemma 13.14.12: the identity legs define the comparison morphism from the
`F`-image of a triangle to the induced triangle on right-derived values. -/
noncomputable def right_derived_comparison_triangle_morphism
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    F.mapTriangle.obj T ⟶
      Triangle.mk (rightDerivedValueMap S F T.mor₁) (rightDerivedValueMap S F T.mor₂)
        (rightDerivedValueMap S F T.mor₃ ≫ (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
  let u₁ : F.obj T.obj₁ ⟶ rightDerivedValue S F T.obj₁ :=
    rightDerivedValueLeg S F (𝟙 T.obj₁) (S.id_mem T.obj₁)
  let u₂ : F.obj T.obj₂ ⟶ rightDerivedValue S F T.obj₂ :=
    rightDerivedValueLeg S F (𝟙 T.obj₂) (S.id_mem T.obj₂)
  let u₃ : F.obj T.obj₃ ⟶ rightDerivedValue S F T.obj₃ :=
    rightDerivedValueLeg S F (𝟙 T.obj₃) (S.id_mem T.obj₃)
  have sq₁ : CommSq T.mor₁ (𝟙 T.obj₁) (𝟙 T.obj₂) T.mor₁ := by
    simpa
  have comm₁ :
      F.map T.mor₁ ≫ u₂ = u₁ ≫ rightDerivedValueMap S F T.mor₁ := by
    -- The first square is the identity-denominator case of the universal compatibility square.
    simpa [u₁, u₂] using
      (show CommSq u₁ (F.map T.mor₁) (rightDerivedValueMap S F T.mor₁) u₂ from
        rightDerivedValueMap_comp_of_square S F T.mor₁
          (𝟙 T.obj₁) (𝟙 T.obj₂) (S.id_mem T.obj₁) (S.id_mem T.obj₂) T.mor₁ sq₁).w.symm
  have sq₂ : CommSq T.mor₂ (𝟙 T.obj₂) (𝟙 T.obj₃) T.mor₂ := by
    simpa
  have comm₂ :
      F.map T.mor₂ ≫ u₃ = u₂ ≫ rightDerivedValueMap S F T.mor₂ := by
    -- The second square is the same identity-denominator compatibility for `T.mor₂`.
    simpa [u₂, u₃] using
      (show CommSq u₂ (F.map T.mor₂) (rightDerivedValueMap S F T.mor₂) u₃ from
        rightDerivedValueMap_comp_of_square S F T.mor₂
          (𝟙 T.obj₂) (𝟙 T.obj₃) (S.id_mem T.obj₂) (S.id_mem T.obj₃) T.mor₂ sq₂).w.symm
  have h_shift :
      ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom ≫ u₁⟦(1 : ℤ)⟧' =
        rightDerivedValueLeg S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) ≫
          (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom := by
    -- The third square uses the explicit compatibility of the canonical shift isomorphism
    -- with the identity-denominator leg at `T.obj₁`.
    simpa [u₁] using
      right_derived_value_shift_iso_hom_naturality_id_leg (F := F) (S := S) (X := T.obj₁)
  have sq₃ :
      CommSq T.mor₃ (𝟙 T.obj₃) (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) T.mor₃ := by
    simpa
  have h_mor₃ :
      F.map T.mor₃ ≫
          rightDerivedValueLeg S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) =
        u₃ ≫ rightDerivedValueMap S F T.mor₃ := by
    -- This is the identity-denominator square for the connecting morphism `T.mor₃`.
    simpa [u₃] using
      (show CommSq u₃ (F.map T.mor₃) (rightDerivedValueMap S F T.mor₃)
          (rightDerivedValueLeg S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧))) from
        rightDerivedValueMap_comp_of_square S F T.mor₃
          (𝟙 T.obj₃) (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem T.obj₃) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧))
          T.mor₃ sq₃).w.symm
  have comm₃ :
      (F.map T.mor₃ ≫ ((F.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ≫ u₁⟦(1 : ℤ)⟧' =
        u₃ ≫
          (rightDerivedValueMap S F T.mor₃ ≫ (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
    -- Rewrite the shift comparison first, then use the identity-denominator square for `T.mor₃`.
    calc
      (F.map T.mor₃ ≫ ((F.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ≫ u₁⟦(1 : ℤ)⟧' =
          F.map T.mor₃ ≫
            (((F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ u₁⟦(1 : ℤ)⟧') := by
              simp [Category.assoc]
      _ = F.map T.mor₃ ≫
            (rightDerivedValueLeg S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) ≫
              (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
            simpa [Category.assoc] using congrArg (fun k ↦ F.map T.mor₃ ≫ k) h_shift
      _ = (F.map T.mor₃ ≫
            rightDerivedValueLeg S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧))) ≫
            (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom := by
              simp [Category.assoc]
      _ = (u₃ ≫ rightDerivedValueMap S F T.mor₃) ≫
            (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom := by
              rw [h_mor₃]
      _ = u₃ ≫
            (rightDerivedValueMap S F T.mor₃ ≫ (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
              simp [Category.assoc]
  exact Triangle.homMk _ _ u₁ u₂ u₃ comm₁ comm₂ comm₃

-- Proof sketch: the underlying pointwise right-derived-definedness already satisfies the
-- third-vertex closure by Lemma `13.14.6`. To upgrade from definedness to computation, compare
-- the `F`-image triangle with the induced triangle on pointwise right-derived values; the first
-- two vertical maps are isomorphisms by the hypotheses on `X` and `Y`, so
-- `Pretriangulated.isIso₃_of_isIso₁₂` gives the third one and hence the required unit
-- isomorphism at `Z`.
/-- Objects computing the right derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesRightDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesRightDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  letI : F.ComputesRightDerivedAt S T.obj₁ := h₁
  letI : F.ComputesRightDerivedAt S T.obj₂ := h₂
  have h₃_defined : F.HasPointwiseRightDerivedFunctorAt S T.obj₃ := by
    -- First recover pointwise right-derived existence at the third vertex from Lemma 13.14.6.
    exact
      (rightDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃ T hT
        h₁.toHasPointwiseRightDerivedFunctorAt h₂.toHasPointwiseRightDerivedFunctorAt
  letI : F.HasPointwiseRightDerivedFunctorAt S T.obj₃ := h₃_defined
  let φ := right_derived_comparison_triangle_morphism (F := F) (S := S) T
  refine
    { toHasPointwiseRightDerivedFunctorAt := h₃_defined
      isIso_rightDerivedValueLeg := ?_ }
  -- Apply the five-lemma analogue to the comparison morphism of distinguished triangles.
  have hdist_derived :
      Triangle.mk (rightDerivedValueMap S F T.mor₁) (rightDerivedValueMap S F T.mor₂)
          (rightDerivedValueMap S F T.mor₃ ≫ (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) ∈
        distTriang D' := by
    simpa using right_derived_triangle_distinguished
      (F := F) (S := S) (X := T.obj₁) (Y := T.obj₂) (Z := T.obj₃)
      (f := T.mor₁) (g := T.mor₂) (h := T.mor₃) hT
  have hφ₃ : IsIso φ.hom₃ := by
    letI : IsIso φ.hom₁ := by
      change IsIso (rightDerivedValueLeg S F (𝟙 T.obj₁) (S.id_mem T.obj₁))
      infer_instance
    letI : IsIso φ.hom₂ := by
      change IsIso (rightDerivedValueLeg S F (𝟙 T.obj₂) (S.id_mem T.obj₂))
      infer_instance
    exact
      Pretriangulated.isIso₃_of_isIso₁₂ φ
        (F.map_distinguished T hT)
        hdist_derived
        inferInstance inferInstance
  simpa [φ] using hφ₃

end Right

section Left

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

/-- Helper for Lemma 13.14.12: the canonical shift comparison for left-derived values sends the
shift of the identity projection to the identity projection at the shifted object. -/
lemma left_derived_value_shift_iso_hom_naturality_id_projection {X : D}
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (leftDerivedValueShiftIso F S X (1 : ℤ)).hom ≫
        (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)⟦(1 : ℤ)⟧') =
      leftDerivedValueProjection S F (𝟙 (X⟦(1 : ℤ)⟧)) (S.id_mem (X⟦(1 : ℤ)⟧)) ≫
        ((F.commShiftIso (1 : ℤ)).app X).hom := by
  -- Route correction: as in the right-derived case, the main comparison proof is already set.
  -- TODO: compute the identity-denominator component of `leftDerivedValueShiftIso` directly
  -- from the shifted limit cone, upgrading Lemma 13.14.11's existential statement to this
  -- canonical formula.
  sorry

/-- Helper for Lemma 13.14.12: the identity projections define the comparison morphism from the
triangle on left-derived values to the `F`-image triangle. -/
noncomputable def left_derived_comparison_triangle_morphism
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    Triangle.mk (leftDerivedValueMap S F T.mor₁) (leftDerivedValueMap S F T.mor₂)
        (leftDerivedValueMap S F T.mor₃ ≫ (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) ⟶
      F.mapTriangle.obj T := by
  let p₁ : leftDerivedValue S F T.obj₁ ⟶ F.obj T.obj₁ :=
    leftDerivedValueProjection S F (𝟙 T.obj₁) (S.id_mem T.obj₁)
  let p₂ : leftDerivedValue S F T.obj₂ ⟶ F.obj T.obj₂ :=
    leftDerivedValueProjection S F (𝟙 T.obj₂) (S.id_mem T.obj₂)
  let p₃ : leftDerivedValue S F T.obj₃ ⟶ F.obj T.obj₃ :=
    leftDerivedValueProjection S F (𝟙 T.obj₃) (S.id_mem T.obj₃)
  have sq₁ : CommSq (𝟙 T.obj₁) T.mor₁ T.mor₁ (𝟙 T.obj₂) := by
    simpa
  have comm₁ :
      leftDerivedValueMap S F T.mor₁ ≫ p₂ = p₁ ≫ F.map T.mor₁ := by
    -- The first square is the identity-denominator case of the left-derived compatibility square.
    simpa [p₁, p₂] using
      (show CommSq (leftDerivedValueMap S F T.mor₁) p₁ p₂ (F.map T.mor₁) from
        leftDerivedValueMap_comp_of_square S F T.mor₁
          (𝟙 T.obj₁) (𝟙 T.obj₂) (S.id_mem T.obj₁) (S.id_mem T.obj₂) T.mor₁ sq₁).w
  have sq₂ : CommSq (𝟙 T.obj₂) T.mor₂ T.mor₂ (𝟙 T.obj₃) := by
    simpa
  have comm₂ :
      leftDerivedValueMap S F T.mor₂ ≫ p₃ = p₂ ≫ F.map T.mor₂ := by
    -- The second square is the same identity-denominator compatibility for `T.mor₂`.
    simpa [p₂, p₃] using
      (show CommSq (leftDerivedValueMap S F T.mor₂) p₂ p₃ (F.map T.mor₂) from
        leftDerivedValueMap_comp_of_square S F T.mor₂
          (𝟙 T.obj₂) (𝟙 T.obj₃) (S.id_mem T.obj₂) (S.id_mem T.obj₃) T.mor₂ sq₂).w
  have h_shift :
      (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom ≫ p₁⟦(1 : ℤ)⟧' =
        leftDerivedValueProjection S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) ≫
          ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom := by
    -- The third square uses the explicit compatibility of the canonical shift isomorphism
    -- with the identity projection at `T.obj₁`.
    simpa [p₁] using
      left_derived_value_shift_iso_hom_naturality_id_projection
        (F := F) (S := S) (X := T.obj₁)
  have sq₃ :
      CommSq (𝟙 T.obj₃) T.mor₃ T.mor₃ (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) := by
    simpa
  have h_mor₃ :
      leftDerivedValueMap S F T.mor₃ ≫
          leftDerivedValueProjection S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) =
        p₃ ≫ F.map T.mor₃ := by
    -- This is the identity-denominator square for the connecting morphism `T.mor₃`.
    simpa [p₃] using
      (show CommSq (leftDerivedValueMap S F T.mor₃) p₃
          (leftDerivedValueProjection S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)))
          (F.map T.mor₃) from
        leftDerivedValueMap_comp_of_square S F T.mor₃
          (𝟙 T.obj₃) (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem T.obj₃) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧))
          T.mor₃ sq₃).w
  have comm₃ :
      (leftDerivedValueMap S F T.mor₃ ≫ (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) ≫
          p₁⟦(1 : ℤ)⟧' =
        p₃ ≫ (F.map T.mor₃ ≫ ((F.commShiftIso (1 : ℤ)).hom.app T.obj₁)) := by
    -- Rewrite the shift comparison first, then use the identity-denominator square for `T.mor₃`.
    calc
      (leftDerivedValueMap S F T.mor₃ ≫ (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) ≫
          p₁⟦(1 : ℤ)⟧' =
        leftDerivedValueMap S F T.mor₃ ≫
          ((leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom ≫ p₁⟦(1 : ℤ)⟧') := by
            simp [Category.assoc]
      _ = leftDerivedValueMap S F T.mor₃ ≫
          (leftDerivedValueProjection S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧)) ≫
            ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom) := by
            simpa [Category.assoc] using congrArg (fun k ↦ leftDerivedValueMap S F T.mor₃ ≫ k) h_shift
      _ = (leftDerivedValueMap S F T.mor₃ ≫
          leftDerivedValueProjection S F (𝟙 (T.obj₁⟦(1 : ℤ)⟧)) (S.id_mem (T.obj₁⟦(1 : ℤ)⟧))) ≫
            ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom := by
              simp [Category.assoc]
      _ = (p₃ ≫ F.map T.mor₃) ≫ ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom := by
            rw [h_mor₃]
      _ = p₃ ≫ (F.map T.mor₃ ≫ ((F.commShiftIso (1 : ℤ)).app T.obj₁).hom) := by
            simp [Category.assoc]
  exact Triangle.homMk _ _ p₁ p₂ p₃ comm₁ comm₂ comm₃

-- Proof sketch: this is the dual owner-level closure statement. Lemma `13.14.6` gives
-- pointwise left-derived existence at the third vertex, and the comparison morphism of
-- distinguished triangles has isomorphic first two components by the hypotheses that `X` and
-- `Y` compute `LF`; two-out-of-three gives the third component, i.e. the identity projection at
-- `Z`.
/-- Objects computing the left derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesLeftDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesLeftDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  letI : F.ComputesLeftDerivedAt S T.obj₁ := h₁
  letI : F.ComputesLeftDerivedAt S T.obj₂ := h₂
  have h₃_defined : F.HasPointwiseLeftDerivedFunctorAt S T.obj₃ := by
    -- First recover pointwise left-derived existence at the third vertex from Lemma 13.14.6.
    exact
      (leftDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃ T hT
        h₁.toHasPointwiseLeftDerivedFunctorAt h₂.toHasPointwiseLeftDerivedFunctorAt
  letI : F.HasPointwiseLeftDerivedFunctorAt S T.obj₃ := h₃_defined
  let φ := left_derived_comparison_triangle_morphism (F := F) (S := S) T
  refine
    { toHasPointwiseLeftDerivedFunctorAt := h₃_defined
      isIso_leftDerivedValueProjection := ?_ }
  -- Apply the five-lemma analogue to the dual comparison morphism of distinguished triangles.
  have hdist_derived :
      Triangle.mk (leftDerivedValueMap S F T.mor₁) (leftDerivedValueMap S F T.mor₂)
          (leftDerivedValueMap S F T.mor₃ ≫ (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) ∈
        distTriang D' := by
    simpa using left_derived_triangle_distinguished
      (F := F) (S := S) (X := T.obj₁) (Y := T.obj₂) (Z := T.obj₃)
      (f := T.mor₁) (g := T.mor₂) (h := T.mor₃) hT
  have hφ₃ : IsIso φ.hom₃ := by
    letI : IsIso φ.hom₁ := by
      change IsIso (leftDerivedValueProjection S F (𝟙 T.obj₁) (S.id_mem T.obj₁))
      infer_instance
    letI : IsIso φ.hom₂ := by
      change IsIso (leftDerivedValueProjection S F (𝟙 T.obj₂) (S.id_mem T.obj₂))
      infer_instance
    exact
      Pretriangulated.isIso₃_of_isIso₁₂ φ
        hdist_derived
        (F.map_distinguished T hT)
        inferInstance inferInstance
  simpa [φ] using hφ₃

end Left

end

section SourceFacing

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [IsSaturatedMultiplicativeSystem S]

/-- Lemma 13.14.12 (1): if `T` is a distinguished triangle of `D` and its first two vertices
compute the right derived functor of `F` with respect to `S`, then so does its third vertex. -/
@[stacks 05SZ]
theorem computesRightDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesRightDerivedAt S T.obj₁)
    (h₂ : F.ComputesRightDerivedAt S T.obj₂) :
    F.ComputesRightDerivedAt S T.obj₃ := by
  exact (F.computesRightDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 13.14.12 (2): if `T` is a distinguished triangle of `D` and its first two vertices
compute the left derived functor of `F` with respect to `S`, then so does its third vertex. -/
@[stacks 05SZ]
theorem computesLeftDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesLeftDerivedAt S T.obj₁)
    (h₂ : F.ComputesLeftDerivedAt S T.obj₂) :
    F.ComputesLeftDerivedAt S T.obj₃ := by
  exact (F.computesLeftDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

end SourceFacing

end CategoryTheory
