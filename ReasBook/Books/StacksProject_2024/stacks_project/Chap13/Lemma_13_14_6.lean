import StacksProject_2024.Chap04.Lemma_4_22_9
import StacksProject_2024.Chap04.Lemma_4_22_10
import StacksProject_2024.Chap13.Situation_13_14_1
import StacksProject_2024.Chap13.Lemma_13_14_3
import StacksProject_2024.Chap13.Lemma_13_14_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section RightTwoOutOfThree

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D'] (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/- Domain-style sampling:
- primary domain: pointwise left/right derived functors in a triangulated localization situation;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.IsTriangulated`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `ObjectProperty.IsTriangulatedClosed₁`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `ObjectProperty.IsTriangulatedClosed₃`,
  `rightDerivedValueMap`,
  `leftDerivedValueMap`,
  `rightDerivedValueShiftIso`,
  `leftDerivedValueShiftIso`;
- best owner abstraction: the pointwise-definedness predicates should be treated as
  `ObjectProperty` owners on `D`, namely `rightDerivedDefinedObjectProperty F S` and
  `leftDerivedDefinedObjectProperty F S`; their distinguished-triangle closure belongs first in
  the canonical owner interfaces `IsTriangulatedClosed₁/₂/₃`, while the induced morphisms and
  shift comparison isomorphisms already belong to `Lemma_13_14_3` and `Lemma_13_14_5`.

Primitive data are a distinguished triangle in `D` and pointwise-definedness on two of its
vertices. The maps on derived values and the shift comparison are derived/canonical upstream API,
so they should be reused from their owner files rather than repeated here as parallel local
declarations.
-/

/-- Helper for Lemma 13.14.6: from a chosen distinguished triangle on `RF(T.mor₁)`, the
denominator-triangle/five-lemma argument should produce an essentially constant colimit cocone on
the third right-derived indexing diagram with vertex `C`. -/
lemma right_derived_third_vertex_cocone_hom_colimit_comparison
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    {C : D'} {b : rightDerivedValue S F T.obj₂ ⟶ C}
    {c : C ⟶ (rightDerivedValue S F T.obj₁)⟦(1 : ℤ)⟧}
    (hT0 : Triangle.mk (rightDerivedValueMap S F T.mor₁) b c ∈ distTriang D') :
    ∃ cZ : ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj T.obj₃) ⋙ F),
      cZ.cocone.pt = C ∧ IsEssentiallyConstantFilteredCocone cZ.cocone := by
  -- Route correction: the source proof runs through denominator triangles and a Hom-colimit
  -- comparison, but the local Chapter 13 API wants an actual colimit cocone on the third vertex.
  -- TODO: build the cocone from the third components of `TR3` morphisms over
  -- `distinguished_triangle_denominators S T`, prove its Hom-colimit comparison by exactness and
  -- the five lemma, and then convert that comparison into an essentially constant colimit cocone
  -- with vertex `C` using `Lemma_4.22.9`.
  sorry

-- Proof sketch: the source proof first chooses a distinguished triangle on `RF(T.mor₁)` and then
-- uses the denominator-triangle argument to turn its third vertex into a colimit cocone for the
-- third indexing diagram. This helper isolates exactly that prefix.
/-- Helper for Lemma 13.14.6: if the right-derived functor is defined at the first two vertices
of a distinguished triangle, then the source-faithful third-vertex cocone construction yields the
missing pointwise right-derived value. -/
lemma hasPointwiseRightDerivedFunctorAt_of_distTriangle_two_vertices
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂] :
    F.HasPointwiseRightDerivedFunctorAt S T.obj₃ := by
  -- Proof comment: choose a distinguished triangle on `RF(T.mor₁)` and pass to the structural
  -- helper that constructs the third colimit cocone.
  obtain ⟨C, b, c, hT0⟩ := distinguished_cocone_triangle (rightDerivedValueMap S F T.mor₁)
  rcases right_derived_third_vertex_cocone_hom_colimit_comparison
      (F := F) (S := S) (T := T) hT hT0 with
    ⟨cZ, _, _⟩
  -- Proof comment: a colimit cocone on the third indexing diagram is exactly the pointwise
  -- right-derived-definedness datum at `T.obj₃`.
  exact ⟨show HasPointwiseLeftKanExtensionAt S.Q F (S.Q.obj T.obj₃) from HasColimit.mk cZ⟩

-- Proof sketch: choose the missing derived value by completing the image of the distinguished
-- triangle under `F` to a distinguished triangle in `D'`, then use the exactness of filtered
-- colimits on Hom groups together with the five lemma to show the third vertex computes the
-- remaining pointwise right-derived value.
/-- The pointwise right-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (rightDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₃.mk' ?_
  intro T hT h₁ h₂
  let _ : F.HasPointwiseRightDerivedFunctorAt S T.obj₁ := h₁
  let _ : F.HasPointwiseRightDerivedFunctorAt S T.obj₂ := h₂
  -- Proof comment: the new helper packages the source-faithful prefix of the proof, so the only
  -- unresolved work remains inside the structural Hom-colimit comparison lemma.
  exact hasPointwiseRightDerivedFunctorAt_of_distTriangle_two_vertices
    (F := F) (S := S) (T := T) hT

-- Proof sketch: rotate the distinguished triangle once, apply the previous clause to the rotated
-- triangle, and use Lemma `13.14.5` to move pointwise right-derived definedness from `X⟦1⟧`
-- back to `X`.
/-- The pointwise right-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (rightDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₁.mk' ?_
  intro T hT h₂ h₃
  -- Rotate once so the missing first vertex becomes the third vertex after a shift.
  have h₁_shift :
      F.HasPointwiseRightDerivedFunctorAt S (T.obj₁⟦(1 : ℤ)⟧) := by
    simpa using
      (rightDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃
        T.rotate (rot_of_distTriang _ hT) h₂ h₃
  -- Move the result back along the shift-invariance from Lemma 13.14.5.
  exact (hasPointwiseRightDerivedFunctorAt_iff_shift F S T.obj₁ (1 : ℤ)).2 h₁_shift

-- Proof sketch: rotate the distinguished triangle twice and apply the main two-out-of-three
-- clause together with Lemma `13.14.5`.
/-- The pointwise right-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (rightDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₂.mk' ?_
  intro T hT h₁ h₃
  -- In the inverse rotation, the original third vertex becomes the shifted first vertex.
  have h₃_shift :
      F.HasPointwiseRightDerivedFunctorAt S (T.obj₃⟦(-1 : ℤ)⟧) := by
    exact (hasPointwiseRightDerivedFunctorAt_iff_shift F S T.obj₃ (-1 : ℤ)).1 h₃
  -- Apply the third-vertex clause to the inverse rotation.
  simpa using
    (rightDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃
      T.invRotate (inv_rot_of_distTriang _ hT) h₃_shift h₁

end RightTwoOutOfThree

section RightDistinguished

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

variable {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}

/-- Helper for Lemma 13.14.6: once the chosen third vertex `C` is known to compute the missing
right-derived value, the chosen distinguished triangle on `RF(f)` should be identified with the
canonical right-derived triangle. -/
noncomputable def right_derived_candidate_triangle_iso
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃]
    {C : D'} {b : rightDerivedValue S F T.obj₂ ⟶ C}
    {c : C ⟶ (rightDerivedValue S F T.obj₁)⟦(1 : ℤ)⟧}
    (hT0 : Triangle.mk (rightDerivedValueMap S F T.mor₁) b c ∈ distTriang D') :
    Triangle.mk (rightDerivedValueMap S F T.mor₁) b c ≅
      Triangle.mk (rightDerivedValueMap S F T.mor₁) (rightDerivedValueMap S F T.mor₂)
        (rightDerivedValueMap S F T.mor₃ ≫
          (rightDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
  -- Route correction: the remaining task is no longer to construct the third derived value, but
  -- to compare the chosen distinguished triangle to the canonical one built from
  -- `rightDerivedValueMap`.
  -- TODO: extract the comparison isomorphism `C ≅ rightDerivedValue S F T.obj₃` from the
  -- denominator-triangle colimit cocone, then use `rightDerivedValueMap_hom_ext` and the shift
  -- compatibility square to verify the second and third morphisms of the canonical triangle.
  sorry

-- Proof sketch: after the two-out-of-three existence statement, the pointwise right-derived
-- values and their induced maps are defined on the whole triangle. The exactness of `F` and the
-- universal-property construction of the pointwise derived values show that the canonical shift
-- comparison from Lemma `13.14.5` makes the induced triangle distinguished.
/-- Lemma 13.14.6 (2): once the pointwise right derived values on a distinguished triangle are
defined, the induced triangle on right-derived values is distinguished in `D'`. -/
theorem right_derived_triangle_distinguished
    (hT : Triangle.mk f g h ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S Z] :
    Triangle.mk (rightDerivedValueMap S F f) (rightDerivedValueMap S F g)
      (rightDerivedValueMap S F h ≫ (rightDerivedValueShiftIso F S X (1 : ℤ)).hom) ∈
        distTriang D' := by
  let T : Triangle D := Triangle.mk f g h
  letI : F.HasPointwiseRightDerivedFunctorAt S T.obj₁ := by
    simpa [T] using (show F.HasPointwiseRightDerivedFunctorAt S X from inferInstance)
  letI : F.HasPointwiseRightDerivedFunctorAt S T.obj₂ := by
    simpa [T] using (show F.HasPointwiseRightDerivedFunctorAt S Y from inferInstance)
  letI : F.HasPointwiseRightDerivedFunctorAt S T.obj₃ := by
    simpa [T] using (show F.HasPointwiseRightDerivedFunctorAt S Z from inferInstance)
  -- Proof comment: choose a distinguished triangle on `RF(f)` and transport distinguishedness
  -- across the comparison isomorphism to the canonical right-derived triangle.
  obtain ⟨C, b, c, hT0⟩ := distinguished_cocone_triangle (rightDerivedValueMap S F f)
  let e :=
    right_derived_candidate_triangle_iso
      (F := F) (S := S) (T := T) (by simpa [T] using hT) hT0
  exact (distinguished_iff_of_iso e).mp hT0

end RightDistinguished

section LeftTwoOutOfThree

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D'] (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/-- Helper for Lemma 13.14.6: from a chosen distinguished triangle on `LF(T.mor₁)`, the dual
denominator-triangle/five-lemma argument should produce an essentially constant limit cone on the
third left-derived indexing diagram with vertex `C`. -/
lemma left_derived_third_vertex_cone_hom_colimit_comparison
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    {C : D'} {b : leftDerivedValue S F T.obj₂ ⟶ C}
    {c : C ⟶ (leftDerivedValue S F T.obj₁)⟦(1 : ℤ)⟧}
    (hT0 : Triangle.mk (leftDerivedValueMap S F T.mor₁) b c ∈ distTriang D') :
    ∃ cZ : LimitCone (StructuredArrow.proj (S.Q.obj T.obj₃) S.Q ⋙ F),
      cZ.cone.pt = C ∧ IsEssentiallyConstantCofilteredCone cZ.cone := by
  -- Route correction: the dual source proof should now be packaged as an actual limit cone on the
  -- third vertex, rather than left as a raw Hom-comparison statement.
  -- TODO: build the cone from the third components of `TR3` morphisms in the opposite
  -- orientation, prove the required Hom-colimit comparison by the dual five-lemma argument, and
  -- convert it to an essentially constant limit cone with vertex `C` using `Lemma_4.22.10`.
  sorry

-- Proof sketch: this is the dual of the right-derived prefix. Choose a distinguished triangle on
-- `LF(T.mor₁)` and use the structural denominator-triangle argument to package its third vertex as
-- a limiting cone for the third indexing diagram.
/-- Helper for Lemma 13.14.6: if the left-derived functor is defined at the first two vertices of
a distinguished triangle, then the dual third-vertex cone construction yields the missing
pointwise left-derived value. -/
lemma hasPointwiseLeftDerivedFunctorAt_of_distTriangle_two_vertices
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂] :
    F.HasPointwiseLeftDerivedFunctorAt S T.obj₃ := by
  -- Proof comment: choose a distinguished triangle on `LF(T.mor₁)` and invoke the dual
  -- structural helper to obtain a limit cone at the third vertex.
  obtain ⟨C, b, c, hT0⟩ := distinguished_cocone_triangle (leftDerivedValueMap S F T.mor₁)
  rcases left_derived_third_vertex_cone_hom_colimit_comparison
      (F := F) (S := S) (T := T) hT hT0 with
    ⟨cZ, _, _⟩
  -- Proof comment: a limit cone on the third indexing diagram is exactly the pointwise
  -- left-derived-definedness datum at `T.obj₃`.
  exact ⟨show HasPointwiseRightKanExtensionAt S.Q F (S.Q.obj T.obj₃) from HasLimit.mk cZ⟩

-- Proof sketch: this is the dual two-out-of-three argument for pointwise left derived functors,
-- replacing filtered colimits by filtered limits and using the exactness criterion on Hom groups
-- against the completed distinguished triangle in `D'`.
/-- The pointwise left-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (leftDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₃.mk' ?_
  intro T hT h₁ h₂
  let _ : F.HasPointwiseLeftDerivedFunctorAt S T.obj₁ := h₁
  let _ : F.HasPointwiseLeftDerivedFunctorAt S T.obj₂ := h₂
  -- Proof comment: the dual helper isolates the already-verified prefix, leaving only the
  -- denominator-triangle Hom-comparison as the genuine open blocker.
  exact hasPointwiseLeftDerivedFunctorAt_of_distTriangle_two_vertices
    (F := F) (S := S) (T := T) hT

-- Proof sketch: rotate the distinguished triangle once, apply the preceding left-derived clause
-- to the rotated triangle, and use Lemma `13.14.5` to move pointwise left-derived definedness
-- from `X⟦1⟧` back to `X`.
/-- The pointwise left-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (leftDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₁.mk' ?_
  intro T hT h₂ h₃
  -- Rotate once so the missing first vertex becomes the third vertex after a shift.
  have h₁_shift :
      F.HasPointwiseLeftDerivedFunctorAt S (T.obj₁⟦(1 : ℤ)⟧) := by
    simpa using
      (leftDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃
        T.rotate (rot_of_distTriang _ hT) h₂ h₃
  -- Move the result back along the shift-invariance from Lemma 13.14.5.
  exact (hasPointwiseLeftDerivedFunctorAt_iff_shift F S T.obj₁ (1 : ℤ)).2 h₁_shift

-- Proof sketch: rotate the distinguished triangle twice and apply the main left-derived
-- two-out-of-three clause together with Lemma `13.14.5`.
/-- The pointwise left-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (leftDerivedDefinedObjectProperty F S) := by
  refine IsTriangulatedClosed₂.mk' ?_
  intro T hT h₁ h₃
  -- In the inverse rotation, the original third vertex becomes the shifted first vertex.
  have h₃_shift :
      F.HasPointwiseLeftDerivedFunctorAt S (T.obj₃⟦(-1 : ℤ)⟧) := by
    exact (hasPointwiseLeftDerivedFunctorAt_iff_shift F S T.obj₃ (-1 : ℤ)).1 h₃
  -- Apply the third-vertex clause to the inverse rotation.
  simpa using
    (leftDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₃
      T.invRotate (inv_rot_of_distTriang _ hT) h₃_shift h₁

end LeftTwoOutOfThree

section LeftDistinguished

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

variable {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}

/-- Helper for Lemma 13.14.6: once the chosen third vertex `C` is known to compute the missing
left-derived value, the chosen distinguished triangle on `LF(f)` should be identified with the
canonical left-derived triangle. -/
noncomputable def left_derived_candidate_triangle_iso
    {T : Triangle D} (hT : T ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃]
    {C : D'} {b : leftDerivedValue S F T.obj₂ ⟶ C}
    {c : C ⟶ (leftDerivedValue S F T.obj₁)⟦(1 : ℤ)⟧}
    (hT0 : Triangle.mk (leftDerivedValueMap S F T.mor₁) b c ∈ distTriang D') :
    Triangle.mk (leftDerivedValueMap S F T.mor₁) b c ≅
      Triangle.mk (leftDerivedValueMap S F T.mor₁) (leftDerivedValueMap S F T.mor₂)
        (leftDerivedValueMap S F T.mor₃ ≫
          (leftDerivedValueShiftIso F S T.obj₁ (1 : ℤ)).hom) := by
  -- Route correction: after the dual denominator argument supplies `C ≅ LF(T.obj₃)`, only the
  -- compatibility of the chosen triangle with the canonical `leftDerivedValueMap` triangle
  -- remains.
  -- TODO: use the limit-cone uniqueness comparison from the previous helper together with
  -- `leftDerivedValueMap_hom_ext` and the shift compatibility square to build the required
  -- triangle isomorphism.
  sorry

-- Proof sketch: after the left-derived values are defined on the three objects, exactness of the
-- triangulated functor together with the pointwise left-Kan-extension construction shows that
-- the canonical shift comparison from Lemma `13.14.5` turns the induced sextuple into a
-- distinguished triangle.
/-- Lemma 13.14.6 (4): once the pointwise left derived values on a distinguished triangle are
defined, the induced triangle on left-derived values is distinguished in `D'`. -/
theorem left_derived_triangle_distinguished
    (hT : Triangle.mk f g h ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S Z] :
    Triangle.mk (leftDerivedValueMap S F f) (leftDerivedValueMap S F g)
      (leftDerivedValueMap S F h ≫ (leftDerivedValueShiftIso F S X (1 : ℤ)).hom) ∈
        distTriang D' := by
  let T : Triangle D := Triangle.mk f g h
  letI : F.HasPointwiseLeftDerivedFunctorAt S T.obj₁ := by
    simpa [T] using (show F.HasPointwiseLeftDerivedFunctorAt S X from inferInstance)
  letI : F.HasPointwiseLeftDerivedFunctorAt S T.obj₂ := by
    simpa [T] using (show F.HasPointwiseLeftDerivedFunctorAt S Y from inferInstance)
  letI : F.HasPointwiseLeftDerivedFunctorAt S T.obj₃ := by
    simpa [T] using (show F.HasPointwiseLeftDerivedFunctorAt S Z from inferInstance)
  -- Proof comment: choose a distinguished triangle on `LF(f)` and transport distinguishedness
  -- across the comparison isomorphism to the canonical left-derived triangle.
  obtain ⟨C, b, c, hT0⟩ := distinguished_cocone_triangle (leftDerivedValueMap S F f)
  let e :=
    left_derived_candidate_triangle_iso
      (F := F) (S := S) (T := T) (by simpa [T] using hT) hT0
  exact (distinguished_iff_of_iso e).mp hT0

end LeftDistinguished

end CategoryTheory
