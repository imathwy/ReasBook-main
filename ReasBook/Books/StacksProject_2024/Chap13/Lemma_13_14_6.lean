import stacks_project.Chap13.Situation_13_14_1
import stacks_project.Chap13.Lemma_13_14_3
import stacks_project.Chap13.Lemma_13_14_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
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

-- Proof sketch: choose the missing derived value by completing the image of the distinguished
-- triangle under `F` to a distinguished triangle in `D'`, then use the exactness of filtered
-- colimits on Hom groups together with the five lemma to show the third vertex computes the
-- remaining pointwise right-derived value.
/-- The pointwise right-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (rightDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle once, apply the previous clause to the rotated
-- triangle, and use Lemma `13.14.5` to move pointwise right-derived definedness from `X⟦1⟧`
-- back to `X`.
/-- The pointwise right-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (rightDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle twice and apply the main two-out-of-three
-- clause together with Lemma `13.14.5`.
/-- The pointwise right-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (rightDerivedDefinedObjectProperty F S) := by
  sorry

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
        distTriang D' := sorry

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

-- Proof sketch: this is the dual two-out-of-three argument for pointwise left derived functors,
-- replacing filtered colimits by filtered limits and using the exactness criterion on Hom groups
-- against the completed distinguished triangle in `D'`.
/-- The pointwise left-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (leftDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle once, apply the preceding left-derived clause
-- to the rotated triangle, and use Lemma `13.14.5` to move pointwise left-derived definedness
-- from `X⟦1⟧` back to `X`.
/-- The pointwise left-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (leftDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle twice and apply the main left-derived
-- two-out-of-three clause together with Lemma `13.14.5`.
/-- The pointwise left-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (leftDerivedDefinedObjectProperty F S) := by
  sorry

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
        distTriang D' := sorry

end LeftDistinguished

end CategoryTheory
