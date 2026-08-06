import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits

universe u v

-- Semantic recall: `pushout`, `pushout.inl`, `pushout.inr`, and `pushout.isColimit` are the
-- canonical mathlib API for gluing a span `B ← A → X`.
/-
Definition 6.1.7: for a cofibration `i : A ⟶ X` and a map `g : A ⟶ B`, the pushout denoted
`B ∪_g X` is modeled by the object `pushout g i`, obtained by gluing `X` to `B` along `A`.
-/
recall pushout {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : C

/- The glued space carries the canonical map from `B`. -/
recall pushout.inl {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g

/- The glued space carries the canonical map from `X`. -/
recall pushout.inr {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g

/- These canonical maps identify the two copies of `A` along the span `B ← A → X`. -/
recall pushout.condition {C : Type u} [Category.{v, u} C] {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
  f ≫ pushout.inl f g = g ≫ pushout.inr f g

/- Equivalently, the canonical cocone on `pushout g i` is a colimit cocone. -/
recall pushout.isColimit {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : IsColimit (pushout.cocone f g)
