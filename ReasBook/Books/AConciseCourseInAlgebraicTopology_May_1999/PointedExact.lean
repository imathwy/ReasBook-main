import Mathlib.CategoryTheory.Category.Pointed

/-- Exactness for pointed maps: `f` and `g` are exact when `g b` is the distinguished point
exactly for those `b` lying in the image of `f`. -/
def PointedExact {A B C : Pointed} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  ∀ b : B, g b = C.point ↔ ∃ a : A, f a = b
