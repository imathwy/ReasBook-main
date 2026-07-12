import Mathlib.CategoryTheory.Sites.Limits

-- Declarations for this helper file.

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A site `(C, J)` has enough objects with property `P` if every object admits a covering whose
members all satisfy `P`. -/
def HasEnoughObjectsWithProperty (P : C → Prop) : Prop :=
  ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, P I.Y

end CategoryTheory.GrothendieckTopology
