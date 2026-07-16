import StacksProject_2024.stacks_project.Chap34.Definition_34_8_4
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}}

/-- Lemma 34.8.6: if `f : Y ⟶ X` is a surjective proper morphism of schemes, then the singleton
family `{f : Y ⟶ X}` is a ph covering. -/
@[stacks 0DES]
theorem phCovering_singleton_of_surjective_proper
    (f : Y ⟶ X) (hf : IsProper f) (hsurj : Surjective f) :
    PhCovering (fun _ : PUnit ↦ Y) (fun _ ↦ f) := sorry

end

end AlgebraicGeometry
