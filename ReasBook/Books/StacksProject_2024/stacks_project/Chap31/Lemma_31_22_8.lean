import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism smoothness owner
-- `AlgebraicGeometry.IsSmooth`; local Chapter 29 precedent uses the source-facing notation
-- `Smooth f`, and Chapter 31 fixes regular immersions as `IsRegularImmersion`.

/-- Lemma 31.22.8: if `f : X ⟶ S` is a smooth morphism of schemes and
`σ : S ⟶ X` is a section of `f`, then `σ` is a regular immersion. -/
@[stacks 067R]
theorem section_isRegularImmersion_of_smooth {X S : Scheme.{u}} {f : X ⟶ S}
    {σ : S ⟶ X} (hf : Smooth f) (hσ : σ ≫ f = 𝟙 S) :
    IsRegularImmersion σ := sorry

end AlgebraicGeometry
