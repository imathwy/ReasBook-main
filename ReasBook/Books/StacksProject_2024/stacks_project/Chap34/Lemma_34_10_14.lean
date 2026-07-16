import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_24_1
import StacksProject_2024.stacks_project.Chap34.Definition_34_10_7

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the coproduct-family API around
-- `CategoryTheory.Limits.Sigma.desc`, while the local Stacks owners for this item are
-- `IsVCovering` and `UniversallySubmersive`. The source-facing statement is therefore the direct
-- bridge from a `V` covering family to universal submersiveness of its coproduct morphism.

section

variable {ι : Type u} {X : Scheme.{u}} (Xi : ι → Scheme.{u}) (f : ∀ i, Xi i ⟶ X)

/-- Lemma 34.10.14: if `Xi ⟶ X` is a `V` covering family, then the coproduct morphism
`∐ Xi ⟶ X` is universally submersive. -/
@[stacks 0ETP]
theorem universallySubmersive_sigmaDesc_of_isVCovering
    (h : IsVCovering X Xi f) :
    UniversallySubmersive (Limits.Sigma.desc f) := sorry

end

end AlgebraicGeometry
