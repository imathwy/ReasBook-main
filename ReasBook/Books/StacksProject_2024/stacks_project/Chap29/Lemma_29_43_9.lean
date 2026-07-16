import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / source-core-bridge check:
Chapter 29 already provides the source-facing owners `Projective`, `HProjective`, and
`LocallyProjective` in `Definition_29_43_1`. This file therefore states the Stacks clauses
directly on those source-facing owners for the canonical base-changed morphism `pullback.snd f g`,
rather than only recalling abstract morphism-property stability interfaces. -/

section

variable {X S S' : Scheme.{u}}

/-- Lemma 29.43.9 (1): a base change of a projective morphism is projective. -/
@[stacks 02V6]
theorem projective_pullback_snd (f : X ⟶ S) [Projective f] (g : S' ⟶ S) :
    Projective (pullback.snd f g) := sorry

/-- Lemma 29.43.9 (2): a base change of a locally projective morphism is locally projective. -/
@[stacks 02V6]
theorem locallyProjective_pullback_snd (f : X ⟶ S) [LocallyProjective f] (g : S' ⟶ S) :
    LocallyProjective (pullback.snd f g) := sorry

end

end AlgebraicGeometry
