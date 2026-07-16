import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the generic base-change stability API
-- `CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange` together with the
-- owner-prefixed pullback theorem `P.universally.pullback_snd`. Since `UniversalHomeomorphism` is
-- the local source-facing owner from `Definition_29_45_1`, this item is stated directly for the
-- canonical base-change morphism `pullback.snd`.

universe u

section

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)

/-- Lemma 29.45.2: the base change of a universal homeomorphism of schemes by any morphism of
schemes is a universal homeomorphism. -/
theorem universalHomeomorphism_pullback_snd [UniversalHomeomorphism f] :
    UniversalHomeomorphism (pullback.snd f g) := by
  rw [universalHomeomorphism_iff]
  exact topologicallyIsHomeomorph.universally.pullback_snd f g
    UniversalHomeomorphism.universally_isHomeomorph

/-- Any base change of a universal homeomorphism is a universal homeomorphism. -/
instance instUniversalHomeomorphismPullbackSndOfUniversalHomeomorphism
    [UniversalHomeomorphism f] :
    UniversalHomeomorphism (pullback.snd f g) :=
  universalHomeomorphism_pullback_snd f g

end

end AlgebraicGeometry
