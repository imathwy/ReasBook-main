import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic owner check:
mathlib already owns the canonical base-change stability theorem for scheme closed immersions,
so this Chapter 29 item is a pure source-facing recall of that owner. -/

/- Lemma 29.2.4: the base change of a closed immersion is a closed immersion. -/
@[stacks 01KV]
recall AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [IsClosedImmersion f] :
    IsClosedImmersion (pullback.snd f g)

end AlgebraicGeometry
