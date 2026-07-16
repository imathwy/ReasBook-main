import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_21_9
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme-side owner `LocallyOfFinitePresentation`;
- `Lemma_29_35_9` packages `GUnramified f` as `Unramified f` together with local finite
  presentation;
- `Lemma_29_21_9` upgrades `LocallyOfFiniteType f` to `LocallyOfFinitePresentation f` when the
  base scheme is locally Noetherian.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.35.6: let `f : X ⟶ S` be a morphism of schemes. Assume `S` is locally Noetherian.
Then `f` is unramified if and only if `f` is G-unramified. -/
@[stacks 04EV]
theorem unramified_iff_gUnramified [IsLocallyNoetherian S] :
    Unramified f ↔ GUnramified f := sorry

end AlgebraicGeometry
