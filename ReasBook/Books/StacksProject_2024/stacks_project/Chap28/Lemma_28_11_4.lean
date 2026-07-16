import Mathlib.AlgebraicGeometry.Stalk
import StacksProject_2024.stacks_project.Chap05.Definition_5_11_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- - the scheme-side owner is `CatenarySpace S`;
-- - the ring-side owner is `IsCatenaryRing`, applied here to the canonical stalk local rings
--   `S.presheaf.stalk x`;
-- - the public surface follows the project's standard stalkwise shape `∀ x : S, P (S.presheaf.stalk x)`.

variable (S : Scheme.{u})

/-- Lemma 28.11.4: a scheme is catenary if and only if each stalk local ring `\mathcal{O}_{S, x}`
is a catenary ring. -/
@[stacks 02J0, simp]
theorem catenarySpace_iff_forall_isCatenaryRing_stalk :
    CatenarySpace S ↔ ∀ x : S, IsCatenaryRing (S.presheaf.stalk x) := by
  sorry

namespace CatenarySpace

/-- If a scheme `S` is catenary, then each stalk local ring `\mathcal{O}_{S, x}` is catenary. -/
theorem isCatenaryRing_stalk {S : Scheme.{u}} (hS : CatenarySpace S) (x : S) :
    IsCatenaryRing (S.presheaf.stalk x) :=
  (catenarySpace_iff_forall_isCatenaryRing_stalk S).1 hS x

end CatenarySpace

/-- If every stalk local ring `\mathcal{O}_{S, x}` is catenary, then the scheme `S` is catenary.
-/
theorem catenarySpace_of_forall_isCatenaryRing_stalk
    (hS : ∀ x : S, IsCatenaryRing (S.presheaf.stalk x)) :
    CatenarySpace S :=
  (catenarySpace_iff_forall_isCatenaryRing_stalk S).2 hS

end AlgebraicGeometry.Scheme
