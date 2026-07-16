import Mathlib
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Definition 8.11.1:
- primary domain: stacks in groupoids over a site and their fiberwise local geometry;
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `StackInGroupoidsOver`,
  `Functor.Fiber`,
  `canonicalPullbackChoice`;
- best owner abstraction: the source-facing property `IsGerbe J p` on a projection functor
  `p : S ⥤ C` already known to be a stack in groupoids over `(C, J)`;
- primitive data: the parent owner `IsStackInGroupoids J p`, local inhabitedness of fibers, and
  local isomorphism of any two objects in a fixed fiber after pullback along a cover;
- derived API: later reformulations in terms of gerbes over morphisms, local essential
  surjectivity, and local lifting of fiber morphisms.

Source/core/bridge triage:
- `source-facing`: `IsGerbe J p`;
- `core/canonical`: `IsStackInGroupoids J p`, `Functor.Fiber`, and the canonical pullback choice
  on `p`;
- `bridge/view`: later characterizations such as `IsGerbeOver` and the equivalence with local
  lifting conditions. -/

/-- Definition 8.11.1: a gerbe over the site `(C, J)` is a stack in groupoids whose fibers are
locally inhabited and such that any two objects of the same fiber become isomorphic after passing
to a covering. The site `J` is a genuine owner parameter of this notion and remains explicit in
the public API. -/
class IsGerbe (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackInGroupoids J p where
  /-- Every object of the base admits a covering by objects over which the gerbe has a section. -/
  locally_inhabited (U : C) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      Nonempty (p.Fiber I.Y)
  /-- Any two objects of the same fiber become isomorphic after restricting to a covering. -/
  locally_isomorphic {U : C} (x y : p.Fiber U) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      Nonempty
        (I.f ^*[canonicalPullbackChoice p] x ≅
          I.f ^*[canonicalPullbackChoice p] y)

/-- A gerbe over the site `(C, J)` is canonically a stack in groupoids over `(C, J)`. -/
instance (J : GrothendieckTopology C) [h : IsGerbe J p] : IsStackInGroupoids J p :=
  h.toIsStackInGroupoids

end

end CategoryTheory
