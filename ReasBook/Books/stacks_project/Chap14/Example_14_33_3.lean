import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Functor
open SimplicialObject
open SimplicialObject.Augmented

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Example 14.33.3:
- primary domain: augmented simplicial objects and functorial whiskering in
  `CategoryTheory.SimplicialObject`;
- sampled owner API:
  `SimplicialObject.Augmented`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`;
- best owner abstraction: `SimplicialObject.Augmented`, transported by the single canonical owner
  `SimplicialObject.Augmented.whiskeringObj` along the composite functor
  `((whiskeringRight C C B).obj G) ⋙ ((whiskeringLeft A C B).obj F) :
    (C ⥤ C) ⥤ (A ⥤ B)`;
- primitive data: only the simplicial object `X` and the augmentation `ε`;
- derived API: the source-facing owner `prePostcomposeAugmented F G ε`; one-sided comparison maps
  are taken directly from the canonical `whiskeringObj.map` API.

Source/core/bridge triage:
- `source-facing`: the augmented simplicial object in `A ⥤ B` whose left side is `G ∘ X ∘ F` and
  whose augmentation point is `G ∘ F`;
- `core/canonical`: `SimplicialObject.Augmented.whiskeringObj`;
- `bridge/view`: the source-facing construction obtained by whiskering the given augmentation
  along the composite functor from endofunctors of `C` to functors `A ⥤ B`.
-/

/-- Example 14.33.3: if a simplicial object of endofunctors of `C` is augmented to the identity
functor of `C`, then composing on the left with `F : A ⥤ C` and on the right with `G : C ⥤ B`
produces an augmented simplicial object in the functor category `A ⥤ B`, whose underlying
simplicial object is `G ∘ X ∘ F` and whose augmentation points to `G ∘ F`. -/
abbrev prePostcomposeAugmented
    (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    SimplicialObject.Augmented (A ⥤ B) :=
  (whiskeringObj (C ⥤ C) (A ⥤ B)
      (((whiskeringRight C C B).obj G) ⋙ ((whiskeringLeft A C B).obj F))).obj
    { left := X
      right := 𝟭 C
      hom := ε }

end CategoryTheory
