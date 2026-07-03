import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) (X : C)

/- Domain-style sampling for Definition 14.20.1:
- primary domain: augmented simplicial objects and augmentations in
  `CategoryTheory.SimplicialObject`;
- sampled owner API:
  `SimplicialObject.const`,
  `SimplicialObject.Augmented`,
  `SimplicialObject.Augmented.const`,
  `SimplicialObject.augment`;
- target layer: `source-facing`;
- best owner abstraction in the surrounding API: `SimplicialObject.Augmented C`, the canonical
  packaged owner of an augmented simplicial object;
- source/core/bridge triage:
  `source-facing`: for fixed `U` and `X`, an augmentation is a morphism
    `U ⟶ (const C).obj X`;
  `core/canonical`: `SimplicialObject.Augmented C`;
  `bridge/view`: an element of `SimplicialObject.Augmented C` with left side `U` and right side
    `X` recovers the textbook fixed-endpoint datum above, while `SimplicialObject.augment` is the
    downstream constructor from degree-`0` data.

Primitive data for the fixed-endpoint notion are exactly the natural-transformation components of
the morphism `U ⟶ (const C).obj X`. The packaged owner
`SimplicialObject.Augmented C` is the canonical way to store `U`, `X`, and the augmentation
together, but Definition 14.20.1 itself fixes `U` and `X`, so the main entry here should stay on
the source-facing fixed-endpoint morphism type and mention the packaged owner only as companion
bridge context.
-/

/- Definition 14.20.1: an augmentation of a simplicial object
`U` toward an object `X` of `C` is a morphism from `U` to the constant simplicial object on `X`.
-/
#check (U ⟶ (const C).obj X)

/- Companion owner context: the canonical packaged owner for augmented simplicial objects in `C`
is `SimplicialObject.Augmented C`. -/
#check (SimplicialObject.Augmented C)

/- Companion recall: the owner declaration for augmented simplicial objects is
`SimplicialObject.Augmented`. -/
recall SimplicialObject.Augmented

end
