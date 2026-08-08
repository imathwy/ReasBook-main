import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

/- Definition 2.5.2: a groupoid is the canonical structure `Groupoid C`, namely a category in
which every morphism is an isomorphism; a group is realized as the corresponding one-object
groupoid `SingleObj G`. -/
recall Groupoid (C : Type u) : Type (max u (v + 1))

variable (G : Type u) [Group G]

/- A group carries the canonical one-object groupoid structure on `SingleObj G`. -/
#check (inferInstance : Groupoid (SingleObj G))

/- The endomorphisms of the unique object of `SingleObj G` recover the original monoid, hence in
particular the original group. -/
recall SingleObj.toEnd (G : Type u) [Monoid G] : G ≃* End (SingleObj.star G)
