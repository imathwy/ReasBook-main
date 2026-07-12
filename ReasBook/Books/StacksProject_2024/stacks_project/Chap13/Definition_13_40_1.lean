import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Definition 13.40.1:
- primary domain: orthogonals of object properties in categories with zero morphisms;
- sampled core/canonical declarations:
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.rightOrthogonal_iff`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.leftOrthogonal_iff`;
- best owner abstraction: the owner object properties `A.rightOrthogonal` and `A.leftOrthogonal`;
- primitive data: only the object property `A : ObjectProperty D`;
- derived API: the full-subcategory realizations `A.rightOrthogonal.FullSubcategory` and
  `A.leftOrthogonal.FullSubcategory`, together with the pointwise membership lemmas
  `A.rightOrthogonal_iff` and `A.leftOrthogonal_iff`;
- source/core/bridge triage:
  `source-facing`: the right and left orthogonal subcategories attached to `A`;
  `core/canonical`: `ObjectProperty.rightOrthogonal` and `ObjectProperty.leftOrthogonal`;
  `bridge/view`: the corresponding full subcategories and pointwise characterization lemmas;
- source-facing notation: `A^⊥` for the right orthogonal and `^⊥A` for the left orthogonal.

No parallel local wrapper is needed: the source notion is already owned canonically by the
mathlib orthogonal API on `ObjectProperty`. -/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroMorphisms D]

/- Source-facing notation for Definition 13.40.1: `A^⊥` and `^⊥A` are the right and left
orthogonals of the object property `A`, while the owner declarations remain
`A.rightOrthogonal` and `A.leftOrthogonal`. -/
postfix:max "^⊥" => rightOrthogonal
prefix:max "^⊥" => leftOrthogonal

/- Definition 13.40.1 (1): for a full subcategory of `D` encoded by an object property `A`, its
right orthogonal `A^⊥` is the canonical owner object property `A.rightOrthogonal`; the
corresponding full subcategory is recalled below. -/
recall rightOrthogonal

/- Definition 13.40.1 (2): for the same full subcategory `A`, its left orthogonal `^⊥A` is the
canonical owner object property `A.leftOrthogonal`; the corresponding full subcategory is recalled
below. -/
recall leftOrthogonal

section

variable (A : ObjectProperty D)

/- Companion recall: the right orthogonal subcategory is the canonical full subcategory
`(A^⊥).FullSubcategory`. -/
#check (A^⊥).FullSubcategory

/- Companion recall: membership in the right orthogonal means that every morphism from an object
satisfying `A` is zero. -/
#check A.rightOrthogonal_iff

/- Companion recall: the left orthogonal subcategory is the canonical full subcategory
`(^⊥A).FullSubcategory`. -/
#check (^⊥A).FullSubcategory

/- Companion recall: membership in the left orthogonal means that every morphism to an object
satisfying `A` is zero. -/
#check A.leftOrthogonal_iff

end

end CategoryTheory.ObjectProperty
