import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_3_1 (from Chap06) -/
universe u v

open CategoryTheory

namespace TopCat

scoped notation "PSh(" X ")" => TopCat.Presheaf (Type _) X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.3.1:
- primary domain: set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Presheaf.sheafify`,
  `TopCat.Sheaf.forget`;
- best owner abstraction: the canonical presheaf owner `X.Presheaf (Type v)`, with source-facing
  Stacks notation `PSh(X)`;
- primitive data: only the functor `(TopologicalSpace.Opens X)ᵒᵖ ⥤ Type v`;
- derived API: morphisms as natural transformations, hence compatibility with restriction maps by
  naturality.

Source/core/bridge triage:
- `source-facing`: the Stacks category `PSh(X)` of set-valued presheaves on `X`;
- `core/canonical`: `TopCat.Presheaf`;
- `bridge/view`: the naturality identities for morphisms of presheaves.

This item adds no extra source-facing mathematics beyond the canonical owner, so the main entry
should be a direct recall of `TopCat.Presheaf` together with the chapter notation `PSh(X)`,
rather than a duplicate local wrapper. -/

/- Definition 6.3.1 (1) and (3): the category of presheaves of sets on a topological space `X`,
denoted `PSh(X)` in the Stacks Project, is the canonical owner `X.Presheaf (Type v)`. -/
recall TopCat.Presheaf
#check (PSh(X))
#check (X.Presheaf (Type v))

section

variable {X}
variable {F G : PSh(X)} (φ : F ⟶ G)

/- Morphisms of presheaves are natural transformations, so compatibility with restriction maps is
the canonical naturality identity `φ.naturality`. -/
#check φ.naturality

end

/-! ### Definition_6_3_2 (from Chap06) -/
open CategoryTheory TopologicalSpace TopCat

universe u v

namespace TopCat

set_option quotPrecheck false in
scoped notation:max A " ₚ " X =>
  (Functor.const (Opens X)ᵒᵖ).obj A

end TopCat

open scoped TopCat

variable (X : TopCat.{u}) (A : Type v)

/- Domain-style sampling for Definition 6.3.2:
- primary domain: set-valued presheaves on a topological space, viewed as a functor category;
- sampled owner API:
  `TopCat.Presheaf`,
  `Functor.const`,
  `CategoryTheory.Functor.obj`,
  `TopCat.Presheaf.Γgerm`;
- best owner abstraction: the constant-functor owner
  `Functor.const (Opens X)ᵒᵖ : Type v ⥤ X.Presheaf (Type v)`;
- source/core/bridge triage:
  `source-facing`: the Stacks constant-presheaf notation `A ₚ X`;
  `core/canonical`: the generic constant-functor owner in the functor category;
  `bridge/view`: the notation `A ₚ X` realizing the specialization of that owner at `A`.

Primitive data are the index category `(Opens X)ᵒᵖ` and the value `A`. The object-level constant
presheaf is derived from the owner abstraction by `.obj A`; the only extra surface needed in this
owner file is the chapter-facing notation `A ₚ X`, not a parallel wrapper definition.
-/
/- Definition 6.3.2: the constant presheaf construction on `X` is the canonical constant-functor
owner, exposed on the chapter surface by the notation `A ₚ X`. -/
recall Functor.const
#check (Functor.const (Opens X)ᵒᵖ : Type v ⥤ X.Presheaf (Type v))

/- Definition 6.3.2 source-facing object: `A ₚ X` is the constant presheaf on `X` with value
`A`. -/
#check (A ₚ X : X.Presheaf (Type v))
