import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (E : Type u) (F : Type v) [Field E] [Field F] [Algebra E F]

namespace FieldExtensionDegree
end FieldExtensionDegree

/- Source/core/bridge triage for Definition 9.7.1:
- `source-facing`: the textbook degree notation `[F : E]`
- `core/canonical`: `Module.rank E F`
- `bridge/view`: `FiniteDimensional E F` and `Module.finrank E F` for the finite-degree case

Primitive data are only the field extension and its canonical `E`-module structure on `F`. The
finite-dimensionality predicate and natural-number degree are derived API, so the owner file should
expose the notation on `Module.rank` and then derive the finite view from it.
-/

/- Definition 9.7.1: for a field extension `F/E`, the chapter's degree notation `[F : E]` is the
canonical owner `Module.rank E F`. -/
scoped[FieldExtensionDegree] notation:max "[" F " : " E "]" => Module.rank E F

open scoped FieldExtensionDegree

/- Source-facing check: the textbook degree notation `[F : E]` denotes the cardinal dimension of
`F` as an `E`-vector space. -/
#check ([F : E] : Cardinal)

/-
Definition 9.7.1 (Tag 09G3): for a field extension `F/E`, the degree `[F : E]` is the dimension
of `F` as an `E`-vector space. In Lean this source-facing notion is the canonical owner
`Module.rank E F`.
-/
recall Module.rank

/- Definition 9.7.1 also uses the canonical `FiniteDimensional E F` typeclass for the notion that
the field extension `F/E` is finite. -/
recall FiniteDimensional

/- Companion recall: `Module.finrank E F` is the canonical natural-number view of the same degree;
by definition it is `Cardinal.toNat (Module.rank E F)`, so `Cardinal.toNat [F : E]` already
reduces to `Module.finrank E F`. -/
recall Module.finrank
