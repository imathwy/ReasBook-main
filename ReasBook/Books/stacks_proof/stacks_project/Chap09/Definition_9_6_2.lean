import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Source/core/bridge triage for Definition 9.6.2:
- `source-facing`: a field extension `E/F`
- `core/canonical`: the `F`-algebra structure `Algebra F E`
- `bridge/view`: injectivity of the canonical map `algebraMap F E`

Primitive data are only the two fields and the `F`-algebra structure on `E`; injectivity of the
canonical map is derived API from the owner abstraction.
-/

section

variable {F : Type u} {E : Type v} [Field F] [Field E]

/- Definition 9.6.2: a field extension `E/F` is modeled in Lean by a field `E` equipped with the
canonical `F`-algebra structure, i.e. by the type expression `Algebra F E`. -/
#check (Algebra F E)

section

variable [Algebra F E]

/- Companion check: for such a field extension, the canonical map `F →+* E` is injective, so the
textbook phrasing that `F` is contained in `E` is recovered from the canonical `F`-algebra
structure. -/
recall FaithfulSMul.algebraMap_injective

end
end
