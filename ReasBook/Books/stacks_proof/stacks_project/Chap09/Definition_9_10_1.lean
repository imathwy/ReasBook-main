import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage:
- primary domain: algebraically closed fields and algebraic field extensions;
- sampled owner declarations: `IsAlgClosed`,
  `IsAlgClosed.algebraMap_bijective_of_isIntegral`,
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`, and `isAlgClosure_iff`;
- core/canonical owner abstraction: `IsAlgClosed F`;
- layer: `core/canonical`, since Definition 9.10.1 is the owner notion itself;
- primitive data: only the field `F`;
- derived API: the triviality of algebraic extensions via the structure map and via intermediate
  fields.
-/

variable (F : Type u) [Field F]

/- Definition 9.10.1: a field `F` is algebraically closed. This is the canonical mathlib owner
notion `IsAlgClosed F`. -/
recall IsAlgClosed

section

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/- Companion recall: the source-facing statement that every algebraic field extension of an
algebraically closed field is trivial via a bijective structure map is already the canonical owner
theorem `IsAlgClosed.algebraMap_bijective_of_isIntegral`, specialized to field extensions. -/
recall IsAlgClosed.algebraMap_bijective_of_isIntegral

/- Companion recall: the equivalent intermediate-field formulation of the Stacks definition is the
existing theorem `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`. -/
recall IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic

end
