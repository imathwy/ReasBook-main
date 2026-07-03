import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (F : Type u) (Fbar : Type v) [Field F] [Field Fbar] [Algebra F Fbar]

/- Domain triage:
- primary domain: algebraic closures of fields;
- sampled owner declarations: `IsAlgClosure`, `isAlgClosure_iff`, `IsAlgClosure.isAlgClosed`, and
  the nearby chapter specializations `Lemma_9_10_5` and `Lemma_9_10_6`;
- core/canonical owner abstraction: `IsAlgClosure F Fbar`;
- layer: `core/canonical`, since Definition 9.10.3 is the owner notion itself;
- primitive data: the fields `F`, `Fbar`, and the `F`-algebra structure on `Fbar`;
- derived API: the source-form decomposition into algebraic-over-`F` and algebraically-closed is
  already the canonical theorem `isAlgClosure_iff`.
-/

/- Definition 9.10.3: an algebraic closure of a field `F` is a field extension `Fbar/F` that is
algebraic over `F` and algebraically closed; this is the canonical mathlib typeclass
`IsAlgClosure F Fbar`. -/
recall IsAlgClosure

/- Companion recall: the source-form specification of `IsAlgClosure F Fbar` is the existing
canonical theorem `isAlgClosure_iff`, expressing that `Fbar` is algebraically closed and
algebraic over `F`. -/
recall isAlgClosure_iff
