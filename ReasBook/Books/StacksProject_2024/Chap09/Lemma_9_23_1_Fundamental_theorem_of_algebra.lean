import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
- primary domain: algebraically closed fields via complex polynomials;
- sampled owner declarations: `IsAlgClosed`, `IsAlgClosed.exists_root`, `Complex.exists_root`, and
  `Complex.isAlgClosed`;
- core/canonical owner abstraction: `IsAlgClosed ℂ`;
- layer: `core/canonical`, since the source statement is exactly the canonical complex-field
  instance;
- primitive data: the field `ℂ`;
- derived API: root-existence and splitting statements for complex polynomials, all obtained from
  `Complex.isAlgClosed`.
-/

/- Lemma 9.23.1 (Fundamental theorem of algebra). The field `ℂ` is algebraically closed.
This is the canonical mathlib fact `Complex.isAlgClosed : IsAlgClosed ℂ`. -/
recall Complex.isAlgClosed
