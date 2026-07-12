import Mathlib.Tactic.Recall
import StacksProject_2024.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for `16_2_3_1`:
- primary domain: presentation-level Jacobian determinants in Definition 16.2.3 for elementary
  standard elements;
- sampled owner API:
  `Algebra.Presentation.jacobianMatrix`,
  `Algebra.Presentation.leadingJacobianDet`,
  `Algebra.Presentation.IsElementaryStandardElement`,
  `Algebra.IsElementaryStandard`;
- best owner abstraction: the source-facing clause lives inside the presentation-level owner
  `Algebra.Presentation.IsElementaryStandardElement`; its Jacobian factor is the derived
  determinant `P.leadingJacobianDet hcₙ hcₘ` of the primitive matrix `P.jacobianMatrix hcₘ`;
- primitive data: a finite presentation `P : Algebra.Presentation R A (Fin n) (Fin m)`, an
  integer `c` with bounds `hcₙ : c ≤ n` and `hcₘ : c ≤ m`, and the canonical matrix
  `P.jacobianMatrix hcₘ`;
- derived API: the displayed source equation
  `a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ)` appears as one conjunct in the
  witness data for `P.IsElementaryStandardElement a`.

Source/core/bridge triage:
- `source-facing`: the first displayed Jacobian-determinant identity in Definition 16.2.3 (1);
- `core/canonical`: `Algebra.Presentation.IsElementaryStandardElement` together with its canonical
  Jacobian determinant owner `leadingJacobianDet`;
- `bridge/view`: this file only recalls that the textbook determinant clause is already the
  determinant built from `P.jacobianMatrix hcₘ` in the chapter owner API.
-/

/- 16.2.3.1: the first displayed clause of the elementary standard condition uses the chapter's
canonical leading Jacobian determinant attached to a finite presentation. -/
recall Algebra.Presentation.leadingJacobianDet

/- Companion recall: the determinant owner is derived from the primitive presentation-level
Jacobian matrix `P.jacobianMatrix hcₘ`. -/
recall Algebra.Presentation.jacobianMatrix

/- Companion recall: the owner predicate `Algebra.Presentation.IsElementaryStandardElement`
packages the displayed Jacobian equation as part of its witness data. -/
recall Algebra.Presentation.IsElementaryStandardElement
