import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for `16_2_3_1`:
- primary domain: Jacobian determinants and elementary standard elements attached to a finite
  presentation in `Algebra.Presentation`;
- sampled owner API:
  `Algebra.Presentation.leadingJacobianDet`,
  `Algebra.Presentation.IsElementaryStandardElement`,
  `Algebra.IsElementaryStandard`;
- best owner abstraction: the presentation-level owner
  `Algebra.Presentation.IsElementaryStandardElement`;
- primitive data: the finite presentation `P` and its canonical determinant
  `P.leadingJacobianDet hcₙ hcₘ`;
- derived API: the displayed equality
  `a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ)` appears as one conjunct in the
  witness data for `P.IsElementaryStandardElement a`.

Source/core/bridge triage:
- `source-facing`: the first displayed Jacobian-determinant equation in Definition 16.2.3;
- `core/canonical`: the determinant owner `leadingJacobianDet` together with the owner predicate
  `IsElementaryStandardElement`;
- `bridge/view`: this file only recalls that the source clause uses the same canonical
  Jacobian-determinant expression already built into the owner API.
-/

/- 16.2.3.1: the first displayed clause of the elementary standard condition uses the chapter's
canonical leading Jacobian determinant attached to a finite presentation. -/
recall Algebra.Presentation.leadingJacobianDet

/- Companion recall: the owner predicate `Algebra.Presentation.IsElementaryStandardElement`
packages the displayed Jacobian equation as part of its witness data. -/
recall Algebra.Presentation.IsElementaryStandardElement
