import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_13
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_31_4_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_4

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 31.4.4 points out three application classes for the Chapter 31.4 value
  formulas: partially affine orthant models, partially quadratic orthant models, and Tucker
  representable pairing-orthogonal subspace pairs.
- `core/canonical`: the owner theorems are already
  `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and
  `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification`, together with the
  source-facing owners `ConvexCone.positive`, `Function.toWithBotTopOn`,
  `Function.IsPartiallyQuadratic`, and
  `AffineSubspace.IsTuckerRepresentable` for the model classes mentioned in the remark.
- `bridge/view`: this remark contributes no new mathematical data beyond those existing owners, so
  the canonical refinement is to recall them directly instead of keeping three parallel local
  wrapper theorems with redundant hypotheses.

Primary mathematical domain:
- finite-dimensional Fenchel duality applications on the nonnegative orthant and on
  pairing-orthogonal subspace pairs.

Domain-style sampling used here:
- `ConvexCone.positive` from `Chap01.Definition_2_5_11`;
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `AffineSubspace.IsTuckerRepresentable` from `Chap01.Text_1_13`;
- `Function.IsPartiallyQuadratic` from `Chap03.Text_12_3_3`;
- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and
  `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification` from
  `Chap06.Theorem_31_4` and `Chap06.Corollary_31_4_2`.

Primitive data vs derived API:
- primitive source-facing model owners: `Function.toWithBotTopOn`, `Function.IsPartiallyQuadratic`,
  `AffineSubspace.IsTuckerRepresentable`, and the canonical orthant owner `ConvexCone.positive`;
- derived API: the orthant and subspace value identities already owned by the Chapter 31.4 cone
  theorem and its subspace specialization.

Layer target: `bridge/view`. The remark is an application note pointing back to existing owner
theorems, not a source-facing owner of new theorem statements.
-/

/- Remark 31.4.4(1): the partially affine model mentioned in the remark is already expressed by
the canonical support-cut owner `Function.toWithBotTopOn`, while the orthant value formula sits on
the core cone-duality owner theorem specialized to the canonical orthant `ConvexCone.positive`. -/
recall Function.toWithBotTopOn
recall ConvexCone.positive
recall iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification

/- Remark 31.4.4(2): the partially quadratic model is already owned by
`Function.IsPartiallyQuadratic`, while the value identity is the same orthant specialization of the
core cone-duality theorem recalled above. -/
recall Function.IsPartiallyQuadratic
#check iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification

/- Remark 31.4.4(3): the Tucker-representable subspace hypothesis is already owned by
`AffineSubspace.IsTuckerRepresentable`, and the corresponding subspace value formula is the
existing Chapter 31.4 subspace corollary. -/
recall AffineSubspace.IsTuckerRepresentable
recall iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification
