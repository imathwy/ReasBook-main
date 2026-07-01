import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex.HomComplex

/- Domain-style sampling for 15.72.6.1:
- primary domain: the Hom-complex differential for cochain complexes and its componentwise sign
  formula;
- sampled owner declarations:
  `CochainComplex.HomComplex.δ`,
  `CochainComplex.HomComplex.δ_v`,
  `CochainComplex.HomComplex.δ_zero_cochain_v`,
  `CochainComplex.HomComplex.Cocycle.mem_iff`;
- best owner abstraction: the canonical owner is the namespace
  `CochainComplex.HomComplex`, with `δ_v` as the primitive component formula and
  `δ_zero_cochain_v` as the degree-zero specialization actually used in the chapter;
- primitive data vs. derived API: the primitive object is the Hom-complex differential `δ`, while
  the component expansions are derived API already owned upstream and should be recalled directly
  rather than recopied in a chapter-local wrapper;
- source/core/bridge triage:
  `source-facing`: the sign pattern for `d(β^{p,s})` in the direct construction of
  Lemma `15.72.6`;
  `core/canonical`: `δ_v` and `δ_zero_cochain_v`;
  `bridge/view`: the degree-zero morphism criterion already lives in `Remark_15_72_2`; this file
  itself is pure canonical recall of the Hom-complex differential formulas.
-/

/- 15.72.6.1: the sign pattern for the component `d(β^{p,s})` in the direct construction of
Lemma `15.72.6` is governed by the standard Hom-complex differential component formula `δ_v`. -/
recall δ_v

/- Companion recall: when the cochain has degree `0`, the Hom-complex differential splits into the
`d_L` and `d_K` terms with the standard sign convention. -/
recall δ_zero_cochain_v
