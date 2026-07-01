import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.123.6 lies in the commutative-algebra/Zariski-main-theorem domain governing conductor
ideals of polynomial algebras. Sampled owner declarations in this domain are
`exists_leadingCoeff_pow_smul_mem_conductor`,
`exists_leadingCoeff_pow_smul_mem_radical_conductor`, and
`isStronglyTranscendental_mk_radical_conductor` from
`Mathlib.RingTheory.ZariskisMainTheorem`.

Layer triage: this item is `core/canonical`, not `bridge/view`. The source statement is already the
canonical coefficientwise radical-conductor theorem for a finite polynomial map with integrally
closed constant image, so no local wrapper or paraphrase theorem should be introduced here.

Primitive data are the polynomial algebra map `φ`, the multiplier `t`, the polynomial `p`, and the
integrally-closed/finite hypotheses; the coefficientwise radical-conductor conclusion is derived
API. -/
recall exists_leadingCoeff_pow_smul_mem_radical_conductor
