import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.37.5: any localization of a normal domain is again normal. Since
`Definition 10.37.1` identifies normal domains with integrally closed domains, the owner
abstraction here is `IsIntegrallyClosed`; `IsLocalization M S` with `hM : M ≤ R⁰` is the
primitive localization data, and the normality/domain conclusions are derived canonically. -/
recall isIntegrallyClosed_of_isLocalization

/- Companion recall: under the same non-zero-divisor hypothesis, the localization is also a
domain via the canonical theorem `IsLocalization.isDomain_of_le_nonZeroDivisors`. -/
recall IsLocalization.isDomain_of_le_nonZeroDivisors
