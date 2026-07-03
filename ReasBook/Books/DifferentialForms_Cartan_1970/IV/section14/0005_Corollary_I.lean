import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary I is a core/canonical recall item in one-variable complex analysis. The source-facing
content is exactly mathlib's product-vanishing theorem
`AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero` from
`Mathlib/Analysis/Analytic/IsolatedZeros.lean`: for analytic functions on a preconnected domain,
vanishing of the product forces one factor to vanish identically. The open-set wording in the
source is already absorbed by `AnalyticOnNhd`, so no local bridge theorem or extra openness
hypothesis is needed here. -/
recall AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero
