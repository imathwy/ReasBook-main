import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.«15_11_6_4»

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 15.11.6.2:
- primary domain: commutative algebra of étale `A`-algebras, quotient sections modulo an ideal,
  and product decompositions controlled by integral-algebra idempotent lifting;
- sampled owner declarations:
  `exists_quotient_product_decomposition_of_etale_section`,
  `exists_integralClosure_quotient_product_of_etale_section`,
  `exists_integralClosure_product_decomposition_of_etale_quotient_section`;
- best owner abstraction: the canonical decomposition data is the `A`-algebra equivalence owned by
  `exists_integralClosure_product_decomposition_of_etale_quotient_section`;
- primitive data: an ideal `I : Ideal A`, the owner hypothesis
  `I.HasIntegralAlgebraIdempotentLifting`, and an étale quotient section
  `σ : A' →ₐ[A] A ⧸ I`;
- derived API: the lifted idempotent, its quotient factors, and the resulting product
  decomposition of `integralClosure A A'`.

Source/core/bridge triage:
- `source-facing`: the existence of the product decomposition in the étale quotient-section setup;
- `core/canonical`: the `AlgEquiv`-valued decomposition owner on `integralClosure A A'`;
- `bridge/view`: this numbered item adds no new owner beyond the chapter result in `15.11.6.4`,
  so it should stay a direct recall rather than a parallel `A'`-level wrapper theorem. -/

/- 15.11.6.2: in the étale quotient-section setup with integral-algebra idempotent lifting, the
canonical chapter owner is the product decomposition theorem for `integralClosure A A'`. This file
therefore stays a thin recall of
`exists_integralClosure_product_decomposition_of_etale_quotient_section` rather than introducing a
new decomposition theorem for `A'` itself. -/
recall exists_integralClosure_product_decomposition_of_etale_quotient_section
