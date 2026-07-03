import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.2.2: in the chapter's commutative-ring setting, the Stacks notion of an integral
domain is expressed by the canonical mathlib owner `IsDomain`; on a ring this is equivalent to
being nontrivial and having no zero divisors. -/
recall IsDomain

/- Definition 9.2.2 companion: on a ring, the source wording "nonzero and with `0` as the only
zerodivisor" is exactly the canonical theorem `isDomain_iff_noZeroDivisors_and_nontrivial`. -/
recall isDomain_iff_noZeroDivisors_and_nontrivial
