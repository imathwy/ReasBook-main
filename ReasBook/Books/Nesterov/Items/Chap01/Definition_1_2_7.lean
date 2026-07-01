import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_2_7

-- Declarations for this item will be appended below by the statement pipeline.

variable {r : ℕ → ℝ} {c : ℝ}

/- Definition 1.2.7 lies in the chapter's scalar superlinear-convergence domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical bridge
  theorems

Primary domain:
* quadratic recurrence bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `HasEventuallySuperlinearErrorBound` in `Nesterov/Chap01/Definition_1_2_7.lean`, the chapter
  owner abstraction for eventual superlinear scalar recurrences;
* `HasSuperlinearRateOfConvergence` in `Nesterov/Chap01/Definition_1_8_15.lean`, which reuses
  that owner for trajectory-level superlinear convergence;
* `HasConvergenceRateOfOrder` in `Nesterov/Chap01/Definition_1_6_9.lean`, a neighboring
  source-facing owner for eventual scalar comparison rates;
* `quadratic_tail_bound` in `Nesterov/Chap01/Proposition_1_7_6.lean`, a downstream owner-level
  consequence of the same quadratic recurrence.

Best owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the textbook quadratic recurrence `r (k + 1) ≤ c * (r k)^2`
* the converse packaging of that recurrence into the owner
* the one-step linear estimate once `c * r k ≤ 1 / 2`

Source/core/bridge triage:
* source-facing: the quadratic-rate existential statement from Definition 1.2.7
* core/canonical: the owner `HasEventuallySuperlinearErrorBound`
* bridge/view: the three recalled companion theorems below

This item intentionally keeps no parallel local definition of `HasEventuallySuperlinearErrorBound`
and no duplicate local proofs of its bridge lemmas. The numbered item is recalled directly through
the canonical chapter owner surface. -/

/- Definition 1.2.7: a quadratic rate of convergence is the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`. -/
#check (∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0)

namespace HasEventuallySuperlinearErrorBound

/- The textbook quadratic recurrence is recalled directly from the owner specialization. -/
recall quadratic_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (k : ℕ) :
    r (k + 1) ≤ c * (r k)^2

/- The explicit quadratic recurrence packages back into the canonical owner specialization. -/
recall of_quadratic_bound
    (h : ∀ k : ℕ, r (k + 1) ≤ c * (r k)^2) :
    HasEventuallySuperlinearErrorBound r 0 c 0

/- Once `c * r k ≤ 1 / 2`, the quadratic owner specialization yields the one-step linear bound. -/
recall linear_bound_of_mul_le_half
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    {k : ℕ}
    (hrk : 0 ≤ r k)
    (hthreshold : c * r k ≤ (1 / 2 : ℝ)) :
    r (k + 1) ≤ (1 / 2 : ℝ) * r k

end HasEventuallySuperlinearErrorBound
