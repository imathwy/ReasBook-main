import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace PerfectClosure

/- Textbook notation for the perfect closure `k^{perf}` of a field `k`. -/
scoped notation:max K "^{" "perf" "}" => perfectClosure K (AlgebraicClosure K)

end PerfectClosure

open scoped PerfectClosure

section

variable (k : Type u) [Field k]

/-
Definition 10.45.5: the perfect closure `k^{perf}` of `k` is the canonical intermediate field
`perfectClosure k (AlgebraicClosure k)` inside a chosen algebraic closure.
-/
#check k^{perf}

end

/- Companion recall: `perfectClosure k E` is the owner-level relative perfect closure attached to
any field extension `E/k`, and `k^{perf}` is its specialization to `E = AlgebraicClosure k`.
-/
recall perfectClosure
