import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling in the order-of-vanishing API:
- primitive ring-level data: `Ring.ord`
- multiplicative ring-level bridge: `Ring.ordMonoidWithZeroHom`
- fraction-field owner: `Ring.ordFrac`
- quotient-rule computation: `Ring.ordFrac_eq_div`

Layer triage:
- `source-facing`: the textbook additive notation `ord_R : Kˣ → ℤ`
- `core/canonical`: mathlib already owns the multiplicative fraction-field order of vanishing as
  `Ring.ordFrac`
- `bridge/view`: `Ring.ord` and `Ring.ordFrac_eq_div` give the ring-level and presentation-level
  views of that owner, while `WithZero.log` recovers the additive textbook form

Primitive-vs-derived split:
- primitive data lives in the ring-level length definition `Ring.ord`
- the fraction-field valuation `Ring.ordFrac` is the canonical owner used downstream
- the formula on a presentation `x / y` is derived API, exposed by `Ring.ordFrac_eq_div`
-/

/- Definition 10.121.2: the order of vanishing along a one-dimensional Noetherian local subring
`R` of a field `K` is the canonical fraction-field order-of-vanishing map `Ring.ordFrac`; after
applying `WithZero.log` on nonzero elements, this recovers the textbook additive function
`ord_R : Kˣ → ℤ`. -/
recall Ring.ordFrac

/- Companion recall: for an element `x : R`, the ring-level order of vanishing `Ring.ord R x` is
defined as the module length of `R / (x)`, matching the formula `length_R(R/(x))`. -/
recall Ring.ord

/- Companion recall: the quotient-rule formula for fractions is encoded by `Ring.ordFrac_eq_div`,
which computes the fraction-field order of vanishing on a presentation `x / y` with `x, y ≠ 0`. -/
recall Ring.ordFrac_eq_div
