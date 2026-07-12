import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.11: integral closure commutes with localization. For a ring map `A → B` and a
multiplicative subset `S ⊆ A`, localizing the integral closure `integralClosure A B` at `S`
produces the integral closure of `Aₛ` in `Bₛ`. This is exactly the canonical mathlib theorem
`IsLocalization.integralClosure`. -/
recall IsLocalization.integralClosure
