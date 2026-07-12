import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Real

section

variable {n : ℕ}
variable [NeZero n]

/- Source/core/bridge triage:
- `source-facing`: Serre's explicit exponential formula for the cyclic character indexed by `h`;
- `core/canonical`: the upstream Pontryagin-duality owner `AddChar.zmodAddEquiv`, built from
  `AddChar.zmod` and `ZMod.toCircle`;
- `bridge/view`: `AddChar.zmodAddEquiv_apply_eq_exp`, which specializes the owner to the textbook
  formula.

This file therefore keeps no primitive data of its own: it recalls the canonical owner and exposes
only the source-facing evaluation formula. -/

/- Definition 5-5.1-1: the finite Pontryagin duality equivalence identifying `ZMod n` with its
complex character group is `AddChar.zmodAddEquiv`. -/
recall AddChar.zmodAddEquiv

namespace AddChar

/-- Definition 5-5.1-1: the canonical cyclic character indexed by `h` evaluates to the textbook
exponential `e^{2π i hk / n}` on the class `k`. -/
theorem zmodAddEquiv_apply_eq_exp (h k : ZMod n) :
    zmodAddEquiv h k =
      Complex.exp (2 * π * Complex.I * ↑((h * k).val) / ↑n) := by
  simpa using (ZMod.toCircle_apply (h * k : ZMod n))

end AddChar

end
