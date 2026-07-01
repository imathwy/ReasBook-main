import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: ring characteristic computations for standard fields via the canonical
  `ringChar` owner;
* sampled owner declarations:
  `ringChar`,
  `ringChar.eq_zero`,
  `ZMod.ringChar_zmod_n`,
  `Rat.instCharZero`;
* best owner abstraction: `ringChar`, with concrete characteristic computations derived from that
  owner;
* primitive data: a semiring or field together with the characteristic structure (`CharP` or
  `CharZero`);
* derived API: concrete formulas such as `ringChar (ZMod n) = n` and the specialization
  `ringChar ℚ = 0`.

Source/core/bridge triage:
* `source-facing`: the two textbook characteristic computations for `𝔽_p` and `ℚ`;
* `core/canonical`: `ringChar`;
* `bridge/view`: `ZMod.ringChar_zmod_n` and `ringChar.eq_zero` as the canonical owner-level
  computations, with `Rat.instCharZero` serving only as supporting instance data. -/

/- Example 9.5.2: for a prime `p`, the field `𝔽_p`, modeled in Lean by `ZMod p`, has
characteristic `p`. This is the prime-field specialization of the canonical characteristic
computation `ZMod.ringChar_zmod_n`, whose statement already covers every `ZMod n`. -/
recall ZMod.ringChar_zmod_n

/- Example 9.5.2: the rational numbers `ℚ` have characteristic `0`. The canonical owner-level
statement is the specialization of `ringChar.eq_zero` to `ℚ`, using the standard instance
`Rat.instCharZero`. -/
#check (ringChar.eq_zero : ringChar ℚ = 0)
